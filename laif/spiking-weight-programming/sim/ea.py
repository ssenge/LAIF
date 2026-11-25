"""Evidence accumulation task of the e-prop paper (Nature Communications 11:3625, 2020) with a hand-written
plain-LIF circuit, no adaptation, no self-connections, no training.

Task and neuron model are ported from the public reference code (github.com/IGITUGraz/eligibility_propagation,
Figure_3_and_S7_e_prop_tutorials: tools.py, models.py, tutorial_evidence_accumulation_with_alif.py; see
LICENSE-eprop-reference-code.txt): 7 cues of 100 ms, one every 150 ms, each on the left or on the right; after a
delay the side with more cues has to be reported during the last 150 ms of the 2250 ms trial. 40 input neurons in
4 groups of 10: left cue, right cue and recall signal at 40 Hz while active, background at 10 Hz throughout.
Neurons: v[t] = decay * v[t-1] + input[t] - thr * z[t-1], spike if v[t] > thr and not refractory (5 ms),
tau = 20 ms, thr = 0.6, no self-connections. Readout: weights times the 20 ms filtered spikes, averaged over the
last 150 ms, argmax of two outputs, no bias.

Circuit (weights in units of the threshold): the right side wins iff at least 4 of the 7 cues are on the right,
so the circuit counts right cues up to 4.
  R        relay of the right-cue group
  L1..L4   latches (pairs of neurons exciting each other): Lk is on once k right cues have been seen
  T, A     between L(k) and L(k+1): two slowly charging latches, about 65 ms each. A(k+1) switches on about
           130 ms after L(k), that is after the cue that switched L(k) on has ended. L(k+1) is a gate of
           A(k+1) and R, so every cue advances the count by exactly one.
  C        relay of the recall group;  O = C AND NOT L4
Readout: "right" reads L4, "left" reads O.

usage: ea.py [N_TRIALS] [SEED]
"""
import json, sys
import numpy as np
import torch

N_IN, THR, TAU, N_REF = 40, 0.6, 20.0, 5
N_CUES, T_CUE, T_INT, T_RECALL, SEQ = 7, 100, 150, 150, 150 * 7 + 1200
F0, P_GROUP = 0.04, 0.3
P = dict(relay=0.4, first=0.6, pair=1.5, slow=0.23, gate_a=0.18, gate_r=0.2, recall=0.4, veto=-3.0)
NAMES = ["R", "C", "O"] + [f"L{k}{s}" for k in range(1, 5) for s in ("a", "b")] \
    + [f"{n}{k}{s}" for k in range(2, 5) for n in ("T", "A") for s in ("a", "b")]
IDX = {n: i for i, n in enumerate(NAMES)}


def make_batch(batch, rng):
    """Port of generate_click_task_data. Returns spikes (T, B, 40) and targets (1 = more cues on the right)."""
    side = rng.integers(0, 2, size=batch)
    p_right = np.where(side == 1, 1 - P_GROUP, P_GROUP)
    cues = (rng.random((batch, N_CUES)) < p_right[:, None]).astype(int)        # 1 = right
    prob = np.zeros((batch, SEQ, N_IN), dtype=np.float32)
    for k in range(N_CUES):
        t0 = (T_INT - T_CUE) + k * T_INT
        for c in (0, 1):
            prob[cues[:, k] == c, t0:t0 + T_CUE, c * 10:(c + 1) * 10] = F0
    prob[:, -T_RECALL:, 20:30] = F0
    prob[:, :, 30:] = F0 / 4
    spikes = (rng.random(prob.shape, dtype=np.float32) < prob).astype(np.float32)
    return torch.from_numpy(spikes).permute(1, 0, 2).contiguous(), (cues.sum(1) > N_CUES // 2).astype(int)


def circuit(p=P):
    n = len(NAMES)
    W_in, W_rec, W_out = torch.zeros(n, N_IN), torch.zeros(n, n), torch.zeros(n, 2)

    def w(post, pre, val):
        W_rec[IDX[post], IDX[pre]] = val

    W_in[IDX["R"], 10:20] = p["relay"]
    W_in[IDX["C"], 20:30] = p["recall"]
    for name in NAMES[3:]:
        if name.endswith("a"):
            w(name, name[:-1] + "b", p["pair"]); w(name[:-1] + "b", name, p["pair"])
    w("L1a", "R", p["first"])
    for k in range(2, 5):
        w(f"T{k}a", f"L{k - 1}a", p["slow"])
        w(f"A{k}a", f"T{k}a", p["slow"])
        w(f"L{k}a", f"A{k}a", p["gate_a"]); w(f"L{k}a", "R", p["gate_r"])
    w("O", "C", p["first"]); w("O", "L4a", p["veto"]); w("O", "L4b", p["veto"])
    W_out[IDX["L4a"], 1] = 1.0; W_out[IDX["O"], 0] = 1.0
    return W_in * THR, W_rec * THR, W_out


@torch.no_grad()
def run(x, W_in, W_rec, trace=False):
    """Port of EligALIF.__call__ without adaptation. x: (T, B, 40). Returns filtered-spike readout input
    averaged over the last 150 ms (B, n), total spikes, optional trace (T, B, n)."""
    T, B, _ = x.shape
    n = W_in.shape[0]
    assert not W_rec.diagonal().any(), "the reference network has no self-connections"
    decay = float(np.exp(-1.0 / TAU))
    v = torch.zeros(B, n); z = torch.zeros(B, n); r = torch.zeros(B, n); f = torch.zeros(B, n)
    acc, total, tr = torch.zeros(B, n), 0.0, []
    for t in range(T):
        v = decay * v + x[t] @ W_in.T + z @ W_rec.T - z * THR
        z = ((v > THR) & (r <= 0)).float()
        r = torch.clamp(r + N_REF * z - 1, 0, N_REF)
        f = decay * f + (1 - decay) * z
        if t >= T - T_RECALL:
            acc += f
        total += z.sum().item()
        if trace:
            tr.append(z.clone())
    return acc / T_RECALL, total, (torch.stack(tr) if trace else None)


def evaluate(n_trials, seed, p=P, batch=500):
    rng = np.random.default_rng(seed)
    W_in, W_rec, W_out = circuit(p)
    ok, spikes = 0, 0.0
    for k in range(0, n_trials, batch):
        x, target = make_batch(min(batch, n_trials - k), rng)
        acc, total, _ = run(x, W_in, W_rec)
        ok += int(((acc @ W_out).argmax(1).numpy() == target).sum()); spikes += total
    return dict(task="evidence accumulation", neurons=len(NAMES), trials=n_trials, seed=seed, accuracy=ok / n_trials,
                wrong=n_trials - ok, rate_hz_per_neuron=spikes / n_trials / (SEQ / 1000) / len(NAMES))


if __name__ == "__main__":
    torch.set_num_threads(1)
    a = sys.argv[1:]
    print(json.dumps(evaluate(int(a[0]) if a else 500, int(a[1]) if len(a) > 1 else 0)), flush=True)
