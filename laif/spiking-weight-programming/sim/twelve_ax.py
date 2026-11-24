"""12AX task of the spike-frequency-adaptation paper (eLife 2021, e65459) with a hand-written plain-LIF
circuit: 25 neurons, no adaptation, no self-connections, no training.

Task and network model are ported from the public reference code (12AX_task/symltl/dataset.py, sym-ltl.py and
lsnn/spiking_models.py of github.com/IGITUGraz/Spike-Frequency-Adaptation-Supports-Network-Computations, MIT
licence): episodes of 90 symbols from {1,2,A,B,C,X,Y,Z}, 500 ms per symbol, 5 Poisson input neurons per symbol
at 200 Hz when shown and 2 Hz otherwise; LIF with tau_m = 20 ms, threshold 0.03, 5 ms refractory, 1 ms delay;
readout = weights times the mean activity in each 500 ms window plus bias, argmax over (L, R).
An episode counts as solved when all 90 outputs are right.

Circuit (weights in units of the threshold):
  relays   r1 r2 rA rB rX rY   fire while their symbol is shown (the 2 Hz background does not reach threshold)
  context  C1 C2               latches: last digit was 1 / 2. A latch is a pair of neurons (C1, C1') that excite
                               each other and so keep firing until both are inhibited
  armed    PX PY               latches: PX = context 1 and last letter A, PY = context 2 and last letter B
  answer   RX RY               RX = rX AND PX, RY = rY AND PY; the R readout counts their spikes
  timer    D1..D5              started by rX or rY, clears PX and PY about 230 ms later, so that a second
                               X or Y in a row is not answered

usage: twelve_ax.py [N_EPISODES] [SEED]
"""
import json, sys
import numpy as np
import torch

SYMS = "12ABCXYZ"            # codes 0..7 as in the reference code
THR, TAU, N_REF, STEP, N_CODE, LENGTH = 0.03, 20.0, 5, 500, 5, 90
LATCHES = ["C1", "C2", "PX", "PY", "D1", "D2", "D3", "D4"]
NAMES = ["r1", "r2", "rA", "rB", "rX", "rY", "C1", "C2", "PX", "PY", "RX", "RY", "D1", "D2", "D3", "D4", "D5"] \
    + [n + "'" for n in LATCHES]
IDX = {n: i for i, n in enumerate(NAMES)}
P = dict(relay=4.0, self_exc=60.0, ignite=30.0, kill=-150.0, clear=-400.0, gate=4.5, slow=5.6)


def episode(rng):
    """Port of generate_string_12_ax_by: 23 strings of the regular expression
    [12][ABCXYZ]{1,10}((A[CZ]{0,6}X|B[CZ]{0,6}Y)|([ABC][XYZ])){1,2}, cut to 90 symbols."""
    s = []
    for _ in range(23):
        s.append(rng.integers(0, 2))
        s += list(rng.integers(2, 8, size=rng.integers(1, 11)))
        for _ in range(rng.integers(1, 3)):
            if rng.integers(0, 2) == 0:
                a = rng.integers(0, 2)                              # A...X or B...Y
                s += [2 + a] + list(rng.choice([4, 7], size=rng.integers(0, 7))) + [5 + a]
            else:
                s += [rng.integers(2, 5), rng.integers(5, 8)]
    return np.array(s[:LENGTH])


def targets(seq):
    """Port of generate_target_12_ax_by."""
    num, letter, out = -1, -1, np.zeros(len(seq), dtype=int)
    for i, c in enumerate(seq):
        if c in (0, 1):
            num, letter = c, -1
        elif c in (2, 3):
            letter = c
        elif c in (5, 6):
            out[i] = int((num, letter, c) in ((0, 2, 5), (1, 3, 6)))
            letter = c
    return out


def circuit(p=P):
    n = len(NAMES)
    W_in, W_rec = torch.zeros(n, 8 * N_CODE), torch.zeros(n, n)

    def w(post, pre, val):
        W_rec[IDX[post], IDX[pre]] = val
        if post in LATCHES and val < 0:                               # inhibition reaches both neurons of a latch
            W_rec[IDX[post + "'"], IDX[pre]] = val

    for name, sym in zip(NAMES[:6], (0, 1, 2, 3, 5, 6)):
        W_in[IDX[name], sym * N_CODE:(sym + 1) * N_CODE] = p["relay"]
    for latch in LATCHES:
        w(latch, latch + "'", p["self_exc"]); w(latch + "'", latch, p["self_exc"])
    w("C1", "r1", p["ignite"]); w("C1", "r2", p["kill"])
    w("C2", "r2", p["ignite"]); w("C2", "r1", p["kill"])
    w("PX", "rA", p["gate"]); w("PX", "C1", p["gate"])               # set: A in context 1
    w("PY", "rB", p["gate"]); w("PY", "C2", p["gate"])               # set: B in context 2
    for pre in ("r1", "r2", "rB"):
        w("PX", pre, p["kill"])
    for pre in ("r1", "r2", "rA"):
        w("PY", pre, p["kill"])
    w("PX", "D5", p["clear"]); w("PY", "D5", p["clear"])            # one timer spike switches a latch off
    w("RX", "rX", p["gate"]); w("RX", "PX", p["gate"])
    w("RY", "rY", p["gate"]); w("RY", "PY", p["gate"])
    w("D1", "rX", p["ignite"]); w("D1", "rY", p["ignite"])
    for a, b in (("D1", "D2"), ("D2", "D3"), ("D3", "D4"), ("D4", "D5")):
        w(b, a, p["slow"])
    for d in ("D1", "D2", "D3", "D4"):
        w(d, "D5", p["clear"])
    W_out = torch.zeros(n, 2)                                         # columns: L, R
    W_out[IDX["RX"], 1] = W_out[IDX["RY"], 1] = 1.0
    b_out = torch.tensor([4.0 / STEP, 0.0])                           # R wins from 5 answer spikes per window
    return W_in * THR, W_rec * THR, W_out, b_out


@torch.no_grad()
def run_episodes(seqs, seed, p=P, trace=False):
    """seqs: (B, 90) symbol codes. Returns outputs (B, 90), total spikes per neuron, and optional spike trace."""
    W_in, W_rec, W_out, b_out = circuit(p)
    B, n = seqs.shape[0], W_in.shape[0]
    assert not W_rec.diagonal().any(), "the reference network has no self-connections"
    gen = torch.Generator().manual_seed(seed)
    decay = float(np.exp(-1.0 / TAU))
    v = torch.zeros(B, n); z = torch.zeros(B, n); ref = torch.zeros(B, n)
    outs, total, tr = [], torch.zeros(n), []
    seqs_t = torch.from_numpy(seqs)
    for k in range(seqs.shape[1]):
        rate = torch.full((B, 8), 0.002)
        rate[torch.arange(B), seqs_t[:, k]] = 0.2
        x = (torch.rand(STEP, B, 8 * N_CODE, generator=gen) < rate.repeat_interleave(N_CODE, 1)).float()
        count = torch.zeros(B, n)
        for t in range(STEP):
            i_t = x[t] @ W_in.T + z @ W_rec.T
            new_z = ((v > THR) & (ref <= 0)).float()                  # spike read from the voltage before the update
            v = decay * v + (1 - decay) * i_t - z * THR
            ref = torch.where(new_z > 0, torch.full_like(ref, N_REF), ref - 1)
            z = new_z
            count += z
            if trace:
                tr.append(z.clone())
        outs.append(((count / STEP) @ W_out + b_out).argmax(1))
        total += count.sum(0)
    return torch.stack(outs, 1).numpy(), total, (torch.stack(tr) if trace else None)


def evaluate(n_episodes, seed, batch=250, p=P):
    rng = np.random.default_rng(seed)
    ok_ep = ok_sym = spikes = 0
    for k in range(0, n_episodes, batch):
        seqs = np.stack([episode(rng) for _ in range(min(batch, n_episodes - k))])
        tgt = np.stack([targets(s) for s in seqs])
        out, total, _ = run_episodes(seqs, seed * 1000 + k, p)
        ok_ep += (out == tgt).all(1).sum(); ok_sym += (out == tgt).sum(); spikes += total.sum().item()
    return dict(task="12AX", neurons=len(NAMES), episodes=n_episodes, seed=seed, success_rate=ok_ep / n_episodes,
                symbol_success_rate=ok_sym / (n_episodes * LENGTH), wrong_episodes=int(n_episodes - ok_ep),
                rate_hz_per_neuron=spikes / n_episodes / (LENGTH * STEP / 1000) / len(NAMES))


if __name__ == "__main__":
    torch.set_num_threads(1)
    # targets on a hand-checked string: 1 A X X  2 B C Y  A X  1 B X  A Z Y  A X
    s = np.array([SYMS.index(c) for c in "1AXX2BCYAX1BXAZYAX"])
    assert list(targets(s)) == [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    a = sys.argv[1:]
    print(json.dumps(evaluate(int(a[0]) if a else 2000, int(a[1]) if len(a) > 1 else 0), default=float))
