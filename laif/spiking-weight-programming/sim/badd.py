"""Binary adding task of the segregated temporal probe (arXiv:2502.09449, code github.com/liyc5929/neuroseqbench)
with a programmed recurrent LIF network of the benchmark's shape 2-128-128-10 at its decay 0.5 and threshold 0.5.

Task, written from the description and the public generator: a sequence of 100 steps with two input channels,
a random bit and a mask with exactly 9 ones. The label is the number of masked bits that are 1 (10 classes,
balanced). The classifier reads the last layer at the last step.

Network model of the benchmark (as in al.py): v[t] = decay * v[t-1] * (1 - y[t-1]) + input[t], y[t] = (v[t] > 0.5);
the first layer also receives its own spikes of the previous step.

Circuit (41 of the 256 neurons are used): 40 gates and one neuron that fires at every step. A gate fires unless
all of its conditions hold, with drive w * (number of conditions that fail), w = 0.75. A gate that does not fire
has drive exactly 0, and a gate that fires is reset, so no potential is carried over and the decay does not matter.
  layer 1: G fires at every step. For each count i = 0..9 three neurons n[i][c], one for each input case c
           (mask 0; mask 1 and bit 0; mask 1 and bit 1): n[i][c] is silent iff the count before the step is i
           and the input case is c. Exactly one of the 30 is silent at every step. "The count before the step is
           i" is a linear function of the silent neurons of the previous step; G marks the first step.
  layer 2: c[j], j = 0..9, fires iff the count after the step is j (one of two or three n-neurons is silent).
  readout: class j reads c[j].

usage: badd.py [N_SEQUENCES] [SEED] [DECAY] [SEQ_LEN]
"""
import json, sys
import numpy as np
import torch

T, N1, N2, THR, W = 100, 128, 128, 0.5, 0.75      # 0.75 and its multiples are exact in binary
M0, M1B0, M1B1 = 0, 1, 2


def make_batch(n, rng, seq_len=T):
    """Balanced over the 10 classes, as in the benchmark."""
    xs, ys = [], []
    need = {c: n // 10 + (1 if c < n % 10 else 0) for c in range(10)}
    while any(v > 0 for v in need.values()):
        bits = (rng.random((4096, seq_len)) < 0.5).astype(np.float32)
        mask = np.zeros((4096, seq_len), dtype=np.float32)
        pos = np.argsort(rng.random((4096, seq_len)), axis=1)[:, :9]
        np.put_along_axis(mask, pos, 1.0, axis=1)
        y = (bits * mask).sum(1).astype(int)
        for c in range(10):
            idx = np.where(y == c)[0][:need[c]]
            need[c] -= len(idx)
            xs.append(np.stack([bits[idx], mask[idx]], axis=2)); ys.append(y[idx])
    x, y = np.concatenate(xs), np.concatenate(ys)
    perm = rng.permutation(len(y))
    return torch.from_numpy(x[perm]).permute(1, 0, 2).contiguous(), y[perm]          # (T, B, 2)


def circuit():
    n = lambda i, c: 1 + 3 * i + c
    G = 0
    fc0, b0 = torch.zeros(N1, 2), torch.zeros(N1)                 # input channels: 0 = bit, 1 = mask
    rec1, rb1 = torch.zeros(N1, N1), torch.zeros(N1)
    b0[G] = 1.0
    for i in range(10):
        sources = [n(i, M0), n(i, M1B0)] + ([n(i - 1, M1B1)] if i > 0 else [])    # silent one of these: count is i
        k_init = len(sources) - (1 if i == 0 else 0)                              # first step: count 0
        for c in (M0, M1B0, M1B1):
            m = n(i, c)
            k = 2 if c == M0 else 3                                               # number of inputs of the gate
            # drive = W * (k - state - literals), state = len(sources) - sum(n[sources]) - k_init * (1 - G)
            rb1[m] = W * (k - len(sources) + k_init)
            for s in sources:
                rec1[m, s] += W
            rec1[m, G] -= W * k_init
            if c == M0:                    # literal 1 - mask
                b0[m] -= W; fc0[m, 1] += W
            elif c == M1B0:                # literals mask and 1 - bit
                fc0[m, 1] -= W; b0[m] -= W; fc0[m, 0] += W
            else:                          # literals mask and bit
                fc0[m, 1] -= W; fc0[m, 0] -= W
    fc1, b1 = torch.zeros(N2, N1), torch.zeros(N2)
    for j in range(10):
        sources = [n(j, M0), n(j, M1B0)] + ([n(j - 1, M1B1)] if j > 0 else [])
        b1[j] = W * len(sources)
        for s in sources:
            fc1[j, s] = -W
    cls, cb = torch.zeros(10, N2), torch.zeros(10)
    for j in range(10):
        cls[j, j] = 1.0
    return dict(fc0=fc0, b0=b0, rec1=rec1, rb1=rb1, fc1=fc1, b1=b1, cls=cls, cb=cb)


@torch.no_grad()
def run(x, c, decay):
    """x: (T, B, 2). Returns the classifier output at the last step (B, 10) and spikes per sequence."""
    B = x.shape[1]
    v1 = torch.zeros(B, N1); y1 = torch.zeros(B, N1); v2 = torch.zeros(B, N2); y2 = torch.zeros(B, N2)
    spikes = 0.0
    for t in range(x.shape[0]):
        v1 = decay * v1 * (1 - y1) + x[t] @ c["fc0"].T + c["b0"] + y1 @ c["rec1"].T + c["rb1"]
        y1 = (v1 > THR).float()
        v2 = decay * v2 * (1 - y2) + y1 @ c["fc1"].T + c["b1"]
        y2 = (v2 > THR).float()
        spikes += (y1.sum() + y2.sum()).item()
    return y2 @ c["cls"].T + c["cb"], spikes / B


def evaluate(n, seed, decay=0.5, seq_len=T):
    rng = np.random.default_rng(seed)
    x, y = make_batch(n, rng, seq_len)
    out, spikes = run(x, circuit(), decay)
    pred = out.argmax(1).numpy()
    one_hot = bool(((out > 0).sum(1) == 1).all())
    return dict(task="binary adding", seq_len=seq_len, neurons_used=41, decay=decay, sequences=n, seed=seed,
                accuracy=float((pred == y).mean()), wrong=int((pred != y).sum()), exactly_one_class_unit=one_hot,
                spikes_per_neuron_per_step=spikes / seq_len / (N1 + N2))


if __name__ == "__main__":
    torch.set_num_threads(1)
    a = sys.argv[1:]
    print(json.dumps(evaluate(int(a[0]) if a else 2000, int(a[1]) if len(a) > 1 else 0,
                              float(a[2]) if len(a) > 2 else 0.5,
                              int(a[3]) if len(a) > 3 else T)), flush=True)
