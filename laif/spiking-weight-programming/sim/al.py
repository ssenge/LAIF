"""AL task (autonomous localization) of the Neuromorphic Sequential Arena (arXiv:2505.22035) with a programmed
recurrent LIF network of the benchmark's shape 3-128-176-176-2.

Task, written from the description of the benchmark and its public generator (github.com/liyc5929/neuroseqbench):
a robot starts at the origin facing +y. At each of 400 steps it gets one action: stop, go straight, turn left,
turn right, with probabilities 0.45, 0.45, 0.05, 0.05. The input has three binary channels (straight, left,
right), one step per action. Label: 1 if the final x coordinate is at least 1, else 0.

Network model of the benchmark: three layers of LIF neurons, v[t] = decay * v[t-1] * (1 - y[t-1]) + input[t],
y[t] = (v[t] > 0.5); a layer receives the spikes of the layer below from the same step through a linear map
with bias; the first two layers also receive their own spikes of the previous step through a linear map with
bias; a linear classifier reads the third layer at every step and its outputs are averaged over the 400 steps.

Circuit (194 of the 480 neurons are used):
  layer 1, 16 neurons e[h][a]: fires at step t iff the heading before step t is h and the action is a.
           The heading before step t is a sum of the e-neurons of step t-1; with none of them (first step) it is 0.
  layer 2, 174 neurons u[k], k = -86..87, a thermometer code of x: u[k] fires iff x >= k. One step of the
           counter is a threshold function: u[k]' = [u[k-1] + u[k] + u[k+1] + inc - dec >= 2], where
           inc = e[+x][straight] and dec = e[-x][straight] of the same step.
           2 neurons UP, DOWN: fire when x goes from 0 to 1, and from 1 to 0.
  layer 3, 2 relay neurons for UP and DOWN.
  readout: class 1 gets +1 for every UP spike and -1 for every DOWN spike. Their difference over the whole
           sequence is [final x >= 1], so the time average decides the label with a bias of -0.5 / 400.

usage: al.py [N_SEQUENCES] [SEED] [DECAY]
"""
import json, sys
import numpy as np
import torch

T, CAP, THR = 400, 20, 0.5
N1, N2, N3 = 128, 176, 176
K = 87                                            # x is tracked in [-86, 87]
STOP, STRAIGHT, LEFT, RIGHT = 0, 1, 2, 3
W_AND, B_AND = 0.75, -0.42                        # AND of two unit inputs: drive -0.42, 0.33, 1.08
A_CNT, B_CNT = 1.0, -0.67                         # counter unit: drive (level) - 0.67, fires from level 2


def make_batch(n, rng, seq_len=T, capacity=CAP):
    p = capacity / seq_len
    actions = rng.choice(4, size=(n, seq_len), p=[0.5 - p, 0.5 - p, p, p])
    heading = np.zeros(n, dtype=int)
    x = np.zeros(n, dtype=int)
    for t in range(seq_len):
        a = actions[:, t]
        x += (a == STRAIGHT) * ((heading == 1).astype(int) - (heading == 3).astype(int))
        heading = (heading - (a == LEFT) + (a == RIGHT)) % 4
    inp = np.stack([actions == STRAIGHT, actions == LEFT, actions == RIGHT], axis=2).astype(np.float32)
    return torch.from_numpy(inp).permute(1, 0, 2).contiguous(), (x >= 1).astype(int), x      # (T, B, 3)


def next_heading(h, a):
    return (h - (a == LEFT) + (a == RIGHT)) % 4


def circuit():
    e = lambda h, a: 4 * h + a
    fc0, b0 = torch.zeros(N1, 3), torch.zeros(N1)
    rec1, rb1 = torch.zeros(N1, N1), torch.zeros(N1)
    for h in range(4):
        for a in range(4):
            n = e(h, a)
            for h0 in range(4):                    # heading before this step = heading after the previous step
                for a0 in range(4):
                    if next_heading(h0, a0) == h:
                        rec1[n, e(h0, a0)] += W_AND
            if h == 0:                             # first step: no e-neuron fired before, heading 0
                rb1[n] += W_AND
                rec1[n, :16] -= W_AND
            if a == STOP:                          # heading h AND no input
                fc0[n, :] = -W_AND
                b0[n] = B_AND + W_AND
            else:                                  # heading h AND input a
                fc0[n, a - 1] = W_AND
                b0[n] = B_AND
    u = lambda k: k + K - 1                        # k = -K+1 .. K  ->  0 .. 2K-1
    UP, DOWN = 2 * K, 2 * K + 1
    fc1, b1 = torch.zeros(N2, N1), torch.zeros(N2)
    rec2, rb2 = torch.zeros(N2, N2), torch.zeros(N2)
    inc, dec = e(1, STRAIGHT), e(3, STRAIGHT)
    for k in range(-K + 1, K + 1):
        n = u(k)
        b1[n] = B_CNT
        rec2[n, n] += A_CNT
        if k - 1 >= -K + 1:
            rec2[n, u(k - 1)] += A_CNT
        else:
            rb2[n] += A_CNT                        # below the range x >= k always holds
        if k + 1 <= K:
            rec2[n, u(k + 1)] += A_CNT
        fc1[n, inc] = A_CNT
        if k > -K + 1:
            fc1[n, dec] = -A_CNT                   # the lowest unit never switches off
        if k <= 0:                                 # first step: no unit fired before, x = 0
            rb2[n] += 2 * A_CNT
            rec2[n, u(-K + 1)] -= 2 * A_CNT
    for n, lo, hi, src in ((UP, 0, 1, inc), (DOWN, 1, 2, dec)):       # x = lo before the step AND inc / dec
        b1[n] = B_AND - W_AND
        rec2[n, u(lo)] += W_AND; rec2[n, u(hi)] -= W_AND
        fc1[n, src] = 2 * W_AND
    fc2, b2 = torch.zeros(N3, N2), torch.zeros(N3)
    fc2[0, UP] = 1.0; fc2[1, DOWN] = 1.0
    cls, cb = torch.zeros(2, N3), torch.zeros(2)
    cls[1, 0], cls[1, 1], cb[1] = 1.0, -1.0, -0.5 / T
    return dict(fc0=fc0, b0=b0, rec1=rec1, rb1=rb1, fc1=fc1, b1=b1, rec2=rec2, rb2=rb2, fc2=fc2, b2=b2, cls=cls, cb=cb)


@torch.no_grad()
def run(x, c, decay):
    """x: (T, B, 3). Returns the time-averaged classifier output (B, 2) and spikes per sequence."""
    B = x.shape[1]
    v1 = torch.zeros(B, N1); y1 = torch.zeros(B, N1)
    v2 = torch.zeros(B, N2); y2 = torch.zeros(B, N2)
    v3 = torch.zeros(B, N3); y3 = torch.zeros(B, N3)
    out, spikes = torch.zeros(B, 2), 0.0
    for t in range(x.shape[0]):
        v1 = decay * v1 * (1 - y1) + x[t] @ c["fc0"].T + c["b0"] + y1 @ c["rec1"].T + c["rb1"]
        y1 = (v1 > THR).float()
        v2 = decay * v2 * (1 - y2) + y1 @ c["fc1"].T + c["b1"] + y2 @ c["rec2"].T + c["rb2"]
        y2 = (v2 > THR).float()
        v3 = decay * v3 * (1 - y3) + y2 @ c["fc2"].T + c["b2"]
        y3 = (v3 > THR).float()
        out += y3 @ c["cls"].T + c["cb"]
        spikes += (y1.sum() + y2.sum() + y3.sum()).item()
    return out / x.shape[0], spikes / B


def evaluate(n, seed, decay=0.3, batch=1000):
    rng = np.random.default_rng(seed)
    c = circuit()
    ok = spikes = 0
    xmax = 0
    for k in range(0, n, batch):
        x, label, xf = make_batch(min(batch, n - k), rng)
        out, s = run(x, c, decay)
        ok += int((out.argmax(1).numpy() == label).sum()); spikes += s * len(label)
        xmax = max(xmax, int(np.abs(xf).max()))
    return dict(task="AL", seq_len=T, neurons_used=16 + 2 * K + 2 + 2, decay=decay, sequences=n, seed=seed,
                accuracy=ok / n, wrong=n - ok, max_abs_final_x=xmax,
                spikes_per_neuron_per_step=spikes / n / T / (N1 + N2 + N3))


if __name__ == "__main__":
    torch.set_num_threads(1)
    a = sys.argv[1:]
    print(json.dumps(evaluate(int(a[0]) if a else 1000, int(a[1]) if len(a) > 1 else 0,
                              float(a[2]) if len(a) > 2 else 0.3)), flush=True)
