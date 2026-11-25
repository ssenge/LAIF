"""Trained baseline on the AL task: the recurrent LIF network 3-128-176-176-2 of the Neuromorphic Sequential
Arena (arXiv:2505.22035), trained with backpropagation through time in the setting of the benchmark's AL run for
recurrent LIF: 50,000 training and 5,000 test sequences of length 400, batch 256, AdamW with learning rate 1e-3,
learning rate times 0.8 every 10 epochs, gradient clipping at 1, triangle surrogate gradient of width 0.4,
threshold 0.5, cross-entropy on the time-averaged output. As in the benchmark, the reported number is the best
test accuracy over the epochs. The number of epochs is an argument (the benchmark uses 100).

usage: al_train.py SEED EPOCHS [DECAY] [N_TRAIN]
"""
import json, sys, time
import numpy as np
import torch
from al import make_batch, T, THR, N1, N2, N3

WIDTH = 0.4


class Spike(torch.autograd.Function):
    @staticmethod
    def forward(ctx, v):
        ctx.save_for_backward(v)
        return (v > THR).float()

    @staticmethod
    def backward(ctx, g):
        (v,) = ctx.saved_tensors
        return g * (WIDTH - (v - THR).abs()).clamp(min=0) / WIDTH ** 2


class Net(torch.nn.Module):
    def __init__(self, decay):
        super().__init__()
        self.decay = decay
        self.fc0, self.fc1, self.fc2 = torch.nn.Linear(3, N1), torch.nn.Linear(N1, N2), torch.nn.Linear(N2, N3)
        self.rec1, self.rec2 = torch.nn.Linear(N1, N1), torch.nn.Linear(N2, N2)
        self.cls = torch.nn.Linear(N3, 2)

    def forward(self, x):                       # x: (T, B, 3)
        B, d = x.shape[1], self.decay
        v1 = x.new_zeros(B, N1); y1 = x.new_zeros(B, N1)
        v2 = x.new_zeros(B, N2); y2 = x.new_zeros(B, N2)
        v3 = x.new_zeros(B, N3); y3 = x.new_zeros(B, N3)
        out = 0
        for t in range(x.shape[0]):
            v1 = d * v1 * (1 - y1) + self.fc0(x[t]) + self.rec1(y1); y1 = Spike.apply(v1)
            v2 = d * v2 * (1 - y2) + self.fc1(y1) + self.rec2(y2); y2 = Spike.apply(v2)
            v3 = d * v3 * (1 - y3) + self.fc2(y2); y3 = Spike.apply(v3)
            out = out + self.cls(y3)
        return out / x.shape[0]


def main(seed, epochs, decay=0.5, n_train=50000, n_test=5000, batch=256):
    torch.set_num_threads(1)
    torch.manual_seed(seed)
    rng = np.random.default_rng(1000 + seed)
    xtr, ytr, _ = make_batch(n_train, rng)
    xte, yte, _ = make_batch(n_test, rng)
    ytr_t = torch.from_numpy(ytr)
    net = Net(decay)
    opt = torch.optim.AdamW(net.parameters(), lr=1e-3, weight_decay=0)
    sched = torch.optim.lr_scheduler.StepLR(opt, step_size=10, gamma=0.8)
    t0, test_acc, train_acc = time.time(), [], []
    for ep in range(epochs):
        perm = torch.randperm(n_train)
        ok = 0
        for i in range(0, n_train, batch):
            idx = perm[i:i + batch]
            out = net(xtr[:, idx])
            loss = torch.nn.functional.cross_entropy(out, ytr_t[idx])
            opt.zero_grad(); loss.backward()
            torch.nn.utils.clip_grad_norm_(net.parameters(), 1.0)
            opt.step()
            ok += int((out.argmax(1) == ytr_t[idx]).sum())
        sched.step()
        with torch.no_grad():
            pred = torch.cat([net(xte[:, i:i + 1000]).argmax(1) for i in range(0, n_test, 1000)]).numpy()
        test_acc.append(round(float((pred == yte).mean()), 4)); train_acc.append(round(ok / n_train, 4))
        print(json.dumps(dict(epoch=ep + 1, train_acc=train_acc[-1], test_acc=test_acc[-1],
                              seconds=round(time.time() - t0))), file=sys.stderr, flush=True)
    return dict(model="recurrent LIF trained", task="AL", seed=seed, decay=decay, epochs=epochs, n_train=n_train,
                best_test_acc=max(test_acc), last_test_acc=test_acc[-1], train_acc=train_acc, test_acc=test_acc,
                label_mean=float(yte.mean()), seconds=round(time.time() - t0))


if __name__ == "__main__":
    a = sys.argv[1:]
    print(json.dumps(main(int(a[0]), int(a[1]), *(float(v) for v in a[2:3]), *(int(v) for v in a[3:4]))), flush=True)
