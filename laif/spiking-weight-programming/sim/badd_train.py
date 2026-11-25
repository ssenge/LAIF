"""Trained baseline on binary adding: the recurrent LIF network 2-128-128-10 of the segregated temporal probe
(arXiv:2502.09449) with backpropagation through time in the setting of its run for recurrent LIF: 50,000 training
and 2,000 test sequences of length 100 (balanced classes), batch 250, 50 epochs, AdamW with learning rate 5e-4,
learning rate times 0.8 every 10 epochs, rectangular surrogate gradient of width 0.4, decay 0.5, threshold 0.5,
cross-entropy on the classifier output of the last step. The reported number is the best test accuracy over the
epochs, as in the benchmark.

usage: badd_train.py SEED [EPOCHS]
"""
import json, sys, time
import numpy as np
import torch
from badd import make_batch, T, THR, N1, N2

WIDTH, DECAY = 0.4, 0.5


class Spike(torch.autograd.Function):
    @staticmethod
    def forward(ctx, v):
        ctx.save_for_backward(v)
        return (v > THR).float()

    @staticmethod
    def backward(ctx, g):
        (v,) = ctx.saved_tensors
        return g * ((v - THR).abs() < WIDTH / 2).float()


class Net(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.fc0, self.fc1 = torch.nn.Linear(2, N1), torch.nn.Linear(N1, N2)
        self.rec1 = torch.nn.Linear(N1, N1)
        self.cls = torch.nn.Linear(N2, 10)

    def forward(self, x):                       # x: (T, B, 2)
        B = x.shape[1]
        v1 = x.new_zeros(B, N1); y1 = x.new_zeros(B, N1); v2 = x.new_zeros(B, N2); y2 = x.new_zeros(B, N2)
        for t in range(x.shape[0]):
            v1 = DECAY * v1 * (1 - y1) + self.fc0(x[t]) + self.rec1(y1); y1 = Spike.apply(v1)
            v2 = DECAY * v2 * (1 - y2) + self.fc1(y1); y2 = Spike.apply(v2)
        return self.cls(y2)


def main(seed, epochs=50, n_train=50000, n_test=2000, batch=250):
    torch.set_num_threads(1)
    torch.manual_seed(seed)
    rng = np.random.default_rng(2000 + seed)
    xtr, ytr = make_batch(n_train, rng)
    xte, yte = make_batch(n_test, rng)
    ytr_t = torch.from_numpy(ytr)
    net = Net()
    opt = torch.optim.AdamW(net.parameters(), lr=5e-4, weight_decay=0.0)
    sched = torch.optim.lr_scheduler.StepLR(opt, step_size=10, gamma=0.8)
    t0, test_acc, train_acc = time.time(), [], []
    for ep in range(epochs):
        perm = torch.randperm(n_train)
        ok = 0
        for i in range(0, n_train, batch):
            idx = perm[i:i + batch]
            out = net(xtr[:, idx])
            loss = torch.nn.functional.cross_entropy(out, ytr_t[idx])
            opt.zero_grad(); loss.backward(); opt.step()
            ok += int((out.argmax(1) == ytr_t[idx]).sum())
        sched.step()
        with torch.no_grad():
            pred = net(xte).argmax(1).numpy()
        test_acc.append(round(float((pred == yte).mean()), 4)); train_acc.append(round(ok / n_train, 4))
        print(json.dumps(dict(epoch=ep + 1, train_acc=train_acc[-1], test_acc=test_acc[-1],
                              seconds=round(time.time() - t0))), file=sys.stderr, flush=True)
    return dict(model="recurrent LIF trained", task="binary adding", seed=seed, epochs=epochs,
                best_test_acc=max(test_acc), last_test_acc=test_acc[-1], train_acc=train_acc, test_acc=test_acc,
                seconds=round(time.time() - t0))


if __name__ == "__main__":
    a = sys.argv[1:]
    print(json.dumps(main(int(a[0]), *(int(v) for v in a[1:2]))), flush=True)
