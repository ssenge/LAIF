"""Programmed circuit as initialization: the 5-neuron STORE-RECALL circuit is written into the first 5 of 60
LIF neurons, all weights are perturbed with normally distributed noise, and the network is then trained exactly as the
network of sr_train.py (same optimizer, schedule, loss, 400 iterations, batch 64).

usage: sr_finetune.py SETTING SEED SIGMA [ITERS] [REG] [LR]
  SIGMA: standard deviation of the weight noise, in units of the standard deviation of the random
         initialization of sr_train.py (1/sqrt(40) for input weights, 1/sqrt(60) for recurrent weights)
  REG:   coefficient of the rate regularization (1 as in sr_train.py, 0 switches it off)
"""
import json, sys, time
import numpy as np
import torch
from sr_protocol import N_IN, RECALL, TABLE1, make_batch
from sr_train import Net
from sr_circuit import circuit


def test(net, setting, seed):
    seq_len, tau_char, seq_delay = TABLE1[setting]
    hits, rates = [], []
    with torch.no_grad():
        for k in range(8):
            x, sym, target, _ = make_batch(256, seq_len, tau_char, seq_delay, 20_000_000 + seed * 1000 + k)
            out, rate = net(x, tau_char)
            m = sym == RECALL
            hits.append(out.argmax(2).numpy()[m] == target[m]); rates.append(rate.mean().item() * 1000)
    return float(np.concatenate(hits).mean()), float(np.mean(rates))


def main(setting, seed, sigma, iters=400, reg=1.0, lr=0.01, n=60, batch=64):
    torch.set_num_threads(1)
    seq_len, tau_char, seq_delay = TABLE1[setting]
    gen = torch.Generator().manual_seed(seed)
    net = Net(n, gen)
    W_in, W_rec, W_out = circuit()
    k = W_in.shape[0]
    with torch.no_grad():
        net.W_in.zero_(); net.W_rec.zero_(); net.W_out.zero_()
        net.W_in[:k] = W_in; net.W_rec[:k, :k] = W_rec; net.W_out[:k] = W_out * 10   # readout scaled for the loss
        net.W_in.add_(sigma / N_IN ** 0.5 * torch.randn(n, N_IN, generator=gen))
        net.W_rec.add_(sigma / n ** 0.5 * torch.randn(n, n, generator=gen))
    acc0, rate0 = test(net, setting, seed)
    opt = torch.optim.Adam(net.parameters(), lr=lr)
    t0, curve = time.time(), []
    for it in range(iters):
        if it and it % 100 == 0:
            for g in opt.param_groups:
                g["lr"] *= 0.3
        x, sym, target, _ = make_batch(batch, seq_len, tau_char, seq_delay, 10_000_000 + seed * 100_000 + it)
        out, rate = net(x, tau_char)
        m = torch.from_numpy(sym == RECALL)
        loss = torch.nn.functional.cross_entropy(out[m], torch.from_numpy(target)[m]) + reg * ((rate - 0.01) ** 2).sum()
        opt.zero_grad(); loss.backward(); opt.step()
        curve.append((out[m].argmax(1).numpy() == target[m.numpy()]).mean().item())
    acc, rate1 = test(net, setting, seed)
    return dict(model="programmed init + training", setting=setting, seed=seed, n=n, sigma=sigma, iters=iters, reg=reg, lr=lr,
                acc_before=acc0, acc=acc, rate_before=rate0, rate_hz_per_neuron=rate1,
                train_acc_per_50=[round(float(np.mean(curve[i:i + 50])), 3) for i in range(0, iters, 50)],
                seconds=round(time.time() - t0))


if __name__ == "__main__":
    a = sys.argv[1:]
    print(json.dumps(main(a[0], int(a[1]), float(a[2]), *(int(v) for v in a[3:4]), *(float(v) for v in a[4:6]))),
          flush=True)
