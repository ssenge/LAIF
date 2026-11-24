"""Surrogate-gradient baseline on the STORE-RECALL task: 60 recurrent LIF neurons trained with BPTT,
following the settings of the reference code (bin/tutorial_storerecall_with_LSNN.py, MIT licence):
400 iterations, batch 64, Adam, learning rate 0.01 times 0.3 every 100 iterations, pseudo-derivative
0.3 * max(0, 1 - |v - thr| / thr), rate regularization towards 10 Hz, no self-connections, test on 2048
sequences. The network state starts from zero in every batch (the reference code carries it over between
training batches).

usage: sr_train.py SETTING SEED [N] [ITERS]     e.g. sr_train.py "2 s" 0
"""
import json, sys, time
import numpy as np
import torch
from sr_protocol import N_IN, TAU, THR, N_REF, RECALL, TABLE1, make_batch


class Spike(torch.autograd.Function):
    @staticmethod
    def forward(ctx, v_scaled):
        ctx.save_for_backward(v_scaled)
        return (v_scaled > 0).float()

    @staticmethod
    def backward(ctx, g):
        (v_scaled,) = ctx.saved_tensors
        return g * 0.3 * torch.clamp(1 - v_scaled.abs(), min=0)


class Net(torch.nn.Module):
    def __init__(self, n, gen):
        super().__init__()
        self.W_in = torch.nn.Parameter(torch.randn(n, N_IN, generator=gen) / N_IN ** 0.5)
        self.W_rec = torch.nn.Parameter(torch.randn(n, n, generator=gen) / n ** 0.5)
        self.W_out = torch.nn.Parameter((torch.rand(n, 2, generator=gen) * 2 - 1) * (6 / (n + 2)) ** 0.5)

    def forward(self, x, tau_char):
        """x: (T, B, 40). Returns step-averaged readout (B, L, 2) and mean rate per neuron (spikes per ms)."""
        T, B, _ = x.shape
        n = self.W_rec.shape[0]
        decay = float(np.exp(-1.0 / TAU))
        W_rec = self.W_rec * (1 - torch.eye(n))            # no self-connections, as in the reference code
        v = x.new_zeros(B, n); z = x.new_zeros(B, n); ref = x.new_zeros(B, n); psp = x.new_zeros(B, n)
        steps, acc, rate = [], 0, 0
        for t in range(T):
            i_t = x[t] @ self.W_in.T + z @ W_rec.T
            new_z = Spike.apply((v - THR) / THR) * (ref <= 0).float()
            v = decay * v + (1 - decay) * i_t - z * THR
            ref = torch.where(new_z.detach() > 0, torch.full_like(ref, N_REF), ref - 1)
            z = new_z
            psp = decay * psp + (1 - decay) * z
            acc = acc + psp
            rate = rate + z
            if (t + 1) % tau_char == 0:
                steps.append(acc / tau_char @ self.W_out)
                acc = 0
        return torch.stack(steps, 1), rate.mean(0) / T


def main(setting, seed, n=60, iters=400, batch=64):
    torch.set_num_threads(1)
    seq_len, tau_char, seq_delay = TABLE1[setting]
    gen = torch.Generator().manual_seed(seed)
    net = Net(n, gen)
    opt = torch.optim.Adam(net.parameters(), lr=0.01)
    t0, curve = time.time(), []
    for it in range(iters):
        if it and it % 100 == 0:
            for g in opt.param_groups:
                g["lr"] *= 0.3
        x, sym, target, _ = make_batch(batch, seq_len, tau_char, seq_delay, 10_000_000 + seed * 100_000 + it)
        out, rate = net(x, tau_char)
        m = torch.from_numpy(sym == RECALL)
        loss = torch.nn.functional.cross_entropy(out[m], torch.from_numpy(target)[m]) + ((rate - 0.01) ** 2).sum()
        opt.zero_grad(); loss.backward(); opt.step()
        curve.append(round((out[m].argmax(1).numpy() == target[m.numpy()]).mean().item(), 3))
    hits, rates = [], []
    with torch.no_grad():
        for k in range(8):
            x, sym, target, _ = make_batch(256, seq_len, tau_char, seq_delay, 20_000_000 + seed * 1000 + k)
            out, rate = net(x, tau_char)
            m = sym == RECALL
            hits.append(out.argmax(2).numpy()[m] == target[m]); rates.append(rate.mean().item() * 1000)
    hit = np.concatenate(hits)
    return dict(model="LIF trained", setting=setting, seed=seed, n=n, iters=iters, recalls=len(hit), acc=float(hit.mean()),
                rate_hz_per_neuron=float(np.mean(rates)), train_acc_last20=float(np.mean(curve[-20:])),
                seconds=round(time.time() - t0))


if __name__ == "__main__":
    a = sys.argv[1:]
    print(json.dumps(main(a[0], int(a[1]), *(int(v) for v in a[2:4]))), flush=True)
