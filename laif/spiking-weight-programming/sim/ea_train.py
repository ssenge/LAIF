"""Trained baselines on the evidence accumulation task, following the reference tutorial of the e-prop paper
(tutorial_evidence_accumulation_with_alif.py, BPTT): 100 recurrent neurons, either all LIF ("lif") or 50 LIF and
50 with threshold adaptation ("alif", tau_a = 2000 ms), Adam with learning rate 0.005, batch 64, at most 2000
iterations, rate regularization towards 10 Hz, pseudo-derivative 0.3 * max(0, 1 - |v - A| / thr). As in the
tutorial, training stops when the error on a fresh batch and then on 8 further batches is below 7 %.

usage: ea_train.py MODEL SEED [MAX_ITERS]
"""
import json, sys, time
import numpy as np
import torch
from ea import N_IN, THR, TAU, N_REF, T_RECALL, make_batch

N, TAU_A = 100, 2000.0


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
    def __init__(self, model, gen):
        super().__init__()
        self.W_in = torch.nn.Parameter(torch.randn(N, N_IN, generator=gen) / N_IN ** 0.5)
        self.W_rec = torch.nn.Parameter(torch.randn(N, N, generator=gen) / N ** 0.5)
        self.W_out = torch.nn.Parameter((torch.rand(N, 2, generator=gen) * 2 - 1) * (6 / (N + 2)) ** 0.5)
        rho = float(np.exp(-1 / TAU_A))
        beta_a = 1.7 * (1 - rho) / (1 - float(np.exp(-1 / TAU)))
        self.rho = rho
        self.beta = torch.cat([torch.zeros(N // 2), torch.full((N // 2,), beta_a if model == "alif" else 0.0)])

    def forward(self, x):
        T, B, _ = x.shape
        decay = float(np.exp(-1.0 / TAU))
        W_rec = self.W_rec * (1 - torch.eye(N))
        v = x.new_zeros(B, N); z = x.new_zeros(B, N); r = x.new_zeros(B, N); b = x.new_zeros(B, N); f = x.new_zeros(B, N)
        logits, rate = [], 0
        for t in range(T):
            b = self.rho * b + z
            v = decay * v + x[t] @ self.W_in.T + z @ W_rec.T - z * THR
            z = Spike.apply((v - (THR + b * self.beta)) / THR) * (r <= 0).float()
            r = torch.clamp(r + N_REF * z.detach() - 1, 0, N_REF)
            f = decay * f + (1 - decay) * z
            rate = rate + z
            if t >= T - T_RECALL:
                logits.append(f @ self.W_out)
        return torch.stack(logits, 1), rate.mean(0) / T          # (B, 150, 2), spikes per ms per neuron


def error(net, rng, batch=64):
    with torch.no_grad():
        x, target = make_batch(batch, rng)
        logits, _ = net(x)
        return float((logits.mean(1).argmax(1).numpy() != target).mean())


def main(model, seed, max_iters=2000, batch=64):
    torch.set_num_threads(1)
    gen = torch.Generator().manual_seed(seed)
    rng = np.random.default_rng(seed)
    net = Net(model, gen)
    opt = torch.optim.Adam(net.parameters(), lr=0.005)
    t0, val, stopped = time.time(), [], None
    for it in range(max_iters):
        x, target = make_batch(batch, rng)
        logits, rate = net(x)
        tgt = torch.from_numpy(target)[:, None].expand(-1, T_RECALL)
        loss = torch.nn.functional.cross_entropy(logits.reshape(-1, 2), tgt.reshape(-1)) + ((rate - 0.01) ** 2).sum()
        opt.zero_grad(); loss.backward(); opt.step()
        if it % 10 == 0:
            val.append(error(net, rng))
            if it > 0 and val[-1] < 0.07 and np.mean([error(net, rng) for _ in range(8)]) < 0.07:
                stopped = it
                break
    rng_test = np.random.default_rng(50_000 + seed)
    test_err = float(np.mean([error(net, rng_test, 250) for _ in range(8)]))
    return dict(model=model, task="evidence accumulation", seed=seed, neurons=N, iterations=(stopped if stopped is not None else max_iters),
                stopped_early=stopped is not None, test_accuracy=1 - test_err,
                val_error_last10=float(np.mean(val[-10:])), val_error_curve=[round(float(np.mean(val[i:i + 20])), 3) for i in range(0, len(val), 20)],
                seconds=round(time.time() - t0))


if __name__ == "__main__":
    a = sys.argv[1:]
    print(json.dumps(main(a[0], int(a[1]), *(int(v) for v in a[2:3]))), flush=True)
