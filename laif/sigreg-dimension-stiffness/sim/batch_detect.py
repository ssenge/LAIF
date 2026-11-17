"""Minibatch SIGReg (the N * EP statistic, as in the paper and the package) on Gaussian batches:
isotropic N(0, I) against rank-K/2 collapse N(0, 2 P) with the same trace. Also checks E[N EP] = N D(s) + B(s)."""
import numpy as np, torch
from slice_function import D, B
torch.manual_seed(0)
def sigreg(x, M, tmax=5.0, n=17):           # paper form: t in [-tmax, tmax], trapezoid, weight e^{-t^2/2}
    t = torch.linspace(-tmax, tmax, n, dtype=torch.float64)
    phi = torch.exp(-t * t / 2)
    A = torch.randn(x.shape[1], M, dtype=torch.float64); A /= A.norm(dim=0)
    xt = (x @ A).unsqueeze(-1) * t
    err = (torch.cos(xt).mean(0) - phi) ** 2 + torch.sin(xt).mean(0) ** 2
    return (torch.trapezoid(err * phi, t, dim=-1) * x.shape[0]).mean().item()
# exact expectation identity for one fixed slice of variance s (integral over R ~ [-12, 12] with fine grid)
for s in [0.5, 1.0, 2.0]:
    N = 64; vals = [sigreg(torch.randn(N, 1, dtype=torch.float64) * s ** 0.5, 1, tmax=12, n=2001) for _ in range(4000)]
    pred = N * D(s) + B(s); se = np.std(vals) / np.sqrt(len(vals))
    assert abs(np.mean(vals) - pred) < 4 * se, (s, np.mean(vals), pred)
print("E[N EP] = N D(s) + B(s) confirmed for s in {0.5, 1, 2}")
N, M, T = 256, 1024, 40
print(f"{'K':>5} {'iso mean':>9} {'iso sd':>7} {'rank K/2 mean':>13} {'sd':>6} {'gap/sd':>7} {'pred gap':>8}")
for K in [16, 64, 256, 1024]:
    iso = [sigreg(torch.randn(N, K, dtype=torch.float64), M) for _ in range(T)]
    P = torch.zeros(K, dtype=torch.float64); P[: K // 2] = 2 ** 0.5
    col = [sigreg(torch.randn(N, K, dtype=torch.float64) * P, M) for _ in range(T)]
    gap = np.mean(col) - np.mean(iso)
    pred = (N - 2) * 0.2412 * 1.0 / (K + 2)          # (N D''(1) + B''(1)) v/(K+2), v = 1
    print(f"{K:>5} {np.mean(iso):9.4f} {np.std(iso):7.4f} {np.mean(col):13.4f} {np.std(col):6.4f} {gap/np.std(iso):7.2f} {pred:8.4f}")
