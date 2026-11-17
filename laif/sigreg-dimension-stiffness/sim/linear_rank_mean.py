"""Reduced linear LeJEPA with the invariance loss averaged over the K dimensions:
F(lam) = (1/K) sum_i c_i lam_i + mu0 * E_a D(sum_k lam_k a_k^2), i.e. the sum form with mu = mu0 K."""
import numpy as np
from linear_rank import solve
from slice_function import L
print(f"{'K':>5} {'mu0':>5} {'rank/K':>7} {'eff.rank/K':>10} {'max lam':>8} {'mean lam':>8}")
out = {}
for mu0 in [0.5, 2.0]:
    for K in [4, 8, 16, 32, 64, 128, 256, 512]:
        c = np.linspace(0.05, 0.5, K)
        lam = solve(c, mu0 * K)
        p = lam / lam.sum(); er = np.exp(-(p[p > 0] * np.log(p[p > 0])).sum())
        print(f"{K:>5} {mu0:>5} {np.mean(lam > 1e-6 * lam.max()):7.3f} {er / K:10.3f} {lam.max():8.3f} {lam.mean():8.3f}")
        out[mu0, K] = er / K
for mu0 in [0.5, 2.0]:
    assert out[mu0, 512] < out[mu0, 8], "effective rank fraction should fall with K"
