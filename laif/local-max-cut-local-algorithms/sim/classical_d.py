"""Radius-1 linear rule z_u = [g_u > lam d^{-1/2} sum_{w~u} g_w] for LocalMaxCut on the d-regular tree. Given the
seeds of v and its neighbours, the neighbours' outputs are independent, with
P(z_u = 1) = Phi((sqrt(d) g_u / lam - g_v) / sqrt(d - 1)); the count of disagreeing neighbours is Poisson-binomial
and is computed exactly. Monte Carlo over the d + 1 seeds only."""
import sys, json, numpy as np
from scipy.stats import norm
def val(d, lam, n, rng):
    k = -(-d // 2); gv = rng.standard_normal(n); gu = rng.standard_normal((n, d))
    zv = gv > lam * gu.sum(1) / np.sqrt(d)
    p1 = norm.cdf((np.sqrt(d) * gu / lam - gv[:, None]) / np.sqrt(d - 1))
    q = np.where(zv[:, None], 1 - p1, p1)                   # P(z_u != z_v)
    D = np.zeros((n, d + 1)); D[:, 0] = 1
    for i in range(d):
        D[:, 1:i + 2] = D[:, 1:i + 2] * (1 - q[:, i:i + 1]) + D[:, 0:i + 1] * q[:, i:i + 1]
        D[:, 0] *= 1 - q[:, i]
    x = D[:, k:].sum(1); return x.mean(), x.std() / np.sqrt(n)
if __name__ == "__main__":
    rng = np.random.default_rng(1)
    for d in [4, 5, 8, 10, 20, 40, 100]:
        res = max((val(d, lam, 40000, np.random.default_rng(2))[0], lam) for lam in [0.6, 0.8, 1.0, 1.2])
        print(d, res, flush=True)
