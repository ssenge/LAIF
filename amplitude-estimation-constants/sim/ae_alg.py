"""The amplitude estimation algorithm of ae_bound.py, run with exactly sampled measurement outcomes.
Checks that the Q count never exceeds the certified bound and that the error exceeds eps at most at rate alpha.

usage: ae_alg.py eps alpha r kappa gamma alpha_last runs [seed]
"""
import sys
import numpy as np
from ae_core import cp, HALF
from ae_bound import wtable, qround, NGRID


def estimate(theta, eps, alpha_last, r, kappa, gamma, rng, rho=1.02):
    stop = np.arcsin(2 * eps)
    g = [stop]
    while g[-1] < HALF:
        g.append(min(HALF, g[-1] * rho))
    l, u, q = 0.0, HALF, 0
    while u - l > stop:
        w = u - l
        c = int(np.searchsorted(g, w)) - 1          # cell (g[c], g[c+1]] containing w
        lo, hi = g[c], g[c + 1]
        a_c = qround(alpha_last * (stop / hi) ** gamma)
        tab = wtable(a_c)
        cap = max(1, int(kappa * HALF / w))
        K = next(K for K in range(cap if cap % 2 else cap - 1, 0, -2)
                 if np.floor(K * l / HALF) == np.floor(K * u / HALF) or K * u / HALF == np.floor(K * u / HALF))
        target = max(lo / r, stop * 0.999)
        i = next(j for j, v in enumerate(tab) if v <= target * K)
        N = NGRID[i]
        h = rng.binomial(N, np.sin(K * theta) ** 2)
        q += N * (K - 1) // 2
        plo, phi = cp(h, N, a_c)
        j = int(np.floor(K * l / HALF))
        f0, f1 = np.arcsin(np.sqrt(plo)), np.arcsin(np.sqrt(phi))
        if j % 2:                                   # decreasing branch: phi = j pi/2 + pi/2 - asin(sqrt p)
            a, b = (j + 1) * HALF - f1, (j + 1) * HALF - f0
        else:
            a, b = j * HALF + f0, j * HALF + f1
        nl, nu = max(l, a / K), min(u, b / K)
        if nl > nu:                                 # empty after a miss: keep the new interval
            nl, nu = a / K, b / K
        l, u = nl, nu
    return (np.sin(l) ** 2 + np.sin(u) ** 2) / 2, q        # error <= sin(u - l) / 2 <= eps


if __name__ == "__main__":
    eps, alpha, r, kappa, gamma, al = map(float, sys.argv[1:7])
    runs = int(sys.argv[7]); rng = np.random.default_rng(int(sys.argv[8]) if len(sys.argv) > 8 else 0)
    thetas = np.r_[rng.random(runs // 2) * HALF, np.pi / 6 + (rng.random(runs - runs // 2) - 0.5) * 1e-3]
    errs, qs = [], []
    for th in thetas:
        est, q = estimate(th, eps, al, r, kappa, gamma, rng)
        errs.append(abs(est - np.sin(th) ** 2)); qs.append(q)
    errs, qs = np.array(errs), np.array(qs)
    print(f"runs {runs}: failure rate {np.mean(errs > eps):.4f} (alpha {alpha}), max Q {qs.max()} = {qs.max() * eps:.2f}/eps, "
          f"mean Q {qs.mean() * eps:.2f}/eps", flush=True)
