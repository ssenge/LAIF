"""Reduced linear LeJEPA: minimize F(lam) = sum_i c_i lam_i + mu * E_a D(sum_k lam_k a_k^2) over lam >= 0.

lam = spectrum of the embedding covariance, c = invariance cost per direction (noise-to-signal ratio).
Checks the collapse theorem: at a minimizer, lam_j > 0 implies c_j - c_i <= 2 L mu |lam_i - lam_j| / (K (K+2)).
"""
import numpy as np
from scipy.optimize import minimize
from slice_function import D, D1, L

rng = np.random.default_rng(0)
def solve(c, mu, M=6000):
    K = len(c)
    a = rng.standard_normal((M, K)); a /= np.linalg.norm(a, axis=1, keepdims=True)
    A2 = a * a
    A2 *= 1.0 / (K * A2.mean(0))           # exact first moments, E a_k^2 = 1/K
    def f(lam):
        X = A2 @ lam
        return c @ lam + mu * D(X).mean(), c + mu * (D1(X) @ A2) / M
    r = minimize(f, np.ones(K), jac=True, method="L-BFGS-B", bounds=[(0, None)] * K,
                 options={"maxiter": 20000, "ftol": 1e-15, "gtol": 1e-11})
    return r.x
if __name__ == "__main__":
    print(f"{'K':>5} {'mu':>5} {'rank':>5} {'rank/K':>7} {'eff.rank/K':>10} {'max lam':>8}")
    rows = []
    for mu in [3.0, 10.0]:
        for K in [4, 8, 16, 32, 64, 128, 256]:
            c = np.linspace(0.05, 0.5, K)
            lam = solve(c, mu)
            pos = lam > 1e-6 * lam.max()
            p = lam / lam.sum(); er = np.exp(-(p[p > 0] * np.log(p[p > 0])).sum())
            print(f"{K:>5} {mu:>5.0f} {pos.sum():>5} {pos.mean():7.3f} {er / K:10.3f} {lam.max():8.3f}")
            rows.append((mu, K, pos.mean()))
            # theorem check on all pairs i < j with lam_j > 0 (tolerance for the finite direction sample)
            for i in range(K):
                for j in range(i + 1, K):
                    if lam[j] > 1e-6:
                        assert c[j] - c[i] <= 2 * L * mu * abs(lam[i] - lam[j]) / (K * (K + 2)) * 1.05 + 1e-6, (K, i, j)
    for mu in [3.0, 10.0]:
        fr = [r for m, K, r in rows if m == mu]
        assert fr[-1] < fr[0] and fr[-1] < 0.5, fr
    print("theorem inequality holds at all computed minimizers; rank fraction falls with K at fixed mu")
