"""Batch size and regularizer weight in linear LeJEPA (reduced objective, K = 2, exact circle quadrature).

Expected minibatch loss at batch size N and weight lam (invariance term averaged over the K coordinates):
F(l) = sum_i c_i l_i + mu E_a h_N(a^T diag(l) a), mu = 4 K lam / (1 - lam), h_N = N D + B.
So F depends on (N, lam) through mu N = 4 K lam N / (1 - lam), up to the bias term mu S_B of relative size 1/N.
Checks: the minimizer is (nearly) unchanged when lam N / (1 - lam) is held fixed, and moves when lam is held fixed.
"""
import numpy as np
from scipy.optimize import minimize
from slice_function import D, D1, B

K = 2
th = (np.arange(4000) + 0.5) * 2 * np.pi / 4000
u = np.stack([np.cos(th) ** 2, np.sin(th) ** 2], 1)          # a_i^2 for a uniform on the circle
B1 = lambda s: np.sqrt(2 * np.pi) * (2 * s + 1) ** -1.5

def spectrum(c, N, lam):
    mu = 4 * K * lam / (1 - lam)
    f = lambda l: c @ l + mu * np.mean(N * D(u @ l) + B(u @ l))
    g = lambda l: c + mu * (u * (N * D1(u @ l) + B1(u @ l))[:, None]).mean(0)
    r = minimize(f, np.ones(K), jac=g, bounds=[(0, None)] * K, method="L-BFGS-B", options={"ftol": 1e-15, "gtol": 1e-12})
    return r.x

if __name__ == "__main__":
    for c in [np.array([0.2, 1.0]), np.array([0.05, 0.6])]:
        base = spectrum(c, 128, 0.05)
        q = 0.05 / 0.95 * 128
        for N in [256, 512, 1024]:
            lam_m = (q / N) / (1 + q / N)                          # lam N / (1 - lam) fixed
            same = spectrum(c, N, lam_m)
            fixed = spectrum(c, N, 0.05)
            dm, df = np.abs(same - base).max(), np.abs(fixed - base).max()
            print(f"c = {c}, N = {N}: base {base.round(4)}, matched (lam = {lam_m:.4f}) {same.round(4)}, "
                  f"lam = 0.05 {fixed.round(4)}; max change {dm:.2e} vs {df:.2e}")
            assert df > 5 * dm
    # threshold kappa_N = mu (N |D'(0)| - sqrt(2 pi)) / K at lam = 0.05, N = 256
    mu = 4 * K * 0.05 / 0.95
    kap = mu * (256 * abs(D1(0.0)) - np.sqrt(2 * np.pi)) / K
    print(f"kappa_N at lam = 0.05, N = 256: {kap:.1f}")
    assert 80 < kap < 90
    print("all checks passed")
