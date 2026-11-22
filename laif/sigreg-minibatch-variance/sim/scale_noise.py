"""Scale direction of the minibatch SIGReg slice statistic T(s), the statistic of one slice, for samples sqrt(s) X, X ~ N(0, 1).

Claims checked:
  (a) E T(s) = N D(s) + B(s) is minimized at s* = 1 - 2/N + O(1/N^2), since B'(1) = 2 D''(1) exactly
      (B'(1) = sqrt(2 pi) 3^{-3/2}, D''(1) = (3/2) sqrt(2 pi) 3^{-5/2}).
  (b) Var[dT/ds at s = 1] = 4 N Var G1 + O(1), Var G1 = (pi/64) Var[e^{-X^2/4} (X^2 - 2)] ~ 0.03728,
      where G1(x) = sqrt(pi) e^{-x^2/4} (x^2/8 - 1/4) + const is the first projection of the s-derivative kernel.
"""
import numpy as np
from scipy.optimize import minimize_scalar

SQ2PI, SQPI = np.sqrt(2 * np.pi), np.sqrt(np.pi)
D = lambda s: SQ2PI * ((2 * s + 1) ** -0.5 - 2 * (s + 2) ** -0.5 + 3 ** -0.5)
B = lambda s: SQ2PI * (1 - (2 * s + 1) ** -0.5)


def dT_ds(x):
    """Exact derivative in s at s = 1 of (1/N) sum_{j,k} H(sqrt(s) x_j, sqrt(s) x_k), per column of x (N x T)."""
    N = x.shape[0]
    d = x[:, None, :] - x[None, :, :]
    # d/ds of sqrt(2pi) e^{-s d^2/2} at s=1 is -sqrt(2pi) d^2/2 e^{-d^2/2}; of -2N sqrt(pi) e^{-s x^2/4}: +2N sqrt(pi) x^2/4 e^{-x^2/4}
    return (-SQ2PI * (d**2 / 2 * np.exp(-d**2 / 2)).sum((0, 1)) + 2 * N * SQPI * (x**2 / 4 * np.exp(-x**2 / 4)).sum(0)) / N


def main():
    D2 = 1.5 * SQ2PI * 3 ** -2.5
    B1 = SQ2PI * 3 ** -1.5
    assert abs(B1 / D2 - 2) < 1e-12
    for N in (64, 256, 1024):
        s_star = minimize_scalar(lambda s: N * D(s) + B(s), bounds=(0.5, 1.5), method="bounded", options={"xatol": 1e-12}).x
        print(f"N={N}: s* = {s_star:.6f}, 1 - 2/N = {1 - 2 / N:.6f}, N^2 (s* - 1 + 2/N) = {N**2 * (s_star - 1 + 2 / N):.3f}")
        assert abs(s_star - (1 - 2 / N)) < 20 / N**2
    # (b) closed form of Var G1
    x = np.random.default_rng(2).standard_normal(4_000_000)
    vg = np.pi / 64 * np.var(np.exp(-x**2 / 4) * (x**2 - 2))
    e1 = 1.5**-1.5 - 2 * 1.5**-0.5
    e2 = 3 * 2**-2.5 - 4 * 2**-1.5 + 4 * 2**-0.5
    vg_th = np.pi / 64 * (e2 - e1**2)
    assert abs(vg / vg_th - 1) < 0.01, (vg, vg_th)
    rng = np.random.default_rng(3)
    for N in (64, 256):
        T = 3000
        v = np.var(np.concatenate([dT_ds(rng.standard_normal((N, 100))) for _ in range(T // 100)]))
        print(f"N={N}: Var dT/ds = {v:.3f}, 4 N Var G1 = {4 * N * vg_th:.3f}, ratio {v / (4 * N * vg_th):.3f}")
        assert abs(v / (4 * N * vg_th) - 1) < 0.15
    # finite-difference check of dT_ds
    xs = rng.standard_normal((50, 1)); h = 1e-5
    Tfun = lambda s: ((SQ2PI * np.exp(-s * (xs - xs.T) ** 2 / 2)).sum() - 2 * 50 * SQPI * np.exp(-s * xs**2 / 4).sum()) / 50
    assert abs((Tfun(1 + h) - Tfun(1 - h)) / (2 * h) - dT_ds(xs)[0]) < 1e-5
    print(f"Var G1 = {vg_th:.5f}; all checks passed")


if __name__ == "__main__":
    main()
