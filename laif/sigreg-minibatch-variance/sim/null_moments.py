"""Null mean and variance of the minibatch SIGReg statistic (exact integral over t, weight e^{-t^2/2}).

For a slice X_1..X_N, T = (1/N) sum_{j,k} H(X_j, X_k) with
H(x, y) = sqrt(2 pi) e^{-(x-y)^2/2} - sqrt(pi) (e^{-x^2/4} + e^{-y^2/4}) + sqrt(2 pi / 3).
Claims checked here, for z ~ N(0, I_K) and M directions a_m:
  E[T] = B = sqrt(2 pi) (1 - 3^{-1/2})                                  (any N)
  Var[T] = 2 (1 - 1/N) C(1) + V(1) / N                                 (one slice)
  Cov between slices with a_m . a_m' = r:  2 (1 - 1/N) C(r) + V(r) / N
  C(r) = 2 pi [(9 - 4 r^2)^{-1/2} - sqrt(2) (9/2 - r^2/2)^{-1/2} + 1/3]
  V(r) = 4 pi [(9/4 - r^2/4)^{-1/2} - 2/3]
"""
import numpy as np

SQ2PI, SQPI = np.sqrt(2 * np.pi), np.sqrt(np.pi)
B = SQ2PI * (1 - 3 ** -0.5)
C = lambda r: 2 * np.pi * ((9 - 4 * r**2) ** -0.5 - np.sqrt(2) * (4.5 - r**2 / 2) ** -0.5 + 1 / 3)
V = lambda r: 4 * np.pi * ((2.25 - r**2 / 4) ** -0.5 - 2 / 3)


def n_ep(x):
    """The statistic T for each column of x (N x M), exact integral over t."""
    d = x[:, None, :] - x[None, :, :]
    f = np.exp(-x**2 / 4)
    N = x.shape[0]
    return (SQ2PI * np.exp(-d**2 / 2).sum((0, 1)) - 2 * N * SQPI * f.sum(0)) / N + N * np.sqrt(2 * np.pi / 3)


def quad_check():
    # H against a direct quadrature of the characteristic-function form, for one small sample
    rng = np.random.default_rng(0)
    x = rng.standard_normal((7, 1))
    t = np.linspace(-12, 12, 200001)
    phi = np.exp(1j * t[:, None] * x[:, 0][None, :]).mean(1)
    ep = np.trapezoid(np.abs(phi - np.exp(-t**2 / 2)) ** 2 * np.exp(-t**2 / 2), t)
    assert abs(7 * ep - n_ep(x)[0]) < 1e-8, (7 * ep, n_ep(x)[0])


def main():
    quad_check()
    assert abs(C(0)) < 1e-12 and abs(V(0)) < 1e-12
    assert abs(C(1) - 2 * np.pi * (5**-0.5 - 2**-0.5 + 1 / 3)) < 1e-12
    rng = np.random.default_rng(1)
    K, M, T = 32, 8, 4000
    A = rng.standard_normal((K, M)); A /= np.linalg.norm(A, axis=0)
    R = A.T @ A
    for N in (16, 128):
        s = np.array([n_ep(rng.standard_normal((N, K)) @ A) for _ in range(T)])   # T x M
        cov_th = 2 * (1 - 1 / N) * C(R) + V(R) / N
        m_err = abs(s.mean() - B) / (s.mean(1).std() / np.sqrt(T))
        v1, v1_th = s[:, 0].var(), cov_th[0, 0]
        va, va_th = s.mean(1).var(), cov_th.mean()
        print(f"N={N}: mean {s.mean():.4f} vs B {B:.4f} ({m_err:.1f} se); one-slice var {v1:.4f} vs {v1_th:.4f}; "
              f"slice-average var {va:.4f} vs {va_th:.4f}")
        assert m_err < 4
        assert abs(v1 / v1_th - 1) < 0.08 and abs(va / va_th - 1) < 0.08
    # high-dimensional floor: for random directions E r^2 = 1/K and C(r) = 2 pi r^2 / 27 + O(r^4)
    r = 1e-3
    assert abs(C(r) / r**2 - 2 * np.pi / 27) < 1e-4
    assert abs(V(r) / r**2 - 4 * np.pi / 27) < 1e-4
    for N in (2, 16, 256):  # N cancels in the 1/K floor
        assert abs((2 * (1 - 1 / N) * C(r) + V(r) / N) / r**2 - 4 * np.pi / 27) < 1e-4
    print("all checks passed")


if __name__ == "__main__":
    main()
