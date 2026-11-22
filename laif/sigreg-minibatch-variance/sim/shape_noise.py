"""Gradient noise of minibatch SIGReg in a shape direction, null z ~ N(0, I_K), fresh uniform directions per batch.

Perturb the linear encoder by z -> (I + eps Delta) z with Delta symmetric, trace 0, ||Delta||_F = 1. The slice m moves by
dx_mj = a_m^T Delta z_j = rho_m x_mj + w_mj with rho_m = a_m^T Delta a_m and w_mj independent of x_mj.
Proposition 4: dS/deps (S = slice average of the statistic T) has mean 0 and, to leading order in 1/K, variance
  4 eta / (M K) + 16 N Var(G1) E[rho^2] / M + 32 D''(1)^2 (K^2 + N) / K^4
with eta = E[d1H(X,Y)^2] ~ 0.84628, Var G1 ~ 0.03727, kappa2 = D''(1)^2 / 2 ~ 0.02909, E rho^2 = 2/(K(K+2)).
"""
import numpy as np

SQ2PI, SQPI = np.sqrt(2 * np.pi), np.sqrt(np.pi)
ETA = 2 * np.pi * 2 * 5**-1.5 - np.pi * np.sqrt(2) / 8 + np.pi / 4 * 2**-1.5
VG1 = np.pi / 64 * ((3 * 2**-2.5 - 4 * 2**-1.5 + 4 * 2**-0.5) - (1.5**-1.5 - 2 * 1.5**-0.5) ** 2)
D2 = 1.5 * SQ2PI * 3**-2.5
KAPPA2 = D2**2 / 2


def dS(z, A, Delta):
    """Exact directional derivative of S(z) = mean_m T(a_m^T z) along z -> (I + eps Delta) z."""
    N = z.shape[0]
    x, dx = z @ A, z @ Delta @ A                     # N x M
    d = x[:, None, :] - x[None, :, :]
    d1H = -SQ2PI * d * np.exp(-d**2 / 2) + SQPI / 2 * x[:, None, :] * np.exp(-x[:, None, :] ** 2 / 4)
    g = 2 / N * d1H.sum(1)                           # N x M, per-sample derivative of T
    return (g * dx).sum(0).mean()


def predict(N, K, M):
    # floor: projection term 32 N D''^2 / K^4 plus two degenerate terms 4 (2 D'')^2 / K^2 each = 32 D''^2 (K^2 + N) / K^4
    return 4 * ETA / (M * K) + 16 * N * VG1 * 2 / (K * (K + 2)) / M + 32 * D2**2 * (K**2 + N) / K**4


def main():
    # eta from its definition by Monte Carlo
    rng = np.random.default_rng(4)
    X, Y = rng.standard_normal((2, 2_000_000))
    eta_mc = np.mean((-SQ2PI * (X - Y) * np.exp(-(X - Y) ** 2 / 2) + SQPI / 2 * X * np.exp(-X**2 / 4)) ** 2)
    assert abs(eta_mc / ETA - 1) < 0.01, (eta_mc, ETA)
    # kappa2: leading r^2 coefficient of Cov(G1(X), G1(X')) is (E[G1(X)(X^2 - 1)])^2 / 2, and E[G1(X)(X^2 - 1)] = D''(1)
    g1 = lambda x: SQPI * np.exp(-x**2 / 4) * (x**2 / 8 - 0.25)
    assert abs(np.mean(g1(X) * (X**2 - 1)) / D2 - 1) < 0.01
    # finite-difference check of dS
    K, N = 8, 20
    z = rng.standard_normal((N, K)); A = rng.standard_normal((K, 3)); A /= np.linalg.norm(A, axis=0)
    Dl = np.diag([1.0, -1.0] + [0.0] * (K - 2)) / np.sqrt(2)
    def S(zz):
        x = zz @ A; dd = x[:, None, :] - x[None, :, :]
        return ((SQ2PI * np.exp(-dd**2 / 2).sum((0, 1)) - 2 * N * SQPI * np.exp(-x**2 / 4).sum(0)) / N).mean()
    h = 1e-6
    assert abs((S(z @ (np.eye(K) + h * Dl).T) - S(z @ (np.eye(K) - h * Dl).T)) / (2 * h) - dS(z, A, Dl)) < 1e-5
    # variance against Proposition 4
    for K, N, T, Ms in ((16, 64, 2000, (1, 8, 64, 256)), (32, 64, 1500, (1, 64, 256))):
      Delta = np.diag([1.0, -1.0] + [0.0] * (K - 2)) / np.sqrt(2)
      for M in Ms:
        v = []
        for _ in range(T):
            A = rng.standard_normal((K, M)); A /= np.linalg.norm(A, axis=0)
            v.append(dS(rng.standard_normal((N, K)), A, Delta))
        v = np.array(v)
        print(f"K={K} N={N} M={M}: mean {v.mean():+.4f} (se {v.std() / np.sqrt(T):.4f}), var {v.var():.5f}, "
              f"formula {predict(N, K, M):.5f}, ratio {v.var() / predict(N, K, M):.3f}")
        assert abs(v.mean()) < 4 * v.std() / np.sqrt(T) and abs(v.var() / predict(N, K, M) - 1) < 0.25
    print(f"all checks passed; eta={ETA:.5f} VarG1={VG1:.5f} kappa2={KAPPA2:.5f}")


if __name__ == "__main__":
    main()
