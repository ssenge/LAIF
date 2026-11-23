"""Null moments of minibatch SIGReg for any weight/quadrature in t, and the exact average over random directions.

For knots t_l with weights w_l (the weight e^{-t^2/2} included), the statistic of one slice is
  T = N sum_l w_l |phi_N(t_l) - g(t_l)|^2,  g(t) = e^{-t^2/2},
a V-statistic with the kernel H(x, y) = sum_l w_l [(cos t_l x - g_l)(cos t_l y - g_l) + sin t_l x sin t_l y],
which is degenerate under N(0, 1). With (X, X') standard normal with correlation r,
  E cos(aX) cos(bX') = g(a) g(b) cosh(abr),  E sin(aX) sin(bX') = g(a) g(b) sinh(abr),
so, for two slices with directions a, a' and r = a^T a':
  E T = sum_l w_l (1 - g_l^2)                                   (every slice, every N)
  Cov[T(a), T(a')] = F(r) = 2 (1 - 1/N) C(r) + V(r) / N,
  C(r) = sum_{l,m} w_l w_m g_l^2 g_m^2 [(cosh(t_l t_m r) - 1)^2 + sinh(t_l t_m r)^2],
  V(r) = 4 sum_{l,m} w_l w_m g_l^2 g_m^2 (cosh(t_l t_m r) - 1).
To order r^2, F(r) = 2 S2^2 r^2 for every N, with S2 = sum_l w_l t_l^2 g_l^2 (the exact integral gives 2 S2^2 = 4 pi/27).
For M fresh uniform directions, Var S = F(1)/M + (1 - 1/M) E F(r) exactly, r^2 ~ Beta(1/2, (K-1)/2), and
E F(r) = 2 S2^2 / K + O(1/K^2).
"""
import numpy as np
from scipy.integrate import quad
from scipy.special import gammaln


def quadrature(kind):
    if kind == "exact":      # fine grid on the line, stands in for the integral
        t = np.linspace(-14, 14, 4001); w = np.full(t.size, t[1] - t[0]); w[[0, -1]] /= 2
    elif kind == "paper":    # 17 points on [-5, 5], trapezoid
        t = np.linspace(-5, 5, 17); w = np.full(17, t[1] - t[0]); w[[0, -1]] /= 2
    elif kind == "package":  # 17 points on [0, 3], trapezoid, doubled (t = 0 carries no error term)
        t = np.linspace(0, 3, 17); w = np.full(17, 2 * (t[1] - t[0])); w[[0, -1]] /= 2
    return t, w * np.exp(-t**2 / 2)


def moments(t, w):
    g2 = np.exp(-t**2)
    ww = np.outer(w * g2, w * g2); tt = np.outer(t, t)
    C = lambda r: (ww * ((np.cosh(tt * r) - 1) ** 2 + np.sinh(tt * r) ** 2)).sum()
    V = lambda r: 4 * (ww * (np.cosh(tt * r) - 1)).sum()
    return (w * (1 - g2)).sum(), C, V, (w * t**2 * g2).sum()


def stat(x, t, w):
    """T for each column of x (N x M)."""
    N = x.shape[0]; xt = x[..., None] * t
    return N * (((np.cos(xt).mean(0) - np.exp(-t**2 / 2)) ** 2 + np.sin(xt).mean(0) ** 2) @ w)


def mean_over_directions(f, K):
    """E f(r) for r = a^T a', a, a' independent uniform on the sphere S^{K-1}."""
    logc = gammaln(K / 2) - gammaln(0.5) - gammaln((K - 1) / 2)
    return quad(lambda r: f(r) * np.exp(logc + (K - 3) / 2 * np.log1p(-r * r)), -1, 1, limit=200)[0]


def main():
    SQ2PI = np.sqrt(2 * np.pi)
    E, C, V, S2 = moments(*quadrature("exact"))
    assert abs(E - SQ2PI * (1 - 3**-0.5)) < 1e-9
    assert abs(C(1) - 2 * np.pi * (5**-0.5 - 2**-0.5 + 1 / 3)) < 1e-9
    assert abs(V(1) - 4 * np.pi * (2**-0.5 - 2 / 3)) < 1e-9
    assert abs(2 * S2**2 - 4 * np.pi / 27) < 1e-9
    r = 0.37  # closed forms of the exact integral at an interior r
    assert abs(C(r) - 2 * np.pi * ((9 - 4 * r**2) ** -0.5 - np.sqrt(2) * (4.5 - r**2 / 2) ** -0.5 + 1 / 3)) < 1e-9
    assert abs(V(r) - 4 * np.pi * ((2.25 - r**2 / 4) ** -0.5 - 2 / 3)) < 1e-9
    rng = np.random.default_rng(5)
    for kind in ("paper", "package"):
        t, w = quadrature(kind)
        E, C, V, S2 = moments(t, w)
        # r^2 coefficient: F(r) / r^2 -> 2 S2^2 for every N
        for N in (2, 64, 4096):
            F = lambda r: 2 * (1 - 1 / N) * C(r) + V(r) / N
            assert abs(F(1e-3) / 1e-6 - 2 * S2**2) < 1e-4 * 2 * S2**2
        print(f"{kind}: E T = {E:.5f}, C(1) = {C(1):.5f}, V(1) = {V(1):.5f}, 2 S2^2 = {2 * S2**2:.5f} "
              f"(exact integral: 1.05935, 0.46144, 0.50819, {4 * np.pi / 27:.5f})")
        # random sampling: one slice, and two slices of one batch with correlation r
        N, T, r = 32, 40000, 0.6
        X = rng.standard_normal((N, T)); Y = r * X + np.sqrt(1 - r * r) * rng.standard_normal((N, T))
        s1, s2 = stat(X, t, w), stat(Y, t, w)
        F = lambda r: 2 * (1 - 1 / N) * C(r) + V(r) / N
        se_m = s1.std() / np.sqrt(T)
        print(f"  N={N}: mean {s1.mean():.4f} vs {E:.4f}; var {s1.var():.4f} vs F(1) {F(1):.4f}; "
              f"cov(r={r}) {np.cov(s1, s2)[0, 1]:.4f} vs F(r) {F(r):.4f}")
        assert abs(s1.mean() - E) < 4 * se_m
        assert abs(s1.var() / F(1) - 1) < 0.06 and abs(np.cov(s1, s2)[0, 1] / F(r) - 1) < 0.1
        # exact average over directions against the 1/K term
        for K in (16, 128, 1024):
            ef = mean_over_directions(F, K)
            print(f"  K={K}: E F(r) = {ef:.6f}, 2 S2^2 / K = {2 * S2**2 / K:.6f}, ratio {ef / (2 * S2**2 / K):.4f}")
            assert abs(ef / (2 * S2**2 / K) - 1) < 12 / K
        # Var S over fresh directions, against the exact formula
        K, M, T = 16, 8, 6000
        S = []
        for _ in range(T):
            A = rng.standard_normal((K, M)); A /= np.linalg.norm(A, axis=0)
            S.append(stat(rng.standard_normal((N, K)) @ A, t, w).mean())
        vs = F(1) / M + (1 - 1 / M) * mean_over_directions(F, K)
        print(f"  K={K}, M={M}: Var S {np.var(S):.5f} vs exact {vs:.5f}")
        assert abs(np.var(S) / vs - 1) < 0.08
    print("all checks passed")


if __name__ == "__main__":
    main()
