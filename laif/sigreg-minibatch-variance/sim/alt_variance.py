"""Variance of minibatch SIGReg near the null: z ~ N(0, I + Delta), tr Delta = 0, fresh uniform directions per batch.

Quadrature form with knots t_l and weights w_l (the weight e^{-t^2/2} included), g_l = e^{-t_l^2/2}. For a slice with
law N(0, s): E T = N D(s) + B(s), D(s) = sum_l w_l (e^{-s t_l^2/2} - g_l)^2, B(s) = sum_l w_l (1 - e^{-s t_l^2}).
Slice m has s_m = 1 + delta_m, delta_m = a_m^T Delta a_m. Prediction, to leading order in Delta:
  Var S = Var_A[(1/M) sum_m (N D(s_m) + B(s_m))]                                  (directions move the mean)
        + E_A[(1/M^2) sum_{m,m'} F(r_mm')]                                       (null part, Proposition 5)
        + 4 N E_A[(1/M^2) sum_{m,m'} delta_m delta_m' Cov(G1(X), G1(X'))]          (first projection, linear in N)
with G1(x) = -(1/2) sum_l w_l t_l^2 g_l (cos t_l x - g_l), the s-derivative of E_Y H(x, Y) at s = 1, and
Cov(G1(X), G1(X')) = (1/4) sum_{l,m} w_l w_m t_l^2 t_m^2 g_l^2 g_m^2 (cosh(t_l t_m r) - 1) for correlation r.
The first term is about (N^2 D''(1)^2 / (4M)) Var(delta^2), a relative spread sqrt(Var(delta^2)) / E delta^2 / sqrt(M)
of the signal that does not shrink with N, with
  Var(delta^2) / (E delta^2)^2 = 3 (1 + 4 tr Delta^4 / (tr Delta^2)^2) K (K + 2) / ((K + 4)(K + 6)) - 1.
"""
import numpy as np


def quadrature():  # official package form: 17 knots on [0, 3], trapezoid, doubled
    t = np.linspace(0, 3, 17); w = np.full(17, 2 * (t[1] - t[0])); w[[0, -1]] /= 2
    return t, w * np.exp(-t**2 / 2)


T_, W_ = quadrature(); G2 = np.exp(-T_**2); WW = np.outer(W_ * G2, W_ * G2); TT = np.outer(T_, T_)
Dfun = lambda s: (W_ * (np.exp(-np.multiply.outer(s, T_**2) / 2) - np.exp(-T_**2 / 2)) ** 2).sum(-1)
Bfun = lambda s: (W_ * (1 - np.exp(-np.multiply.outer(s, T_**2)))).sum(-1)
C = lambda r: (WW * ((np.cosh(TT * r[..., None, None]) - 1) ** 2 + np.sinh(TT * r[..., None, None]) ** 2)).sum((-1, -2))
V = lambda r: 4 * (WW * (np.cosh(TT * r[..., None, None]) - 1)).sum((-1, -2))
CG = lambda r: 0.25 * (WW * TT**2 * (np.cosh(TT * r[..., None, None]) - 1)).sum((-1, -2))
D2 = (W_ * T_**4 * G2).sum() / 2


def stat(x):
    """T for each column of x (N x M)."""
    N = x.shape[0]; xt = x[..., None] * T_
    return N * (((np.cos(xt).mean(0) - np.exp(-T_**2 / 2)) ** 2 + np.sin(xt).mean(0) ** 2) @ W_)


def predict(N, K, M, Delta, rng, R=4000):
    tot = np.zeros(3); means = []
    for _ in range(R):
        A = rng.standard_normal((K, M)); A /= np.linalg.norm(A, axis=0)
        r = np.clip(A.T @ A, -1, 1); d = np.einsum("km,kl,lm->m", A, Delta, A)
        means.append((N * Dfun(1 + d) + Bfun(1 + d)).mean())
        F = 2 * (1 - 1 / N) * C(r) + V(r) / N
        tot += [0, F.mean(), 4 * N * (np.outer(d, d) * CG(r)).mean()]
    tot /= R; tot[0] = np.var(means)
    return tot


def main():
    rng = np.random.default_rng(6)
    # G1 against a finite difference of E_Y H(x, Y) in s, at a few x
    x = np.array([0.0, 0.7, 1.9]); h = 1e-5
    EH = lambda s: (W_ * (np.cos(np.outer(x, T_)) * np.exp(-s * T_**2 / 2) - np.exp(-T_**2 / 2) * np.cos(np.outer(x, T_))
                          - np.exp(-T_**2 / 2) * np.exp(-s * T_**2 / 2) + G2)).sum(-1)
    g1 = -0.5 * (W_ * T_**2 * np.exp(-T_**2 / 2) * (np.cos(np.outer(x, T_)) - np.exp(-T_**2 / 2))).sum(-1)
    assert np.allclose((EH(1 + h) - EH(1 - h)) / (2 * h), g1, atol=1e-8)
    K = 16
    lam = np.array([0.3, -0.3] * (K // 2)); Delta = np.diag(lam)
    for M in (4, 16):
        for N in (64, 256, 1024):
            Bn = 3000
            S = np.empty(Bn); L = np.linalg.cholesky(np.eye(K) + Delta)
            for b in range(Bn):
                A = rng.standard_normal((K, M)); A /= np.linalg.norm(A, axis=0)
                z = rng.standard_normal((N, K)) @ L.T
                S[b] = stat(z @ A).mean()
            p = predict(N, K, M, Delta, rng, R=1500)
            print(f"K={K} M={M} N={N}: Var S {S.var():.4f}; predicted {p.sum():.4f} = directions {p[0]:.4f} "
                  f"+ null {p[1]:.4f} + linear {p[2]:.4f}; ratio {S.var() / p.sum():.3f}")
            assert abs(S.var() / p.sum() - 1) < 0.12
    # relative spread of the signal from the directions: sqrt(Var delta^2) / E delta^2 -> sqrt(2) for a spread spectrum
    d = np.einsum("km,kl,lm->m", *(lambda A: (A, Delta, A))(
        (lambda A: A / np.linalg.norm(A, axis=0))(rng.standard_normal((K, 200000)))))
    q = (lam**4).sum() / (lam**2).sum() ** 2
    rho = np.sqrt(3 * (1 + 4 * q) * K * (K + 2) / ((K + 4) * (K + 6)) - 1)
    print(f"spread of delta^2: {np.std(d**2) / np.mean(d**2):.3f}, closed form {rho:.3f}")
    assert abs(np.std(d**2) / np.mean(d**2) / rho - 1) < 0.01
    assert abs(np.mean(d**2) / (2 * (lam**2).sum() / (K * (K + 2))) - 1) < 0.01
    print(f"D''(1) = {D2:.5f}; all checks passed")


if __name__ == "__main__":
    main()
