"""Checks of the SIGReg slice function and the stiffness bound (exact integral and the two quadratures in use).

D(s) = int_R (e^{-s t^2/2} - e^{-t^2/2})^2 e^{-t^2/2} dt: population value of the SIGReg slice statistic for one slice N(0, s).
B(s) = int_R (1 - e^{-s t^2}) e^{-t^2/2} dt: null bias of the plug-in statistic (E[N EP] = N D + B).
"""
import numpy as np
from scipy.integrate import quad

r2p = np.sqrt(2 * np.pi)
D = lambda s: r2p * ((2 * s + 1) ** -0.5 - 2 * (s + 2) ** -0.5 + 3 ** -0.5)
D1 = lambda s: r2p * (-(2 * s + 1) ** -1.5 + (s + 2) ** -1.5)
D2 = lambda s: r2p * (3 * (2 * s + 1) ** -2.5 - 1.5 * (s + 2) ** -2.5)
B = lambda s: r2p * (1 - (2 * s + 1) ** -0.5)
B2 = lambda s: -3 * r2p * (2 * s + 1) ** -2.5
L = D2(0.0)                              # sup of D'' on [0, inf), attained at s = 0

if __name__ == "__main__":
    # closed forms against numerical integrals
    for s in [0, 0.3, 1, 2.5, 10]:
        num = quad(lambda t: (np.exp(-s * t * t / 2) - np.exp(-t * t / 2)) ** 2 * np.exp(-t * t / 2), -np.inf, np.inf)[0]
        assert abs(num - D(s)) < 1e-10, (s, num, D(s))
        numB = quad(lambda t: (1 - np.exp(-s * t * t)) * np.exp(-t * t / 2), -np.inf, np.inf)[0]
        assert abs(numB - B(s)) < 1e-10
        h = 1e-5
        assert abs((D(s + h) - D(s - h)) / (2 * h) - D1(s)) < 1e-6 if s > 0 else True
        assert abs((D1(s + h) - D1(s - h)) / (2 * h) - D2(s)) < 1e-5 if s > 0 else True
    assert abs(D(1)) < 1e-15 and abs(D1(1)) < 1e-15
    D2_1 = 1.5 * r2p * 3 ** -2.5
    assert abs(D2(1) - D2_1) < 1e-14 and abs(B2(1) + 2 * D2_1) < 1e-14       # B''(1) = -2 D''(1)
    s_star = (2 - 2 ** -0.4) / (2 * 2 ** -0.4 - 1)                              # D'' > 0 exactly on [0, s*)
    assert abs(D2(s_star)) < 1e-12 and D2(s_star - 1e-3) > 0 > D2(s_star + 1e-3)
    g = np.linspace(0, 200, 2_000_001)
    L = D2(0.0)
    assert np.all(D2(g) <= L + 1e-12) and np.all(np.diff(D2(g[g < s_star])) < 0)   # sup D'' = D''(0)
    assert -D2(g).min() < 0.02                                                       # D'' >= -0.02 everywhere
    print(f"D''(1) = {D2_1:.6f}, s* = {s_star:.4f}, L = sup D'' = D''(0) = {L:.4f}, min D'' = {D2(g).min():.5f}, D(0) = {D(0):.6f}")

    # quadrature versions: paper [-5,5] 17 points, package [0,3] 17 points doubled
    def quad_D(tmax, n, sym):
        t = np.linspace(-tmax, tmax, n) if sym else np.linspace(0, tmax, n)
        w = np.full(n, t[1] - t[0]); w[[0, -1]] /= 2
        if not sym: w = 2 * w; w[0] /= 2       # package: doubled weights, single weight at t=0
        w = w * np.exp(-t * t / 2)
        f = lambda s: np.sum(w * (np.exp(-s * t * t / 2) - np.exp(-t * t / 2)) ** 2)
        f2 = lambda s: np.sum(w * (t ** 4 / 2) * (2 * np.exp(-s * t * t) - np.exp(-(s + 1) * t * t / 2)))
        return f, f2
    for name, (tmax, n, sym) in {"paper [-5,5]x17": (5, 17, True), "package [0,3]x17": (3, 17, False)}.items():
        f, f2 = quad_D(tmax, n, sym)
        h = 1e-4
        assert abs((f(1 + h) - 2 * f(1) + f(1 - h)) / h ** 2 - f2(1)) < 1e-4
        Lq = max(f2(s) for s in np.linspace(0, 50, 50001))
        print(f"{name}: D_q''(1) = {f2(1):.5f}, sup D_q'' = {Lq:.4f}, D_q(0) = {f(0):.5f}")
        assert Lq <= L + 1e-9

    # stiffness theorem: D(m) - c v/(K+2) <= E_a D(a^T Lam a) <= D(m) + L v/(K+2), and the convex-range lower bound
    rng = np.random.default_rng(1)
    for trial in range(300):
        K = int(rng.choice([4, 16, 64, 256]))
        lam = rng.exponential(1.0, K) * rng.choice([0.3, 1, 2])
        if trial % 3 == 0: lam[rng.random(K) < 0.5] = 0
        m, v = lam.mean(), lam.var()
        a = rng.standard_normal((40000, K)); a /= np.linalg.norm(a, axis=1, keepdims=True)
        X = (a * a) @ lam
        S = D(X).mean()
        se = D(X).std() / np.sqrt(len(X))
        assert v < 1e-12 or abs(X.var() / (2 * v / (K + 2)) - 1) < 0.06
        assert S <= D(m) + L * v / (K + 2) + 4 * se
        assert S >= D(m) - 0.02 * v / (K + 2) - 4 * se          # since D'' >= -0.02
        if lam.max() < s_star:
            assert S >= D(m) + D2(lam.max()) * v / (K + 2) - 4 * se
    print("stiffness bounds hold on 300 random spectra")
