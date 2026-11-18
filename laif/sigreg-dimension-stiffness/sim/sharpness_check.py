"""Sharpness of the gap constant of Theorem 2 for h = D, K = 2.

Directions a = (cos u, sin u) with u uniform, X = lam1 cos^2 u + lam2 sin^2 u. Costs just below mu |D'(0)|/K:
c1 = c (1 - 2t), c2 = c (1 - t). The minimizer is small, and the ratio of the two sides of
c2 - c1 <= 2 L mu (lam1 - lam2) / (K (K+2)), with L = D''(0), tends to 1 as t -> 0.
"""
import numpy as np
from scipy.optimize import minimize
from slice_function import D, D1, L

K, mu = 2, 1.0
u, w = np.polynomial.legendre.leggauss(400)
u = (u + 1) * np.pi / 2; w = w * np.pi / 2 / np.pi          # quadrature nodes for the uniform law on [0, pi]
C2, S2 = np.cos(u) ** 2, np.sin(u) ** 2
c = mu * abs(D1(0.0)) / K

def solve(t):
    c1, c2 = c * (1 - 2 * t), c * (1 - t)
    F = lambda lam: c1 * lam[0] + c2 * lam[1] + mu * (w * D(lam[0] * C2 + lam[1] * S2)).sum()
    G = lambda lam: np.array([c1, c2]) + mu * np.array([(w * D1(lam[0] * C2 + lam[1] * S2) * C2).sum(),
                                                         (w * D1(lam[0] * C2 + lam[1] * S2) * S2).sum()])
    r = minimize(F, [t, t], jac=G, bounds=[(0, None)] * 2, method="L-BFGS-B", options={"ftol": 1e-15, "gtol": 1e-14})
    lam = r.x
    assert lam[1] > 0 and lam[0] >= lam[1], lam            # second direction active, ordering of Theorem 2 (i)
    return (c2 - c1) / (2 * L * mu * (lam[0] - lam[1]) / (K * (K + 2)))

ratios = [solve(t) for t in [1e-1, 3e-2, 1e-2, 3e-3]]
for t, q in zip([1e-1, 3e-2, 1e-2, 3e-3], ratios):
    print(f"t = {t:.0e}: ratio of the two sides = {q:.5f}")
assert all(q <= 1 + 1e-6 for q in ratios)                  # Theorem 2 (ii)
assert ratios[-1] > 0.99                                   # the constant is attained in the limit
print("gap bound holds and its constant is approached")
