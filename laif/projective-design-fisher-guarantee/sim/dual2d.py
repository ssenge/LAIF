"""Dual LP in the reduced variables (z, u = x^2): maximise E_Haar q subject to u - (1+z) q(z,u) >= 0 on
0 <= u <= 1 - z^2, with q in span{z^k, u z^j, u^2} up to total degree t (degree of u counts 2)."""
import sys, numpy as np
from scipy.optimize import linprog
from math import gamma

def mom(a, c):   # E[x^(2a) z^c] on S^2
    return 2 * gamma(a + 0.5) * gamma(0.5) * gamma((c + 1) / 2) / gamma((2 * a + c + 3) / 2) / (4 * np.pi) if c % 2 == 0 else 0.0

def basis(t):
    return [(a, c) for a in range(t // 2 + 1) for c in range(t + 1) if 2 * a + c <= t]

def solve(t, M):
    B = basis(t)
    zs = np.cos(np.linspace(0, np.pi, M))
    Z, S = np.meshgrid(zs, np.linspace(0, 1, M)); Z = Z.ravel(); U = (S.ravel()) * (1 - Z ** 2)
    A = np.array([[(1 + z) * u ** a * z ** c for (a, c) in B] for z, u in zip(Z, U)])
    m = np.array([mom(a, c) for a, c in B])
    # maximise m.coef s.t. A coef <= U
    res = linprog(-m, A_ub=A, b_ub=U, bounds=(None, None), method="highs")
    coef = res.x
    slack = U - A @ coef
    tight = np.argsort(slack)[:40]
    return -res.fun, B, coef, Z[tight], U[tight], slack[tight]

if __name__ == "__main__":
    t, M = int(sys.argv[1]), int(sys.argv[2])
    v, B, coef, zt, ut, sl = solve(t, M)
    print("check Haar moment E[x^2] =", mom(1, 0), "(1/3)")
    print(f"t={t}: dual value {v:.8f}")
    print(dict(zip(B, np.round(coef, 6))))
    for z, u, s in sorted(zip(zt, ut, sl))[:40]:
        print(f"  z={z: .5f} u={u:.5f} u/(1-z^2)={u / max(1 - z * z, 1e-12):.4f} slack={s:.2e}")
