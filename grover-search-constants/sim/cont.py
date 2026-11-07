"""Continuum limit (theta -> 0) of theta * E for random-offset geometric rounds, k uniform in [alpha m, m]."""
import numpy as np
from scipy.optimize import minimize_scalar, minimize

def s(y, al):
    if al >= 1: return np.cos(2 * y) ** 2
    return 0.5 + (np.sin(4 * y) - np.sin(4 * al * y)) / (8 * (1 - al) * y)

def C(lam, al, M=400, lo=-40, hi=40):
    U = (np.arange(M) + 0.5) / M
    tot = 0
    for u in U:
        y = lam ** (np.arange(lo, hi) + u) * 1e-9 ** 0      # scale-free: any reference works
        y = y[(y > 1e-6) & (y < 1e4)]
        surv, e = 1.0, 0.0
        for yi in y:
            e += surv * yi * (1 + al) / 2; surv *= s(yi, al)
        tot += e
    return tot / M

if __name__ == "__main__":
    for al in (1.0, 0.95, 0.9, 0.8):
        r = minimize_scalar(lambda l: C(l, al), bounds=(1.2, 1.95), method="bounded", options={"xatol": 1e-3})
        print("alpha %.2f: C = %.5f at lambda %.4f" % (al, r.fun, r.x))
