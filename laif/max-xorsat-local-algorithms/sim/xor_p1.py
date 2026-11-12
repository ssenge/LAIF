"""Radius 1 in the infinite-degree limit, exactly: m_0 = s, field phi = z normal, output sign(z + lam s).
nu(lam) = sqrt(q/2) E[z sign] E[s sign]^(q-1) = sqrt(q/2) sqrt(2/pi) exp(-lam^2/2) erf(lam/sqrt2)^(q-1). usage: xor_p1.py"""
import numpy as np
from scipy.special import erf
from scipy.optimize import minimize_scalar

nu = lambda q, l: np.sqrt(q / 2) * np.sqrt(2 / np.pi) * np.exp(-l * l / 2) * erf(l / np.sqrt(2)) ** (q - 1)
for q in range(2, 7):
    r = minimize_scalar(lambda l: -nu(q, l), bounds=(0, 5), method="bounded", options={"xatol": 1e-10})
    print(q, round(r.x, 4), round(-r.fun, 5))
rng = np.random.default_rng(0); z, s = rng.standard_normal(10 ** 6), rng.choice([-1.0, 1.0], 10 ** 6); o = np.sign(z + 1.1 * s)
assert abs(np.sqrt(1.5) * (z * o).mean() * (s * o).mean() ** 2 - nu(3, 1.1)) < 3e-3   # sampling check of the formula
