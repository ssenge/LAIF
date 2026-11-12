"""d -> infinity limit of the radius-1 rule z_u = [g_u > lam T_u], T_u = d^{-1/2} sum_{w ~ u} g_w, for LocalMaxCut.

Fix v with z_v = +1, that is g_v > lam T_v. Given (g_v, T_v), a neighbour u disagrees with probability
1/2 + (lam g_v - T_v) c / sqrt(d) + o(1/sqrt d), c = 1/sqrt(2 pi (1 + lam^2)), and the disagreement indicators have
conditional variance 1/4 - c^2 each (conditioning on T_v removes their linear part in g_u). So the count of
disagreeing neighbours is d/2 + sqrt(d) (c (lam g_v - T_v) + s N) with s^2 = 1/4 - c^2, and
  value(lam) = 2 P(Z s + c (lam g - T) >= 0, g > lam T) = 1/2 + arcsin(rho)/pi,
  rho^2 = 8 x / ((1 + x) ((pi + 2) x + pi)), x = lam^2,
maximized at x = sqrt(pi / (pi + 2)), where rho^2 = 8 / ((pi + 2) (1 + x)^2)."""
import numpy as np
from scipy.stats import norm
def value(lam):
    x = lam * lam; rho = np.sqrt(8 * x / ((1 + x) * ((np.pi + 2) * x + np.pi))); return 0.5 + np.arcsin(rho) / np.pi
def value_mc(lam, n=4_000_000, seed=1):
    rng = np.random.default_rng(seed); g, T = rng.standard_normal(n), rng.standard_normal(n)
    c = 1 / np.sqrt(2 * np.pi * (1 + lam * lam)); s = np.sqrt(0.25 - c * c)
    return 2 * np.mean(norm.cdf(c * (lam * g - T) / s) * (g > lam * T))
LAM = (np.pi / (np.pi + 2)) ** 0.25
BEST = 0.5 + np.arcsin(np.sqrt(8 / ((np.pi + 2) * (1 + np.sqrt(np.pi / (np.pi + 2))) ** 2))) / np.pi
if __name__ == "__main__":
    for lam in [0.6, 0.88, 1.0, 1.3]:
        a, b = value(lam), value_mc(lam); print(lam, a, b); assert abs(a - b) < 1e-3
    grid = np.linspace(0.3, 2, 20001); assert abs(grid[np.argmax(value(grid))] - LAM) < 1e-3
    assert abs(value(LAM) - BEST) < 1e-15
    print("best lam", LAM, "limit", BEST)
