"""Number states |n>: the order-a bound fails exactly for 0 < a < a1(n) (concavity of h_n, README).
Prints a1(n) and ln||W_n||_1 - (1/2) ln n against the limit c = ln((2/pi)^{3/2} Gamma(3/4)^2 / Gamma(3/2))."""
import numpy as np
from scipy.special import gammaln, gamma
from scipy.optimize import brentq
from fockl1 import l1
c = np.log((2 / np.pi) ** 1.5 * gamma(0.75) ** 2 / gamma(1.5))
a0 = brentq(lambda a: 0.5 * np.log(2 * np.pi) + np.log(a) / (2 * (1 - a)) - c, 0.05, 0.4)
print(f"c = {c:.6f}, limit threshold a0 = {a0:.6f}")
prev = 1.0
for n in [1, 2, 5, 10, 50, 100, 200, 400, 800, 1600, 3200]:
    L = np.log(l1(n))
    h = lambda a: gammaln(a * n + 1) - a * gammaln(n + 1) - a * n * np.log(a) - (1 - a) * L
    a1 = brentq(h, 1e-3, 0.5); assert h(0.5) > 0 and a1 < prev and a1 > a0; prev = a1
    print(f"n={n:5d}  ln||W_n||_1={L:.5f}  minus (1/2)ln n: {L - 0.5 * np.log(n):+.5f}  a1(n)={a1:.5f}", flush=True)
