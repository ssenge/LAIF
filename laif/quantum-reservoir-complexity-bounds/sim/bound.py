"""Theorem 1 against [1, Corollary 11] for the partial-trace reservoir with linear readout.

Constants of [1]: dim Theta = n(n-1)+1, L_Theta = 2^{n+1} n (4n-3) (Lemma 15), L'_Theta = L_Theta/(1-r),
D_Theta = sqrt(n(n-1) dJ^2 + dg^2), slope bound of the readout n 2^{n/2}, L_Omega = sqrt(n+1), D_Omega = sqrt(n + 4 C^2).
Asserts: the integral identity int_0^1 log(1 + c/u) du = log(1+c) + c log(1+1/c) <= log(1+c) + 1 (quadrature),
Theorem 1 below [1, Corollary 11] for n = 2..30, and Theorem 1 / ((C+n) n sqrt(n)) bounded.
Exact arithmetic in logs, since the bound of [1] overflows floats for large n.
"""
import math
from scipy.integrate import quad

for c in [1e-3, 0.5, 3.0, 1e3, 1e8]:
    val = quad(lambda u: math.log(1 + c / u), 0, 1, limit=200)[0]
    assert abs(val - (math.log(1 + c) + c * math.log(1 + 1 / c))) < 1e-6 * max(1, val)
    assert val <= math.log(1 + c) + 1
    root = quad(lambda u: math.sqrt(math.log(1 + c / u)), 0, 1, limit=200)[0]
    assert root <= math.sqrt(val) + 1e-9

k, r, dJ, dg, C = 1, 0.9, 1.0, 1.0, 1.0             # k = 1: both bounds scale as 1/sqrt(k)
ratios = []
for n in range(2, 31):
    dT, dO = n * (n - 1) + 1, n + 1
    lnLp = (n + 1) * math.log(2) + math.log(n * (4 * n - 3)) - math.log(1 - r)
    lnA1 = math.log(n) + n / 2 * math.log(2) + lnLp + 0.5 * math.log(n * (n - 1) * dJ ** 2 + dg ** 2)
    lnA2 = 0.5 * math.log(n + 1) + 0.5 * math.log(n + 4 * C ** 2)
    lnA = max(lnA1, lnA2)
    ln_old = math.log(48 * 0.89 * (math.sqrt(dT) + math.sqrt(dO))) + lnA
    B, d = C + n, dT + dO
    lterm = math.log(2) + lnA - math.log(B)          # ln(2A/B); ln(1 + x) computed stably from ln x
    L = 1 + (lterm + math.log1p(math.exp(-lterm)) if lterm > 0 else math.log1p(math.exp(lterm)))
    new = 24 * B * math.sqrt(d * L / k)
    assert math.log(new) < ln_old
    ratios.append(new / ((C + n) * n * math.sqrt(n)))
    if n in (2, 5, 10, 20, 30):
        print(f"n = {n:2d}: [1, Cor. 11] = e^{ln_old:6.1f} = 10^{ln_old / math.log(10):5.1f},  Theorem 1 = {new:9.1f}")
assert max(ratios) < 2 * min(ratios) * 10
print(f"Theorem 1 / ((C + n) n^1.5) in [{min(ratios):.1f}, {max(ratios):.1f}]")
print("all checks passed")
