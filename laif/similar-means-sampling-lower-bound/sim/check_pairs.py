"""Moment-matching pairs for the similar-means lower bound, in exact rational arithmetic.

For even r, take r + 1 rational nodes y_0 > ... > y_r near c + s cos(k pi / r). The divided-difference
weights w_k = 1 / prod_{j != k} (y_k - y_j) alternate in sign and annihilate every polynomial of degree
< r. mu_1 = positive part (even k, contains both outer nodes), mu_0 = negative part (odd k, interior).
Checked: total masses equal, moments 1..r-1 equal, mu_0 inside an interval of length gamma, and
eps_1 = min over intervals J of length gamma of E_{mu_1} dist(p, J), computed exactly.
Also checks the two polynomial inequalities used in the proof on random polynomials.
"""
from fractions import Fraction as Fr
from math import cos, pi
import random

def pair(r, s, den=10**6, c=Fr(1, 2)):
    ys = [c + Fr(round(s * cos(k * pi / r) * den), den) for k in range(r + 1)]
    w = []
    for k, y in enumerate(ys):
        prod = Fr(1)
        for j, z in enumerate(ys):
            if j != k: prod *= (y - z)
        w.append(1 / prod)
    pos = {y: wk for y, wk in zip(ys, w) if wk > 0}; neg = {y: -wk for y, wk in zip(ys, w) if wk < 0}
    P, N = sum(pos.values()), sum(neg.values())
    assert P == N, "total masses differ"
    mu1 = {y: v / P for y, v in pos.items()}; mu0 = {y: v / N for y, v in neg.items()}
    for j in range(1, r):
        assert sum(v * y ** j for y, v in mu1.items()) == sum(v * y ** j for y, v in mu0.items())
    assert ys[0] in mu1 and ys[-1] in mu1 and min(ys[1:-1]) >= 0 and max(ys) <= 1 and min(ys) >= 0
    lo, hi = min(mu0), max(mu0); gamma = hi - lo
    assert max(ys[1:-1]) <= hi and min(ys[1:-1]) >= lo      # all interior nodes inside J_0
    def E(a): return sum(v * (max(a - y, 0) + max(y - a - gamma, 0)) for y, v in mu1.items())
    cands = [y for y in mu1] + [y - gamma for y in mu1]        # E(a) is piecewise linear in a
    eps1 = min(E(a) for a in cands)
    return gamma, eps1, mu1[ys[0]] + mu1[ys[-1]]

print(" r      gamma       eps_1     outer mass   eps_1*r^3/gamma")
for s in (Fr(1, 2) - Fr(1, 1000), Fr(1, 10)):
    for r in (4, 6, 8, 12, 16, 24):
        g, e, om = pair(r, float(s))
        assert e > 0
        print(f"{r:2d}  {float(g):.6f}  {float(e):.3e}  {float(om):.5f}     {float(e) * r ** 3 / float(g):.3f}")
print("moment-matching pairs checked (exact rational arithmetic)")

# The two classical inequalities of the proof, on random polynomials:
# (a) |g| <= 1 on the grid {0, L/K, ..., L} and D^2 <= K/2 imply |g| <= 2 on [0, L];
# (b) V. A. Markov: |g| <= B on [0, L] implies |g^(d)(0)| / d! <= B (2 D^2 / L)^d / (d! (2d-1)!!).
import numpy as np
from numpy.polynomial import polynomial as Pl
rng = np.random.default_rng(1)
for trial in range(300):
    D = int(rng.integers(1, 7)); K = 2 * D * D + int(rng.integers(0, 20)); L = 1.0
    coef = rng.normal(size=D + 1)
    grid = np.linspace(0, L, K + 1); fine = np.linspace(0, L, 20001)
    g = Pl.polyval(grid, coef); scale = np.abs(g).max(); coef = coef / scale
    B = np.abs(Pl.polyval(fine, coef)).max()
    assert B <= 2 + 1e-9, (D, K, B)
    for d in range(1, D + 1):
        hd = abs(coef[d])                                       # = |g^(d)(0)| / d!
        df = 1.0
        for j in range(1, 2 * d, 2): df *= j
        fact = 1.0
        for j in range(2, d + 1): fact *= j
        assert hd <= B * (2 * D * D / L) ** d / (fact * df) * (1 + 1e-9)
print("grid and Markov inequalities checked on 300 random polynomials")
