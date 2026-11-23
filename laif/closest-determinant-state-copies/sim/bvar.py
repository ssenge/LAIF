"""Variance bound b(m) of matchgate shadows for Gaussian density operators, eq. (40) of [2]."""
from fractions import Fraction
from math import comb, factorial, lgamma, exp, log, sqrt
import numpy as np

def mult(n, *ks):
    r = factorial(n)
    for k in ks: r //= factorial(k)
    return r

def b_exact(m):
    s = Fraction(0)
    for l1 in range(m + 1):
        for l2 in range(m + 1 - l1):
            for l3 in range(m + 1 - l1 - l2):
                r = m - l1 - l2 - l3
                a, c = l1 + l3, l2 + l3
                s += Fraction(mult(m, l1, l2, l3, r) ** 2, mult(2 * m, 2 * l1, 2 * l2, 2 * l3, 2 * r)) \
                     * Fraction(comb(2 * m, 2 * a), comb(m, a)) * Fraction(comb(2 * m, 2 * c), comb(m, c))
    return s / 4 ** m

def b_float(m):
    lg = lambda x: np.vectorize(lgamma)(np.asarray(x, float) + 1)
    L = np.arange(m + 1)
    l1, l2, l3 = np.meshgrid(L, L, L, indexing="ij")
    ok = l1 + l2 + l3 <= m
    l1, l2, l3 = l1[ok], l2[ok], l3[ok]
    r = m - l1 - l2 - l3
    G = {k: lgamma(k + 1) for k in range(2 * m + 1)}
    g = np.array([G[k] for k in range(2 * m + 1)])
    lm = lambda n, *ks: g[n] - sum(g[k] for k in ks)
    lb = lambda n, k: g[n] - g[k] - g[n - k]
    a, c = l1 + l3, l2 + l3
    t = 2 * lm(m, l1, l2, l3, r) - lm(2 * m, 2 * l1, 2 * l2, 2 * l3, 2 * r) \
        + lb(2 * m, 2 * a) - lb(m, a) + lb(2 * m, 2 * c) - lb(m, c) - m * log(4)
    mx = t.max()
    return exp(mx) * np.exp(t - mx).sum()

if __name__ == "__main__":
    assert b_exact(1) == 1
    for m in range(1, 13):
        e = b_exact(m)
        assert abs(float(e) - b_float(m)) < 1e-9 * float(e), m
    print("m  b(m)  b/(sqrt(m) ln(m+1))")
    worst = 0
    for m in [1, 2, 3, 4, 5, 8, 16, 32, 64, 128, 256]:
        b = b_float(m)
        q = b / (sqrt(m) * log(m + 1))
        worst = max(worst, q)
        print(m, round(b, 4), round(q, 4))
    print("max ratio", round(worst, 4))
    assert worst <= 1.5
    # monotone and at most 1.5 sqrt(m) ln(m+1) on the computed range
    bs = [b_float(m) for m in range(1, 129)]
    assert all(x <= y + 1e-12 for x, y in zip(bs, bs[1:]))
    assert all(b <= 1.5 * sqrt(m) * log(m + 1) for m, b in zip(range(1, 129), bs))
    print("ok")
