"""Lemma 2 bounds, exactly: X ~ Hypergeometric(T items, h marked, R drawn), x = hR/T.
(i)  Pr[X >= 2] >= x^2/16 for h >= 2, 2 <= R, x <= 1/8;
(ii) E[C(X_a,2) C(X_b,2)] <= x^4/4 for two disjoint marked groups of size h each (multivariate hypergeometric)."""
from math import comb
def pmf(T, h, R, s): return comb(h, s) * comb(T - h, R - s) / comb(T, R)
cnt = 0
for T in range(16, 400, 7):
    for h in range(2, 12):
        for R in range(2, T):
            x = h * R / T
            if x > 1 / 8 or 2 * h > T: continue
            p2 = 1 - pmf(T, h, R, 0) - pmf(T, h, R, 1)
            assert p2 >= x * x / 16, (T, h, R)
            # E[C(Xa,2)C(Xb,2)] = C(h,2)^2 * R(R-1)(R-2)(R-3) / (T(T-1)(T-2)(T-3))
            if R >= 4:
                m = comb(h, 2) ** 2 * R * (R - 1) * (R - 2) * (R - 3) / (T * (T - 1) * (T - 2) * (T - 3))
                assert m <= x ** 4 / 4
            cnt += 1
print("cases", cnt); assert cnt > 1000
