"""Exponent of nested quantum minimum finding over recurrence (4.3) of reference [1] (SIAM J. Discrete Math. 33(1),
2019, Lemma 4.5), at constant depth D.

Recurrence (4.3), for an even constant c >= 4 and alpha = 2^(-c/2): for more than c terminals,
  g(S, P_S, T) = min over (T1, T2) with |T1|, |T2| <= (1/2 + alpha)|T|, S' superset of S with |S' - S| <= c, and
                 partitions P1, P2 of S' with P_S refining P1 join P2, of g(S', P1, T1) + g(S', P2, T2).
A call with m terminals searches its at most 2^m (n+1)^c Bell(cD)^2 choices by quantum minimum finding and evaluates
both children, each with at most floor((1/2 + alpha) m) terminals. After D levels, or at m <= c, the value is computed by
the classical polynomial-space algorithm of [1, Theorem 4.2] in 7.97^m n^O(1) log(nW) time, run reversibly in time
T^(1 + eps).

Exponent of k in log2 of the time (all other factors are poly(k, n) or constants for fixed delta):
  e(D, c, eps) = (1 - q^D) / (1 - 2 alpha) + (1 + eps) log2(7.97) q^D,   q = 1/2 + alpha.
Proof: m_l <= q^l k, the sum of m_l / 2 over the D search levels is at most k (1 - q^D) / (2 (1 - q)), and the leaf has
m_D <= q^D k. Checked: e <= 1 + delta/2 exactly (fractions, log2 7.97 rounded up), and the bound m_l <= q^l k on the
integer recursion for k up to 10^6. """
from fractions import Fraction as F
from math import floor, log2

LOG797_UP = F(2995, 1000)                          # log2(7.97) = 2.99456... rounded up
assert log2(7.97) < float(LOG797_UP)

def e(D, c, eps):
    q = F(1, 2) + F(1, 2 ** (c // 2))
    return (1 - q ** D) / (2 * (1 - q)) + (1 + eps) * LOG797_UP * q ** D

ROWS = [(F(1, 2), 12, F(1, 10)), (F(1, 4), 16, F(1, 10)), (F(1, 10), 20, F(1, 10)), (F(1, 20), 24, F(1, 20))]
for delta, c, eps in ROWS:
    D = next(d for d in range(1, 60) if e(d, c, eps) <= 1 + delta / 2)   # smallest depth that works
    ex = e(D, c, eps); q = F(1, 2) + F(1, 2 ** (c // 2))
    assert ex <= 1 + delta / 2
    for k in list(range(1, 3000)) + list(range(3000, 10 ** 6, 997)):
        m, path = k, [k]
        for _ in range(D):
            if m <= c:
                break
            m = floor(q * m); path.append(m)
        assert all(ml <= q ** l * k for l, ml in enumerate(path)), k
        if len(path) == D + 1:                      # full depth: the closed form bounds the whole exponent
            assert sum(F(x, 2) for x in path[:-1]) + (1 + eps) * LOG797_UP * path[-1] <= ex * k
    print(f"delta={float(delta):5.3f}  c={c:2d}  alpha=2^-{c // 2}  D={D:2d}  eps={float(eps)}  k-exponent {float(ex):.4f}"
          f" <= {float(1 + delta / 2):.3f}   n-exponent from the searches over S': (c/2) D = {c * D // 2}")
print("all checks passed")
