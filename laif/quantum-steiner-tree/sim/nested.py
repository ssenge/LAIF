"""Exponent of nested quantum minimum finding over the balanced split recursion of Minimum Steiner Tree, at constant depth.

Recursion (split theorem, restated as Lemma 3 and Theorem 4 of arXiv:1904.03581), for eta > 0 and m >= 1/eta terminals:
  W_G(K) = min over K1 with |K1| = (1/2 +- eta)|K| and A subset of V with |A| <= s = ceil(log2(1/eta)) of
           W_G(K1 + A) + W_{G/A}(K2 + v_A),     K2 = K - (K1 + A).
The algorithm unrolls D levels. A call with m terminals searches its at most 2^m (n+1)^s choices by quantum minimum
finding and evaluates both children; children have at most r(m) = floor((1/2 + eta) m) + s + 1 terminals. After D levels,
or once m < 1/eta, the value is computed by the classical polynomial-space algorithm in 6.751^m n^O(1) log W time, run
reversibly in time T^(1 + eps) and space O(S log T).

Exponent of k in log2 of the time, from the square roots along one path of calls (all other factors are poly(k, n)):
  e(D, eta, eps) = (1 - (1/2 + eta)^D) / (1 - 2 eta) + (1 + eps) log2(6.751) (1/2 + eta)^D.
Proof of the k-exponent: m_l <= (1/2 + eta)^l k + R with R = (s + 1) / (1/2 - eta), so the sum of m_l / 2 over the D search
levels is at most k (1 - (1/2 + eta)^D) / (1 - 2 eta) + D R / 2, and the leaf has m_D <= (1/2 + eta)^D k + R.
Checked here, for each delta in the table: e <= 1 + delta/2 exactly (fractions), so 2^{(1+delta)k} absorbs the
poly(k) factors; the recursion on integers stays within the bound for k up to 10^6; and the space factor (2L)^D. """
from fractions import Fraction as F
from math import ceil, floor, log2

LOG6751_UP = F(2756, 1000)                         # log2(6.751) = 2.75507... rounded up
assert log2(6.751) < float(LOG6751_UP)

def e(D, eta, eps):
    q = F(1, 2) + eta
    return (1 - q ** D) / (1 - 2 * eta) + (1 + eps) * LOG6751_UP * q ** D

def path(k, D, eta):
    """Terminal counts m_0..m_D along one path, with integer rounding and the additive s + 1."""
    s = ceil(log2(1 / eta)); ms = [k]
    for _ in range(D):
        m = ms[-1]
        if m < 1 / eta:
            break
        ms.append(floor((F(1, 2) + eta) * m) + s + 1)
    return ms, s

ROWS = [(F(1, 2), F(1, 50), F(1, 10)), (F(1, 4), F(1, 100), F(1, 10)), (F(1, 10), F(1, 500), F(1, 10)), (F(1, 20), F(1, 2000), F(1, 10))]
for delta, eta, eps in ROWS:
    D = next(d for d in range(1, 40) if e(d, eta, eps) <= 1 + delta / 2)   # smallest depth that works
    ex = e(D, eta, eps)
    assert ex <= 1 + delta / 2, (delta, float(ex))
    s = ceil(log2(1 / eta)); R = (s + 1) / (F(1, 2) - eta)
    for k in list(range(1, 3000)) + list(range(3000, 10 ** 6, 997)):
        ms, _ = path(k, D, eta)
        for l, m in enumerate(ms):               # the closed-form bound on every m_l
            assert m <= (F(1, 2) + eta) ** l * k + R, (k, l, m)
        srch = sum(F(m, 2) for m in ms[:-1]); leaf = (1 + eps) * LOG6751_UP * ms[-1]
        # early stop below 1/eta terminals adds at most the constant (1 + eps) log2(6.751) / eta
        assert srch + leaf <= ex * k + len(ms) * R / 2 + (1 + eps) * LOG6751_UP * (R + 1 / eta), (k, D)
    print(f"delta={float(delta):5.3f}  D={D}  eta={float(eta):.4f}  s={s:2d}  k-exponent {float(ex):.4f} <= {float(1 + delta / 2):.3f}"
          f"   n-exponent from the searches over A: (s/2) D = {s * D / 2}   space factor (2L)^D with L = O(k + log n)")
print("all checks passed")
