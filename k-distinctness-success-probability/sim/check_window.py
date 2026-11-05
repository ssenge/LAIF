"""Exponent check: nested Grover algorithm vs Belovs's success bound for k-distinctness.
Everything is an exponent of n. T = n^tau."""
from fractions import Fraction as F

def belovs(k, tau):          # success <= 1/n + T^(4-2^(2-k)) / n^(3-2^(2-k))  [Belovs 2604.05133, Thm 6.15]
    e = 4 - F(2) ** (2 - k)
    return max(F(-1), e * tau - (e - 1))

def nested(k, tau):
    """r_1 = T, r_l = T sqrt(r_{l-1}/n), last stage Grover with T iterations on one marked item.
    Returns (log success, list of log r_l) or None if a constraint fails."""
    r = [tau]
    for _ in range(2, k):
        r.append(tau + (r[-1] - 1) / 2)
    if tau > F(1, 2) or r[-1] < 0:                       # last Grover unsaturated, list nonempty
        return None
    for l in range(1, len(r)):                           # stage l+1 searches among M = Theta(r_{l}) marked
        if r[l] > r[l - 1] or 2 * tau + r[l - 1] < 1:     # r_l <= M, and T^2 M >= n (BBHT regime)
            return None
    p = r[-1] + 2 * tau - 2                              # (r_{k-1}/n) * T^2/n
    return p, r

for k in range(2, 7):
    lo = 1 - 1 / (2 - F(2) ** (1 - k))                   # where the T-term of Belovs's bound overtakes 1/n
    alg_lo = 1 - 1 / (2 - F(2) ** (2 - k)) if k > 2 else F(1, 3)
    for tau in [lo, (lo + F(1, 2)) / 2, F(1, 2)]:
        res = nested(k, tau)
        assert res is not None, (k, tau)
        assert res[0] == belovs(k, tau), (k, tau, res[0], belovs(k, tau))
    # just below lo the bound is the 1/n term and the algorithm is strictly below it
    t = lo - F(1, 100)
    if nested(k, t): assert nested(k, t)[0] < belovs(k, t)
    print(f"k={k}: tight for T in [n^{float(lo):.4f}, n^0.5]; algorithm valid from n^{float(alg_lo):.4f}")
print("ok")
