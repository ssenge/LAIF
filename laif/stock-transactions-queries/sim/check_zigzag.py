"""Checks for the t-transaction stock problem.

f(t): largest total profit of at most t disjoint transactions (buy at i, sell at j > i), by DP.
F(lam): largest total of (profit - lam) over any number of transactions, by the two-state DP.
zigzag(lam): the threshold zigzag; returns its value and the number of transactions.
Asserts: zigzag(lam) == F(lam); f is concave; and the Lagrangian recovery
  f(t) = f(m) + (t - m) a*, with a* = smallest integer a such that m(a + eps) <= t, m = m(a* + eps).
phases(x, c, t): the zigzag at integer threshold c (rise or drop >= c, i.e. lam = c - 1 + eps), as a list of
  phases found by "first index where the largest rise (drop) of the window reaches c", stopped after t + 1 legs.
  Asserts it agrees with zigzag, that m(a + eps) is nonincreasing in a, and sum sqrt(phase length) <= sqrt((2t+3)n).
Lower bound encoding: prices 0, b_1, 0, b_2, ... with b in {0,1} give f(t) = min(t, |b|).
"""
import random
from fractions import Fraction as Fr


def f_dp(x, t):
    NEG = float("-inf")
    cash = [0] + [NEG] * t          # cash[k]: completed k transactions, not holding
    hold = [NEG] * (t + 1)          # hold[k]: holding the (k+1)-th
    for p in x:
        for k in range(t, -1, -1):
            if k > 0 and hold[k - 1] != NEG:
                cash[k] = max(cash[k], hold[k - 1] + p)
            if cash[k] != NEG:
                hold[k] = max(hold[k], cash[k] - p)
    return max(cash)


def F_dp(x, lam):
    cash, hold = Fr(0), None
    for p in x:
        nc = cash if hold is None else max(cash, hold + p - lam)
        nh = cash - p if hold is None else max(hold, cash - p)
        cash, hold = nc, nh
    return cash


def zigzag(x, lam):
    """Threshold zigzag: track the low until a rise >= lam, then the high until a drop >= lam."""
    total, m = Fr(0), 0
    lo, hi, up = x[0], None, False
    for p in x[1:]:
        if not up:
            if p - lo >= lam:
                up, hi = True, p
            else:
                lo = min(lo, p)
        else:
            if hi - p >= lam:
                total += hi - lo - lam; m += 1
                up, lo = False, p
            else:
                hi = max(hi, p)
    if up:
        total += hi - lo - lam; m += 1
    return total, m


def recover(x, t):
    n = len(x)
    eps = Fr(1, 2 * n + 1)
    W = max(x) - min(x) + 1
    lo, hi = 0, W                    # m(hi + eps) <= t holds, since no rise exceeds W
    if zigzag(x, Fr(0) + eps)[1] <= t:
        a = 0
    else:
        while hi - lo > 1:           # invariant: m(lo + eps) > t, m(hi + eps) <= t
            mid = (lo + hi) // 2
            if zigzag(x, mid + eps)[1] <= t:
                hi = mid
            else:
                lo = mid
        a = hi
    val, m = zigzag(x, a + eps)
    fm = val + (a + eps) * m
    assert fm.denominator == 1
    return fm + (t - m) * a


def max_rise(w):
    best, lo = 0, w[0]
    for p in w:
        best, lo = max(best, p - lo), min(lo, p)
    return best


def phases(x, c, t):
    """Phases of the zigzag at integer threshold c >= 1; returns (profit of completed legs, legs, lengths)."""
    n, r, up, legs, prof, lens = len(x), 0, False, 0, 0, []
    lo = None
    while r < n and legs <= t:
        sgn = 1 if not up else -1
        j = next((j for j in range(r + 1, n) if max_rise([sgn * p for p in x[r:j + 1]]) >= c), None)
        end = n if j is None else j
        lens.append(end - r)
        if not up:
            lo = min(x[r:end])
            if j is None:
                break
            up, r = True, j
        else:
            hi = max(x[r:end])
            prof += hi - lo
            legs += 1
            if j is None:
                break
            up, r = False, j
    return prof, legs, lens


def main():
    rng = random.Random(3)
    cnt = 0
    for _ in range(3000):
        n = rng.randint(1, 14)
        W = rng.choice([1, 2, 5, 30])
        x = [rng.randint(0, W) for _ in range(n)]
        fs = [f_dp(x, t) for t in range(n + 1)]
        for t in range(1, n):
            assert fs[t + 1] - fs[t] <= fs[t] - fs[t - 1], "concavity"
        for lam in [Fr(0), Fr(1, 2), Fr(1), Fr(3), Fr(7, 3), Fr(W)]:
            assert zigzag(x, lam)[0] == F_dp(x, lam), (x, lam)
        for t in range(0, n + 1):
            assert recover(x, t) == fs[t], (x, t)
        prev = None
        for a in range(0, W + 2):
            val, m = zigzag(x, a + Fr(1, 2 * n + 1))
            prof, legs, _ = phases(x, a + 1, n)
            assert (prof, legs) == (val + (a + Fr(1, 2 * n + 1)) * m, m)
            assert prev is None or m <= prev
            prev = m
            for t in range(0, n + 1):
                _, lg, lens = phases(x, a + 1, t)
                assert sum(lens) <= n and len(lens) <= 2 * t + 3
                assert sum(l ** 0.5 for l in lens) <= ((2 * t + 3) * n) ** 0.5 + 1e-9
                assert (lg <= t) == (m <= t)
        cnt += 1
    print(f"{cnt} price sequences checked")
    for _ in range(500):
        b = [rng.randint(0, 1) for _ in range(rng.randint(1, 8))]
        x = [v for bi in b for v in (0, bi)]
        for t in range(len(b) + 1):
            assert f_dp(x, t) == min(t, sum(b))
    print("lower bound encoding checked")


if __name__ == "__main__":
    main()
