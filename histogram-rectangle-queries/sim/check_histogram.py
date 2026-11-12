"""Largest rectangle in a histogram: OPT = max over intervals I of |I| * min(h on I).
(A) Exact: for each scale w = 2^a and lattice point p (multiple of w), the window [p - 2w + 1, p + 2w - 1]. Every
interval with length in [w, 2w) contains a lattice point and lies in its window. The left and right record staircases
from p (positions of new strict minima moving outward, inside the window) determine the best interval through p in
the window. Records number at most min(H, 2w), H = number of distinct heights, and the gaps between consecutive records
sum to at most 2w, so the first-finding searches cost sum sqrt(gap) <= sqrt(R * 2w) per side.
(B) Approximation (Theorem 4): thresholds t_b = m / (1+eps)^b for b = 0..B, B = ceil(log_{1+eps} n), m the largest
height; output max_b t_b * L(t_b) with L(t) the longest run of heights >= t. It lies in [OPT / (1+eps), OPT].
Checks against the stack algorithm."""
import math, random

def opt(h):
    best, st = 0, []
    for i, x in enumerate(list(h) + [-1]):
        start = i
        while st and st[-1][1] >= x:
            s, v = st.pop()
            best = max(best, v * (i - s)); start = s
        st.append((start, x))
    return best

def staircase(h, p, lo, hi, step):
    """Records from p in direction step (-1 or +1) within [lo, hi]: list of (position, value), and the search cost."""
    recs, cost, q = [(p, h[p])], 0.0, p
    while True:
        v = h[q]; nq = q + step
        while lo <= nq <= hi and h[nq] >= v:
            nq += step
        gap = abs(nq - q)
        cost += math.sqrt(gap)
        if not (lo <= nq <= hi):
            return recs, cost, (lo - 1 if step < 0 else hi + 1)
        recs.append((nq, h[nq])); q = nq

def best_through(h, p, w):
    n = len(h)
    lo, hi = max(0, p - 2 * w + 1), min(n - 1, p + 2 * w - 1)
    L, cl, lend = staircase(h, p, lo, hi, -1)
    R, cr, rend = staircase(h, p, lo, hi, +1)
    best = 0
    for v in {x for _, x in L} | {x for _, x in R}:
        l = next((q for q, x in L if x < v), lend) + 1      # first left record below v, or past the window
        r = next((q for q, x in R if x < v), rend) - 1
        if l <= p <= r:
            best = max(best, v * (r - l + 1))
    return best, len(L), len(R), cl, cr, hi - lo + 1

def exact(h):
    n, H = len(h), len(set(h))
    best, w = 0, 1
    while w <= n:
        for p in range(0, n, w):
            b, nl, nr, cl, cr, size = best_through(h, p, w)
            assert nl <= min(H, 2 * w) and nr <= min(H, 2 * w)
            assert cl <= math.sqrt(nl * 2 * w) + 1e-9 and cr <= math.sqrt(nr * 2 * w) + 1e-9
            best = max(best, b)
        w *= 2
    return best

def approx(h, eps):
    n, m = len(h), max(h)
    if m == 0:
        return 0
    B = 0
    while (1 + eps) ** B < n:
        B += 1
    best = 0
    for b in range(B + 1):
        t = m / (1 + eps) ** b
        L = max((len(r) for r in ''.join('1' if x >= t else '0' for x in h).split('0')), default=0)
        best = max(best, t * L)
    return best

if __name__ == "__main__":
    rng = random.Random(1)
    cnt = 0
    for _ in range(3000):
        n = rng.randint(1, 60)
        kind = rng.randrange(4)
        if kind == 0:
            vals = [rng.randint(0, 9) for _ in range(rng.randint(1, 5))]
            h = [rng.choice(vals) for _ in range(n)]
        elif kind == 1:
            h = [rng.randint(0, 100) for _ in range(n)]
        elif kind == 2:                                    # staircases, many records
            h = sorted(rng.randint(1, 1000) for _ in range(n))
            if rng.random() < 0.5: h.reverse()
        else:                                              # pyramid with noise
            h = [min(i, n - 1 - i) * 3 + rng.randint(0, 2) for i in range(n)]
        o = opt(h)
        assert exact(h) == o
        eps = rng.choice([1.0, 0.5, 0.25, 0.1, 0.01])
        a = approx(h, eps)
        assert o / (1 + eps) - 1e-9 <= a <= o + 1e-9, (h, eps, a, o)
        cnt += 1
    print("cases", cnt, "all checks passed")
