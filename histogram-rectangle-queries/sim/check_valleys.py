"""Exact largest rectangle from weak-record runs (Theorem 3).
For a position p and a window [lo, hi], the weak left records of p are the positions j <= p with h_j <= h_i for all
i in (j, p]. Going outward they form maximal runs of consecutive positions; each run is learnt by one search for its
first position (first j beyond the last record with h_j <= current minimum) and one search for its end (first j with
h_{j-1} > h_j). Checks:
- the number of runs per side is at most V_window + 2, V = number of valleys (maximal plateaus whose neighbours are
  both strictly higher; a missing neighbour counts as higher);
- the search cost sum sqrt(gap) + sum sqrt(len) is at most sqrt(2 R * 2 * size) for R runs;
- the best rectangle through p in the window equals max over weak-record values v of v * (run length at level v),
  where the ends of the run are found by binary search in the other side's weak-record list;
- the maximum over all scales w = 2^a and multiples p of w equals the stack answer."""
import bisect, math, random

def opt(h):
    best, st = 0, []
    for i, x in enumerate(list(h) + [-1]):
        start = i
        while st and st[-1][1] >= x:
            s, v = st.pop(); best = max(best, v * (i - s)); start = s
        st.append((start, x))
    return best

def valleys(h, lo, hi):
    """Valleys of h restricted to [lo, hi], neighbours outside the window count as higher."""
    cnt, i = 0, lo
    while i <= hi:
        j = i
        while j + 1 <= hi and h[j + 1] == h[i]: j += 1
        left_ok = i == lo or h[i - 1] > h[i]
        right_ok = j == hi or h[j + 1] > h[i]
        cnt += left_ok and right_ok
        i = j + 1
    return cnt

def runs(h, p, end, step):
    """Weak-record runs from p in direction step up to end (inclusive). Returns list of (start, stop) and the cost."""
    out, cost, q, m = [], 0.0, p, h[p]
    while True:
        # extend the run while heights do not increase outward
        r = q
        while r + step != end + step and h[r + step] <= h[r]: r += step
        cost += math.sqrt(abs(r - q) + 1)
        out.append((q, r)); m = h[r]
        # next weak record: first position beyond r with height <= m
        nq = r + step
        while nq != end + step and h[nq] > m: nq += step
        cost += math.sqrt(abs(nq - r))
        if nq == end + step:
            return out, cost
        q = nq

def best_through(h, p, lo, hi):
    L, cl = runs(h, p, lo, -1)
    R, cr = runs(h, p, hi, +1)
    V = valleys(h, lo, hi)
    assert len(L) <= V + 2 and len(R) <= V + 2, (h[lo:hi + 1], p - lo, len(L), len(R), V)
    size = hi - lo + 1
    assert cl <= math.sqrt(2 * len(L) * 2 * size) + 1e-9 and cr <= math.sqrt(2 * len(R) * 2 * size) + 1e-9
    lpos = [j for a, b in L for j in range(a, b - 1, -1)]          # outward order, values nonincreasing
    rpos = [j for a, b in R for j in range(a, b + 1)]
    lval = [-h[j] for j in lpos]; rval = [-h[j] for j in rpos]      # nondecreasing, for bisect
    assert lval == sorted(lval) and rval == sorted(rval)
    best = 0
    for v in {h[j] for j in lpos + rpos}:
        k = bisect.bisect_right(lval, -v)                             # first record with h < v
        l = (lpos[k] if k < len(lpos) else lo - 1) + 1
        k = bisect.bisect_right(rval, -v)
        r = (rpos[k] if k < len(rpos) else hi + 1) - 1
        best = max(best, v * (r - l + 1))
    brute = max(min(h[l:r + 1]) * (r - l + 1) for l in range(lo, p + 1) for r in range(p, hi + 1))
    assert best == brute, (h[lo:hi + 1], p - lo, best, brute)
    return best

def exact(h):
    n, best, w = len(h), 0, 1
    while w <= n:
        for p in range(0, n, w):
            best = max(best, best_through(h, p, max(0, p - 2 * w + 1), min(n - 1, p + 2 * w - 1)))
        w *= 2
    return best

if __name__ == "__main__":
    rng = random.Random(5)
    for _ in range(2500):
        n = rng.randint(1, 50)
        kind = rng.randrange(5)
        if kind == 0: h = [rng.randint(0, 4) for _ in range(n)]
        elif kind == 1: h = [rng.randint(0, 100) for _ in range(n)]
        elif kind == 2:
            h = sorted(rng.randint(0, 30) for _ in range(n))
            if rng.random() < 0.5: h.reverse()
        elif kind == 3:                                              # few monotone pieces with plateaus
            h, x = [], rng.randint(0, 50)
            while len(h) < n:
                d = rng.choice([-1, 1]); ln = rng.randint(1, 12)
                for _ in range(ln):
                    x = max(0, x + d * rng.randint(0, 3)); h.append(x)
            h = h[:n]
        else: h = [min(i, n - 1 - i) + rng.randint(0, 1) for i in range(n)]
        assert exact(h) == opt(h), h
    print("all checks passed")
