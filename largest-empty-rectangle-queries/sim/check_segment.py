"""Longest empty segment and longest run of identical characters, by scale and lattice.
Checks against brute force:
(1) the scale test: there is a run of length >= K iff some lattice point p (p divisible by K) has a run of length >= K
    through it, decided inside the window [p - K + 1, p + K - 1];
(2) for K <= L < 2K, where L is the longest run, the largest window value over the lattice points of spacing K, each
    computed inside [p - 2K, p + 2K], equals L;
(3) the windows are consistent: the value at p never exceeds the true run through p."""
import random

def runs(x, ok):
    """Length of the maximal run of positions i with ok(i) through each position (0 if not ok)."""
    n = len(x); r = [0] * n; i = 0
    while i < n:
        if not ok(i):
            i += 1; continue
        j = i
        while j < n and ok(j) and (j == i or same(x, i, j)):
            j += 1
        for t in range(i, j):
            r[t] = j - i
        i = j
    return r

def same(x, i, j):
    return x[i] == x[j]

def window_run(x, p, ok, w):
    """Run through p computed only from the positions within distance w of p; capped at the window."""
    n = len(x)
    if not ok(p):
        return 0
    right = p
    while right + 1 < n and right + 1 <= p + w and ok(right + 1) and same(x, p, right + 1):
        right += 1
    left = p
    while left - 1 >= 0 and left - 1 >= p - w and ok(left - 1) and same(x, p, left - 1):
        left -= 1
    return right - left + 1

def check(x, ok):
    n = len(x)
    r = runs(x, ok)
    L = max(r) if r else 0
    for K in range(1, n + 1):
        has = any(window_run(x, p, ok, K - 1) >= K for p in range(0, n, K))
        assert has == (L >= K), (x, K, L)
        if K <= L < 2 * K:
            best = max(window_run(x, p, ok, 2 * K) for p in range(0, n, K))
            assert best == L, (x, K, L, best)
    for p in range(n):
        for w in range(0, n + 1):
            assert window_run(x, p, ok, w) <= r[p]
    return L

if __name__ == "__main__":
    rng = random.Random(3)
    cnt = 0
    for _ in range(3000):
        n = rng.randint(1, 40)
        p1 = rng.choice([0.02, 0.05, 0.1, 0.3, 0.6])
        x = [1 if rng.random() < p1 else 0 for _ in range(n)]
        check(x, lambda i, x=x: x[i] == 0)            # longest empty segment: runs of zeros
        y = [rng.choice("ab" if rng.random() < 0.5 else "abc") if rng.random() < p1 else "a" for _ in range(n)]
        check(y, lambda i: True)                      # longest run of identical characters
        cnt += 1
    for n in range(1, 15):                            # all binary strings up to length 14
        for m in range(1 << n):
            x = [(m >> i) & 1 for i in range(n)]
            check(x, lambda i, x=x: x[i] == 0)
            check(x, lambda i: True)
    print("scale test and lattice maximum agree with brute force on", cnt, "random strings of each kind and all binary strings up to length 14")
