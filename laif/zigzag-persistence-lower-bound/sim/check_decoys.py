"""Checks for the block-decoy lower bound for zigzag persistence statistics S_r.

1. The gadget (spanning star in every snapshot, chords between leaves) has S_r equal to the sum over
   chord rows of sum over runs (u/m)^r: computed independently through the random-window identity
   S_r = E beta_1(G_[min T, max T]) over r uniform times, by brute force over all m^r tuples.
2. A decoy row (exactly one zero in each of s consecutive blocks) has run sum at most (4/s)^(r-1).
3. The relation of Theorem 1 has the degrees used in the proof (brute force on tiny instances).
"""
import itertools, random
from fractions import Fraction

def blocks(m, s):
    q, rem = divmod(m, s)
    sizes = [q + 1] * rem + [q] * (s - rem)
    out, start = [], 0
    for z in sizes:
        out.append(range(start, start + z)); start += z
    return out

def run_sum(row, r):
    m, tot, u = len(row), Fraction(0), 0
    for b in list(row) + [0]:
        if b: u += 1
        else:
            tot += Fraction(u, m) ** r; u = 0
    return tot

def beta1(n, edges):
    parent = list(range(n))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    comps = n
    for u, v in edges:
        a, b = find(u), find(v)
        if a != b: parent[a] = b; comps -= 1
    return len(edges) - n + comps

def window_stat(n, m, rows, r):
    """rows: dict chord (u,v) -> 0/1 list of length m; vertex 0 is the star centre."""
    star = [(0, v) for v in range(1, n)]
    tot = Fraction(0)
    for ts in itertools.product(range(m), repeat=r):
        a, b = min(ts), max(ts)
        chords = [e for e, row in rows.items() if all(row[t] for t in range(a, b + 1))]
        tot += beta1(n, star + chords)
    return tot / m ** r

rng = random.Random(7)
for trial in range(40):
    n, m, r = rng.randint(4, 6), rng.randint(3, 6), rng.choice([2, 3])
    pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
    rows = {e: [rng.randint(0, 1) for _ in range(m)] for e in rng.sample(pairs, rng.randint(1, len(pairs)))}
    assert window_stat(n, m, rows, r) == sum(run_sum(row, r) for row in rows.values())
print("gadget statistic equals the run sum on 40 random instances")

worst = 0
for m in range(2, 61):
    for s in range(1, m + 1):
        for r in (2, 3, 4, 6):
            for _ in range(20):
                row = [1] * m
                for B in blocks(m, s): row[rng.choice(list(B))] = 0
                v = run_sum(row, r); bound = Fraction(4, s) ** (r - 1)
                assert v <= bound, (m, s, r, row)
                worst = max(worst, float(v / bound))
print("decoy run sum <= (4/s)^(r-1) on all tested decoys, largest ratio", round(worst, 4))

# 3. Relation degrees of Theorem 1 by brute force on tiny instances: x has a full rows (others decoy),
#    y has b = a + d full rows; x ~ y if y fills every zero of exactly d decoy rows of x.
from math import comb, prod
def decoys(m, s):
    out = []
    for zs in itertools.product(*blocks(m, s)):
        row = [1] * m
        for z in zs: row[z] = 0
        out.append(tuple(row))
    return out
for (N, m, s, a, d) in [(3, 4, 2, 1, 1), (4, 4, 2, 1, 2), (4, 6, 3, 2, 1), (5, 4, 2, 1, 2)]:
    full = tuple([1] * m); D = decoys(m, s); b = a + d
    def inputs(k):
        res = []
        for F in itertools.combinations(range(N), k):
            for pats in itertools.product(D, repeat=N - k):
                it = iter(pats); res.append(tuple(full if e in F else next(it) for e in range(N)))
        return res
    X, Y = inputs(a), inputs(b)
    def related(x, y):
        ch = [e for e in range(N) if x[e] != y[e]]
        return len(ch) == d and all(y[e] == full for e in ch)
    x0 = X[0]; mx = sum(related(x0, y) for y in Y)
    y0 = Y[0]; my = sum(related(x, y0) for x in X)
    assert mx == comb(N - a, d) and my == comb(b, d) * prod(len(B) for B in blocks(m, s)) ** d
    # a position i that is a zero of a decoy row of x0
    e = next(e for e in range(N) if x0[e] != full); i = x0[e].index(0)
    lx = sum(related(x0, y) and y[e][i] != x0[e][i] for y in Y)
    ey = next(e for e in range(N) if y0[e] == full); jblk = [B for B in blocks(m, s) if 0 in B][0]
    ly = sum(related(x, y0) and x[ey][0] != y0[ey][0] for x in X)
    ratio = mx * my / (lx * ly)
    assert abs(ratio - (N - a) * b * len(jblk) / d ** 2) < 1e-9, (ratio, (N - a) * b * len(jblk) / d ** 2)
print("relation degrees of Theorem 1 checked")

# 4. Constants of Theorem 1 on a grid, exact arithmetic where it matters.
from math import ceil, floor, sqrt
cases = 0
for n in (4100, 5000, 20000, 10**5, 10**6):
    N = (n - 1) * (n - 2) // 2
    for eps in (Fraction(1, n), Fraction(1, 100), Fraction(1, 8)):
        for K in sorted({256 * n, 1000 * n, N // 64, N // 8}):
            if not 256 * n <= K <= Fraction(N, 8): continue
            for r in (2, 3, 4, 7):
                Y = (2 * N / K) ** (1 / (r - 1)); s = ceil(4 * Y)
                lam = Fraction(4, s) ** (r - 1)
                b = K // 2; d = floor(4 * eps * n) + 1; a = b - d
                assert a >= 0 and N * lam <= Fraction(K, 2)                  # choice of s
                assert b + (N - b) * lam <= K                                # promise on Y (and on X)
                assert d * (1 - lam) > 2 * eps * n                           # related pairs separate
                assert s <= 5 * Y and d <= 5 * eps * n and N >= Fraction(n * n, 4)
                m = ceil(10 * Y); L = m // s
                assert L >= m / (10 * Y) - 1e-9
                assert sqrt((N - a) * b * L) / d >= sqrt(K * L) / (29 * float(eps)) * (1 - 1e-12)
                cases += 1
print("constants of Theorem 1 checked on", cases, "parameter cases")
