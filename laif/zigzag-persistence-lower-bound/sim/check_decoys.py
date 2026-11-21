"""Checks for the block-decoy lower bound for zigzag persistence statistics S_r.

1. The gadget (spanning star in every snapshot, chords between leaves) has S_r equal to the sum over
   chord rows of sum over runs (u/m)^r: computed independently through the random-window identity
   S_r = E beta_1(G_[min T, max T]) over r uniform times, by brute force over all m^r tuples.
2. A decoy row (exactly one zero in each of s consecutive blocks) has run sum at most (4/s)^(r-1).
3. Adv+- of the inner function (all ones -> 1, one zero per block -> 0) is at least sqrt(min block).
"""
import itertools, random
from fractions import Fraction
import numpy as np, cvxpy as cp

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

def adv(f, n):
    D = list(f); N = len(D); A = np.array(D); F = np.array([f[x] for x in D])
    diff = F[:, None] != F[None, :]
    X = [cp.Variable((N, N), PSD=True) for _ in range(n)]; s = cp.Variable()
    S = sum(cp.multiply((A[:, None, j] != A[None, :, j]).astype(float), X[j]) for j in range(n))
    cp.Problem(cp.Minimize(s), [sum(cp.diag(X[j]) for j in range(n)) <= s, S[diff] == 1]).solve(solver='CLARABEL')
    return s.value

for m, s in [(4, 2), (6, 2), (6, 3), (7, 2), (8, 2), (8, 4)]:
    B = blocks(m, s)
    f = {tuple([1] * m): 1}
    for zs in itertools.product(*B):
        row = [1] * m
        for z in zs: row[z] = 0
        f[tuple(row)] = 0
    a = adv(f, m); L = min(len(b) for b in B)
    print(f"m={m} s={s}: Adv(g)={a:.4f} sqrt(min block)={L ** 0.5:.4f}")
    assert a >= L ** 0.5 * (1 - 1e-6)
print("inner adversary bound checked")
