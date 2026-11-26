"""Exact checks on small Pigeonhole Equal Subset Sum instances (n <= 15).
(a) Lemma 4 of the ESA 2025 paper: -i F <= w_i - 2^{i-1} <= F under prefix condition (1).
(b) Close pairs: |D| <= 200 n^5, and some (X, Y) in D has F(W_{X,Y}) >= F / |C|.
(c) Bins mod a random prime p ~ P of the subset sums of W = W_{X,Y}:
    E_p sum_r |T_r|^2 <= sum_t f_t^2 + 2 n N0^2 / P  (second moment used in the light case),
    and the number of bins holding a repeated sum is >= c/2 for most p when P >= 4 n c (c = number of repeated sums)."""
import random, itertools, math, sys
from collections import Counter

def sums(w):
    s = [0]
    for x in w:
        s = s + [y + x for y in s]
    return s

def F_of(w):
    return sum(c - 1 for c in Counter(sums(w)).values())

def primes_between(a, b):
    return [q for q in range(max(2, a), b + 1) if all(q % d for d in range(2, int(q ** 0.5) + 1))]

def instance(n, rng):
    # w_i = 2^{i-1} + noise, sorted, sum < 2^n - 1, and prefix condition (1); retry until valid
    while True:
        e = rng.choice([0, 1, 2, 4, 16, 64])
        w = sorted(set(max(1, (1 << i) + rng.randint(-e * (i + 1), e)) for i in range(n)))
        if len(w) < n or sum(w) >= (1 << n) - 1:
            continue
        if all(sum(w[:i]) >= (1 << i) - 1 for i in range(1, n)):
            return w

rng = random.Random(7)
checked = 0
for trial in range(60):
    n = rng.randint(8, 14)
    w = instance(n, rng)
    F = F_of(w)
    assert F >= 1                                        # pigeonhole
    for i in range(1, n + 1):                            # (a)
        assert -i * F <= w[i - 1] - (1 << (i - 1)) <= F, (w, F, i)
    k = F.bit_length() - 1                               # 2^k <= F < 2^{k+1}
    if k >= n - 1:
        continue
    hi = list(range(k, n))                               # 0-based indices of [n] \ [k]
    B = (k + 1) << (k + 1)
    sub = [frozenset(c) for r in range(len(hi) + 1) for c in itertools.combinations(hi, r)]
    wt = {S: sum(w[i] for i in S) for S in sub}
    C = [(X, Y) for X in sub for Y in sub if abs(wt[X] - wt[Y]) <= B]
    D = [(X, Y) for (X, Y) in C if not (X & Y)]
    assert len(D) <= 200 * n ** 5                        # (b)
    best = 0
    for X, Y in D:
        W = w[:k] if X == Y else w[:k] + [wt[X] - wt[Y]]
        best = max(best, F_of(W))
    assert best * len(C) >= F, (n, F, best, len(C))
    checked += 1
    # (c) on the best W
    for X, Y in D:
        W = w[:k] if X == Y else w[:k] + [wt[X] - wt[Y]]
        if F_of(W) == best:
            break
    ss = sums(W); N0 = len(ss); f = Counter(ss)
    rep = [t for t, c in f.items() if c >= 2]
    sumf2 = sum(c * c for c in f.values())
    for P in [8, 32, 128]:
        ps = primes_between(P, 2 * P)
        m2 = sum(sum(v * v for v in Counter(s % p for s in ss).values()) for p in ps) / len(ps)
        assert m2 <= sumf2 + 2 * (n + 1) * N0 * N0 / P, (P, m2, sumf2)
        if P >= 4 * (n + 1) * len(rep) and rep:
            good = [len({t % p for t in rep}) for p in ps]
            assert sum(g >= len(rep) / 2 for g in good) >= 0.75 * len(ps)
print("instances checked:", checked)
assert checked >= 20
