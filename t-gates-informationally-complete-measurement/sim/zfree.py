# Checks of the Z-free counting lemma with asserts. A vector of (F_2^2)^t is a t-qubit Pauli string up to phase; it is
# Z-free if no coordinate is Z. Lemma: a coset of a D-dimensional subspace contains at most 3^{D-t} 2^{2t-D} Z-free
# vectors if D >= t, and at most 2^D if D <= t.
#  (1) exhaustively over all subspaces and all their cosets for t <= 3 (the bound is attained for every D);
#  (2) on random subspaces and cosets for t = 4..8;
#  (3) the resulting bound t >= (3 - log2 3) n: smallest t with 3^n 2^{t-n} >= 4^n, against 2n/log2 3.
# python -I zfree.py
import math
import random

Z = 2                                     # coordinate encoding: 0 = I, 1 = X, 2 = Z, 3 = Y


def zfree(a, t):
    return all(((a >> 2 * i) & 3) != Z for i in range(t))


def span(gens):
    S = {0}
    for v in gens:
        S |= {s ^ v for s in S}
    return frozenset(S)


def bound(t, D):
    return 3 ** (D - t) * 2 ** (2 * t - D) if D >= t else 2 ** D


for t in (1, 2, 3):
    N = 1 << (2 * t)
    subs = {0: {frozenset({0})}}
    for D in range(1, 2 * t + 1):
        subs[D] = {span(list(S) + [v]) for S in subs[D - 1] for v in range(1, N) if v not in S}
        best = max(sum(zfree(a ^ c, t) for a in S) for S in subs[D] for c in range(N))
        assert best == bound(t, D), (t, D, best)
    print(f"t = {t}: all subspaces and cosets checked, maximum equals the bound for every D")

rng = random.Random(7)
for t in range(4, 9):
    N = 1 << (2 * t)
    for _ in range(3000):
        D = rng.randint(1, 2 * t)
        S = span([rng.randrange(1, N) for _ in range(D)])
        D = round(math.log2(len(S)))
        c = rng.randrange(N)
        assert sum(zfree(a ^ c, t) for a in S) <= bound(t, D)
    print(f"t = {t}: 3000 random cosets within the bound")

for n in (1, 2, 3, 5, 10, 100, 1000):
    t = next(t for t in range(n, 3 * n + 1) if 3 ** n * 2 ** (t - n) >= 4 ** n)
    old = math.ceil(2 * n / math.log2(3))
    assert t >= old
    print(f"n = {n}: t >= {t} (previous {old}, upper {2 * n})")
print("Z-free checks: ok")
