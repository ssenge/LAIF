# Checks of the Z-free counting lemma with asserts. A vector of (F_2^2)^t is a t-qubit Pauli string up to phase; it is
# Z-free if no coordinate is Z. Lemma: a coset of a D-dimensional subspace contains at most 3^{D-t} 2^{2t-D} Z-free
# vectors if D >= t, and at most 2^D if D <= t.
#  (1) exhaustively over all subspaces and all their cosets for t <= 3 (the bound is attained for every D);
#  (1') exhaustively for t = 4, with each subspace given as the kernel of a unique reduced row echelon matrix H,
#      so that its cosets are the values of H z and the Z-free count of a coset is the multiplicity of H z on Z-free z;
#  (2) on random subspaces and cosets for t = 5..8, and on the extremal subspaces (X and Y on D - t coordinates,
#      X alone on the others, or X alone on D coordinates for D <= t), which attain the bound;
#  (3) the resulting bound t >= (3 - log2 3) n: smallest t with 3^n 2^{t-n} >= 4^n, against 2n/log2 3.
# python -I zfree.py
import itertools
import math
import random

import numpy as np

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

def rref_all(N, k):
    for piv in itertools.combinations(range(N), k):
        free = [(r, c) for r, p in enumerate(piv) for c in range(p + 1, N) if c not in piv]
        for bits in range(1 << len(free)):
            rows = [1 << p for p in piv]
            for i, (r, c) in enumerate(free):
                if bits >> i & 1:
                    rows[r] |= 1 << c
            yield rows


t = 4
parity = np.array([bin(i).count("1") & 1 for i in range(1 << (2 * t))], dtype=np.int64)
zf = np.array([a for a in range(1 << (2 * t)) if zfree(a, t)], dtype=np.int64)
for D in range(2 * t + 1):
    best, count = 0, 0
    for rows in rref_all(2 * t, 2 * t - D):
        lab = np.zeros(len(zf), dtype=np.int64)
        for i, r in enumerate(rows):
            lab |= parity[zf & r] << i
        best = max(best, int(np.bincount(lab).max()) if rows else len(zf))
        count += 1
    assert count == round(np.prod([(2 ** (2 * t - i) - 1) / (2 ** (D - i) - 1) for i in range(D)])), (D, count)
    assert best == bound(t, D), (t, D, best)
print("t = 4: all subspaces and cosets checked, maximum equals the bound for every D")

X, Y = 1, 3
rng = random.Random(7)
for t in range(5, 9):
    for D in range(2 * t + 1):
        k = max(D - t, 0)
        gens = [X << 2 * i for i in range(min(D, t))] + [Y << 2 * i for i in range(k)]
        S = span(gens)
        assert len(S) == 2 ** D and sum(zfree(a, t) for a in S) == bound(t, D), (t, D)
    N = 1 << (2 * t)
    for _ in range(3000):
        D = rng.randint(1, 2 * t)
        S = span([rng.randrange(1, N) for _ in range(D)])
        D = round(math.log2(len(S)))
        c = rng.randrange(N)
        assert sum(zfree(a ^ c, t) for a in S) <= bound(t, D)
    print(f"t = {t}: 3000 random cosets within the bound, extremal subspaces attain it")

for n in (1, 2, 3, 5, 10, 100, 1000):
    t = next(t for t in range(n, 3 * n + 1) if 3 ** n * 2 ** (t - n) >= 4 ** n)
    old = math.ceil(2 * n / math.log2(3))
    assert t >= old
    print(f"n = {n}: t >= {t} (previous {old}, upper {2 * n})")
print("Z-free checks: ok")
