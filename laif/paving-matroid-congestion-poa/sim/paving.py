"""Symmetric matroid congestion games with affine delays d_r(x) = a_r x + b_r (a, b >= 0), the model of
[1, Sec. 2 and 4]: weak pure NE, social cost sum_r s_r d_r(s_r), PoA = worst PNE cost / social optimum.
[1] B. Hao, C. Michini, Price of anarchy in paving matroid congestion games, ACM Trans. Econ. Comput. (2025).

lp_pair(F, H): for a fixed NE profile F and comparison profile H, the NE conditions are linear in (a, b);
maximize cost(F) subject to cost(H) = 1. Since OPT <= cost(H), the value is a lower bound on the PoA.
verify(): exact rational check of a certificate (matroid axioms, paving, NE, OPT by enumeration)."""
import itertools, random
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog


def rank2(sizes):
    """Rank-2 loopless matroid with parallel classes of the given sizes: bases = pairs from different classes."""
    cl = [c for c, s in enumerate(sizes) for _ in range(s)]
    n = len(cl)
    return n, [frozenset(p) for p in itertools.combinations(range(n), 2) if cl[p[0]] != cl[p[1]]]


def is_matroid(n, bases):
    """Basis exchange axiom."""
    S = set(bases)
    return bool(S) and all(any((A - {x}) | {y} in S for y in B - A) for A in S for B in S for x in A - B)


def circuits(n, bases):
    indep = {I for B in bases for k in range(len(B) + 1) for I in map(frozenset, itertools.combinations(B, k))}
    r = len(next(iter(bases)))
    C = []
    for k in range(1, r + 2):
        for D in map(frozenset, itertools.combinations(range(n), k)):
            if D not in indep and all(D - {x} in indep for x in D): C.append(D)
    return r, C


def is_paving(n, bases):
    r, C = circuits(n, bases)
    return all(len(c) >= r for c in C)


def loads(n, bases, P):
    x = [0] * n
    for i in P:
        for e in bases[i]: x[e] += 1
    return x


def cost_row(n, bases, P):
    x = loads(n, bases, P)
    return np.array([v * v for v in x] + x, float)


def lp_pair(n, bases, Fp, Hp):
    x = loads(n, bases, Fp); rows = []
    for i in set(Fp):
        p = bases[i]
        for q in bases:
            if q == p: continue
            r = np.zeros(2 * n)
            for e in p: r[e] += x[e]; r[n + e] += 1
            for e in q: r[e] -= x[e] + (e not in p); r[n + e] -= 1
            rows.append(r)
    res = linprog(-cost_row(n, bases, Fp), A_ub=np.array(rows), b_ub=np.zeros(len(rows)),
                  A_eq=cost_row(n, bases, Hp)[None], b_eq=[1], bounds=[(0, None)] * (2 * n), method="highs")
    return (-res.fun, res.x) if res.status == 0 else (0.0, None)


def verify(n, bases, a, b, Fp):
    """Exact: returns cost(F)/OPT, asserting matroid, paving, a, b >= 0 and that F is a weak PNE."""
    a = [F(v) for v in a]; b = [F(v) for v in b]
    assert is_matroid(n, bases) and is_paving(n, bases) and min(a + b) >= 0
    d = lambda e, k: a[e] * k + b[e]
    x = loads(n, bases, Fp)
    for i in set(Fp):
        p = bases[i]; own = sum(d(e, x[e]) for e in p)
        for q in bases:
            assert sum(d(e, x[e] + (e not in p)) for e in q) >= own
    cost = lambda P: sum(k * d(e, k) for e, k in enumerate(loads(n, bases, P)))
    opt = min(cost(P) for P in itertools.combinations_with_replacement(range(len(bases)), len(Fp)))
    return cost(Fp) / opt


def rationalize(n, bases, Fp, xs):
    for den in (10, 100, 1000, 10**4, 10**6):
        ab = [F(v).limit_denominator(den) if v > 1e-12 else F(0) for v in xs]
        try:
            return verify(n, bases, ab[:n], ab[n:], Fp), ab
        except AssertionError:
            continue
    return None, None


def local_search(n, bases, N, iters, rng, start=None):
    m = len(bases)
    Fp = start[0] if start else tuple(sorted(rng.randrange(m) for _ in range(N)))
    Hp = start[1] if start else tuple(sorted(rng.randrange(m) for _ in range(N)))
    v, _ = lp_pair(n, bases, Fp, Hp)
    for _ in range(iters):
        G = [list(Fp), list(Hp)]; w = rng.randrange(2); G[w][rng.randrange(N)] = rng.randrange(m)
        F2, H2 = tuple(sorted(G[0])), tuple(sorted(G[1]))
        v2, _ = lp_pair(n, bases, F2, H2)
        if v2 >= v - 1e-12: Fp, Hp, v = F2, H2, v2
    return v, Fp, Hp


def check():
    n, B = rank2([2, 2, 1])
    assert is_matroid(n, B) and is_paving(n, B)
    Fp = tuple(sorted(B.index(frozenset(s)) for s in [(0, 2), (0, 2), (1, 4)]))
    assert verify(n, B, [2, 2, 1, 0, 2], [0, 0, 0, 2, 0], Fp) == F(16, 11)
    assert not is_paving(5, [frozenset(s) for s in [(0, 1, 2), (0, 1, 3)]])   # {2,3} parallel: circuit of size 2 < 3
    print("paving.py check ok: 16/11 certificate verified, paving test rejects a non-paving rank-3 matroid")


if __name__ == "__main__":
    check()
