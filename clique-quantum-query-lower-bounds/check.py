"""Brute-force checks for the K_k lower bound on G = K_{n,...,n} (k parts).

Checks, for k = 4, 5, 6:
- the candidate multiplicities of the sums over A_e and B_{u,v};
- that every edge j interacting with a queried edge i is counted by one of
  the two extension patterns (j sharing a vertex with i, j disjoint from i),
  and that inside a star the interaction count is at most an outside degree
  (on sampled inputs only: the sampler deletes one edge of each present K_k,
  which does not sample the conditioned distribution, and only the sampled
  star assignments are tested; the proof argues both claims for all inputs);
- the coefficients of the comparison map;
- with exact fractions: planting exponents, the exponents of all
  sub-extensions of both patterns, the final exponent, and kappa <= R.
"""
import itertools
import random
from fractions import Fraction as Fr
from math import comb


def graph(k, n):
    V = [(a, i) for a in range(k) for i in range(n)]
    E = [frozenset((u, v)) for u, v in itertools.combinations(V, 2) if u[0] != v[0]]
    K = [frozenset(frozenset(p) for p in itertools.combinations(q, 2))
         for q in itertools.product(*[[(a, i) for i in range(n)] for a in range(k)])]
    return V, E, K


def check_multiplicities(k, n):
    V, E, K = graph(k, n)
    for e in E:
        u, v = tuple(e)
        A = [T for T in K if e in T]
        assert len(A) == n ** (k - 2)
        for T in A:
            for j in T - {e}:
                cnt = sum(1 for S in A if j in S)
                assert cnt == (n ** (k - 3) if (u in j or v in j) else n ** (k - 4))
        for w, o in ((u, v), (v, u)):
            B = [T for T in K if any(w in i for i in T) and not any(o in i for i in T)]
            assert len(B) == (n - 1) * n ** (k - 2)
            for T in B:
                for j in T:
                    cnt = sum(1 for S in B if j in S)
                    assert cnt <= (n ** (k - 2) if w in j else n ** (k - 3))


def kk_free_sample(E, K, p, rng):
    x = {e: rng.random() < p for e in E}
    for T in K:  # delete one edge of every present K_k
        if all(x[i] for i in T):
            x[rng.choice(sorted(T, key=sorted))] = False
    return x


def check_interactions(k, n, p, trials, rng):
    V, E, K = graph(k, n)
    by_pair, by_edge = {}, {}
    for T in K:
        for i in T:
            by_edge.setdefault(i, []).append(T)
        for i, j in itertools.permutations(T, 2):
            by_pair.setdefault((i, j), []).append(T)
    for _ in range(trials):
        x = kk_free_sample(E, K, p, rng)
        assert not any(all(x[i] for i in T) for T in K)
        adj = lambda a, b: a[0] != b[0] and x[frozenset((a, b))]
        N = {v: {u for u in V if adj(u, v)} for v in V}
        for i in E:
            inter = {j for j in E if j != i and any(all(x[c] for c in T - {i, j})
                                                    for T in by_pair.get((i, j), []))}
            # tuple counts: vertex sets of a K_k through i with all edges but i, j present
            tuples = set()
            for T in by_edge.get(i, []):
                for j in T - {i}:
                    if all(x[c] for c in T - {i, j}):
                        tuples.add((j, T))
            assert inter == {j for j, _ in tuples}
            u, v = tuple(i)
            for w in (u, v):  # star at w, i = wa
                a = v if w == u else u
                star = {j for j in inter if w in j}
                assert len(star) <= len(N[a] - {w})


def check_map(s):
    for _ in range(50):
        c0, cs = random.random(), [random.random() for _ in range(s)]
        f = lambda bits: c0 + sum(c * b for c, b in zip(cs, bits))
        unit = lambda i: [1 if t == i else 0 for t in range(s)]
        val = sum(f(unit(i)) for i in range(s)) - (s - 1) * f([0] * s)
        assert abs(val - f([1] * s)) < 1e-9
        # query error for e = 0: Q+ T f - T Q- f = -2 sum_{i != e} (f_i - f_0)
        g = lambda i: f(unit(i))
        lhs = -val - (-g(0) + sum(g(i) for i in range(1, s)) - (s - 1) * f([0] * s))
        assert abs(lhs + 2 * sum(g(i) - f([0] * s) for i in range(1, s))) < 1e-9


def sub_extension_exponents(k, theta):
    """log_n of n^{|S|} p^{e(S)} over nonempty S, both patterns, p = n^{-theta}."""
    out = []
    # pattern 1: roots u, v; non-roots w, y_1..y_{k-3}; all pairs but uv, uw.
    # pattern 2: roots u, v; non-roots w, z, y_1..y_{k-4}; all pairs but uv, wz.
    for missing, nonroots in ((("u", "w"), ["w"] + [f"y{t}" for t in range(k - 3)]),
                              (("w", "z"), ["w", "z"] + [f"y{t}" for t in range(k - 4)])):
        verts = ["u", "v"] + nonroots
        edges = {frozenset(q) for q in itertools.combinations(verts, 2)}
        edges -= {frozenset(("u", "v")), frozenset(missing)}
        for r in range(1, len(nonroots) + 1):
            for S in itertools.combinations(nonroots, r):
                inside = set(S) | {"u", "v"}
                eS = sum(1 for q in edges if q <= inside and q & set(S))
                out.append(r - theta * eS)
        assert eS == len(edges) == comb(k, 2) - 2
    return out


def check_exponents():
    for k in range(4, 8):
        s = comb(k, 2)
        theta = Fr(2, k + 1)
        # planting: a new K_k sharing j vertices with T, 2 <= j <= k-1
        for j in range(2, k):
            ex = (k - j) - theta * (s - comb(j, 2))
            assert ex == Fr((k - j) * (2 - j), k + 1) and ex <= 0
        # extension counts: full count ~ 1/p, every sub-extension grows polynomially
        ex = sub_extension_exponents(k, theta)
        assert min(ex) >= Fr(1, k + 1)
        assert (k - 2) - theta * (s - 2) == theta  # n^{k-2} p^{s-2} = n^{theta} ~ 1/p
        # alpha ~ n^{-3}(R/p + n^2 p/R^2), R = (np)^{2/3}
        r = Fr(2, 3) * (1 - theta)
        assert r + theta - 3 == 2 - theta - 2 * r - 3 == Fr(-7, 3) + theta / 3
        assert 1 - r - 3 <= r + theta - 3  # n/R is smaller
        # kappa ~ n p^2 at most R ~ (np)^{2/3}
        assert (1 - 2 * theta <= r) == (k <= 7)
    final = {k: Fr(7, 6) - Fr(2, k + 1) / 6 for k in range(4, 8)}
    assert final == {4: Fr(11, 10), 5: Fr(10, 9), 6: Fr(47, 42), 7: Fr(9, 8)}
    return final


if __name__ == "__main__":
    rng = random.Random(1)
    for n in range(1, 5):
        check_multiplicities(4, n)
    for n in range(1, 4):
        check_multiplicities(5, n)
    for n in range(1, 3):
        check_multiplicities(6, n)
    check_interactions(4, 3, 0.6, 3, rng)
    check_interactions(5, 2, 0.7, 3, rng)
    check_interactions(5, 3, 0.6, 1, rng)
    for s in (6, 10, 15):
        check_map(s)
    print(check_exponents())
    print("all checks passed")
