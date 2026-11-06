"""Brute-force checks for the K4 lower bound on G = K_{n,n,n,n}.

Vertices are (part, index). Checks the candidate multiplicities of Step 5,
the interaction bounds of Steps 3 and 4 on random K4-free inputs, the map
coefficients of Step 2, and the exponent arithmetic.
"""
import itertools
import random
from fractions import Fraction as Fr


def graph(n):
    V = [(a, i) for a in range(4) for i in range(n)]
    E = {frozenset((u, v)) for u, v in itertools.combinations(V, 2) if u[0] != v[0]}
    K4 = [frozenset(frozenset(p) for p in itertools.combinations(q, 2))
          for q in itertools.product(*[[(a, i) for i in range(n)] for a in range(4)])]
    return V, E, K4


def check_multiplicities(n):
    V, E, K4 = graph(n)
    for e in E:
        u, v = tuple(e)
        A = [T for T in K4 if e in T]
        assert len(A) == n * n
        for T in A:
            for j in T - {e}:
                cnt = sum(1 for S in A if j in S)
                assert cnt == (n if (u in j or v in j) else 1)
        for w in (u, v):
            o = v if w == u else u
            B = [T for T in K4 if any(w in i for i in T) and not any(o in i for i in T)]
            assert len(B) == (n - 1) * n * n
            for T in B:
                for j in T:
                    cnt = sum(1 for S in B if j in S)
                    assert cnt <= (n * n if w in j else n)


def k4_free_sample(E, K4, p, rng):
    x = {e: rng.random() < p for e in E}
    for T in K4:  # delete one edge of every present K4
        if all(x[i] for i in T):
            x[rng.choice(sorted(T, key=sorted))] = False
    return x


def check_interactions(n, p, trials, rng):
    V, E, K4 = graph(n)
    by_pair = {}
    for T in K4:
        for i, j in itertools.permutations(T, 2):
            by_pair.setdefault((i, j), []).append(T)
    for _ in range(trials):
        x = k4_free_sample(E, K4, p, rng)
        assert not any(all(x[i] for i in T) for T in K4)
        N = {v: {u for u in V if frozenset((u, v)) in E and x[frozenset((u, v))]} for v in V}
        codeg = max(len(N[a] & N[b]) for a, b in itertools.combinations(V, 2))
        for i in E:
            inter = {j for j in E if j != i and any(all(x[k] for k in T - {i, j})
                                                    for T in by_pair.get((i, j), []))}
            assert len(inter) <= 3 * codeg ** 2  # Step 4
            for w in i:  # Step 3: star at w, i = wa
                a = next(iter(i - {w}))
                star = {j for j in inter if w in j}
                assert len(star) <= len(N[a] - {w})


def check_map():
    # T_T f = sum_i f(e_i) - 5 f(0) equals f(1^6) on affine f, and the query error formula.
    for _ in range(50):
        c0, cs = random.random(), [random.random() for _ in range(6)]
        f = lambda bits: c0 + sum(c * b for c, b in zip(cs, bits))
        unit = lambda i: [1 if k == i else 0 for k in range(6)]
        val = sum(f(unit(i)) for i in range(6)) - 5 * f([0] * 6)
        assert abs(val - f([1] * 6)) < 1e-9


def check_exponents():
    # alpha ~ n^{-4} (n R/p + n^3 p/R^2), R = (np)^{2/3}, p = n^{-a}.
    a = Fr(2, 5)
    r = Fr(2, 3) * (1 - a)
    t1 = 1 + r + a - 4
    t2 = 3 - a - 2 * r - 4
    assert t1 == t2 == Fr(-11, 5)
    assert 2 + (-r) - 4 < t1  # n^2/R is smaller
    assert Fr(7, 6) - a / 6 == Fr(11, 10)
    # planting: n^2 p^5 and n p^3 bounded at p = n^{-2/5}
    assert 2 - 5 * a == 0 and 1 - 3 * a < 0
    # kappa ~ n p^2 below R ~ (np)^{2/3}
    assert 1 - 2 * a < r


if __name__ == "__main__":
    rng = random.Random(1)
    for n in range(1, 6):
        check_multiplicities(n)
    for n in (3, 4):
        check_interactions(n, 0.6, 5, rng)
    check_map()
    check_exponents()
    print("all checks passed")
