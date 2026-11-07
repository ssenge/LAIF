"""Checks for the extension-count lower bounds (README, Theorems 1 and 2).

With p = n^-theta, a rooted pattern (S, R, F) has
    eps(theta) = max over R <= U <= S of |S - U| - theta |F - F[U]|,
the exponent of the largest expected partial derivative of its extension count.
1. theta_star(H) evaluates the conditions of Theorem 2 by brute force: (P), the star
   condition eps < 2/3 + theta/3 and the interaction condition eps < theta, each
   minimised over induced patterns S. It also checks that every condition that is
   tight at theta* has a safe pattern, so that the bound holds at theta* itself.
2. Known cases: C3, C4, K4, K5 reproduce 13/12, 19/18, 11/10, 10/9.
3. K_{a,b}: brute force for a + b <= 8 and a type-based computation for b <= 30
   agree with the closed form of Theorem 1.
4. Octahedron: theta* = 2/5.
5. Comparison with beta_r of [2, (68)].
"""
import itertools
from fractions import Fraction as Fr


def subsets(xs):
    xs = list(xs)
    for k in range(len(xs) + 1):
        yield from itertools.combinations(xs, k)


def threshold(terms, g0, g1):
    """Smallest theta >= 0 with c - theta f <= g0 - theta g1 for all (c, f)."""
    t = Fr(0)
    for c, f in terms:
        a, b = c - g0, f - g1
        if b > 0:
            t = max(t, Fr(a) / b)
        elif a > 0:
            return Fr(10 ** 9)
    return t


def eps_terms(S, root, F):
    X = [x for x in S if x not in root]
    out = []
    for Sig in subsets(X):
        U = set(root) | set(Sig)
        out.append((len(X) - len(Sig), len(F) - sum(1 for a, b in F if a in U and b in U)))
    return out


def safe(S, root, F, th):
    X = [x for x in S if x not in root]
    for Sig in subsets(X):
        if Sig:
            U = set(root) | set(Sig)
            if len(Sig) - th * sum(1 for a, b in F if a in U and b in U) <= 0:
                return False
    return True


def patterns(v, E):
    """Yield (kind, list of (S, root, F)) for every star and interaction condition."""
    adj = {x: set() for x in range(v)}
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    for x in range(v):
        Fx = [f for f in E if x not in f]
        for y in adj[x]:
            for z in adj[x] - {y}:
                others = [t for t in range(v) if t not in (x, y, z)]
                yield 'S', [({y, z, *ex}, (y,), [f for f in Fx if set(f) <= {y, z, *ex}]) for ex in subsets(others)]
    for i in E:
        for j in E:
            if i != j:
                base = set(i) | set(j)
                others = [t for t in range(v) if t not in base]
                yield 'I', [(base | set(ex), i, [f for f in E if f not in (i, j) and set(f) <= base | set(ex)])
                            for ex in subsets(others)]


GOAL = {'S': (Fr(2, 3), Fr(-1, 3)), 'I': (Fr(0), Fr(-1))}


def theta_star(v, E):
    E = [tuple(sorted(e)) for e in E]
    e = len(E)
    tP = max(Fr(v - j, e - max(sum(1 for a, b in E if a in J and b in J)
                               for J in map(set, itertools.combinations(range(v), j))))
             for j in range(2, v))
    conds = [(kind, [(threshold(eps_terms(*P), *GOAL[kind]), P) for P in Ps]) for kind, Ps in patterns(v, E)]
    th = max([tP] + [min(t for t, _ in c) for _, c in conds])
    for kind, c in conds:  # tight conditions need a safe pattern
        if min(t for t, _ in c) == th:
            assert any(safe(*P, th) for t, P in c if t == th), (v, E, kind)
    return th


def Kab(a, b):
    return a + b, [(i, a + j) for i in range(a) for j in range(b)]


def closed(a, b):
    tP = Fr(a + b - 2, a * b - 1)
    return max(tP, Fr(3 * a + 3 * b - 8, 3 * (a - 1) * b + 1) if a >= 3 else Fr(4, 7))


def kab_types(a, b):
    """theta* of K_{a,b} with star patterns grouped by type; (I) via the Remark."""
    tP = max(Fr(a + b - x - y, a * b - x * y) for x in range(1, a + 1) for y in range(1, b + 1) if (x, y) != (a, b))
    th = tP
    for A, B in ((a, b), (b, a)):  # w in the side of size A, so y, z in the side of size B
        best = None
        for sA in range(A):
            for sB in range(B - 1):  # S: sA vertices of A - x, y, z and sB more of B
                terms = [(wA + wB, wA * (sB + 2) + wB * sA - wA * wB) for wA in (0, sA) for wB in (0, sB + 1)]
                t = threshold(terms, *GOAL['S'])  # bilinear in (wA, wB): corners suffice
                best = t if best is None else min(best, t)
        th = max(th, best)
    return th


def beta(r):
    return max(Fr(2 * h * r, (h + 1) * (r + h)) * (1 - Fr(h - 1, r) + Fr(h - 1, 2 * r * r)) for h in range(2, r))


if __name__ == "__main__":
    cyc = lambda k: (k, [(t, (t + 1) % k) for t in range(k)])
    cliq = lambda k: (k, list(itertools.combinations(range(k), 2)))
    for H, x in [(cyc(3), Fr(13, 12)), (cyc(4), Fr(19, 18)), (cliq(4), Fr(11, 10)), (cliq(5), Fr(10, 9))]:
        assert Fr(7, 6) - theta_star(*H) / 6 == x
    for a in range(2, 5):
        for b in range(a, 9 - a):
            assert theta_star(*Kab(a, b)) == closed(a, b), (a, b)
    for a in range(2, 31):
        for b in range(a, 31):
            assert kab_types(a, b) == closed(a, b), (a, b)
            if a >= 3:  # star bound dominates planting, and theta (a - 1) >= 1
                t = closed(a, b)
                assert t > Fr(a + b - 2, a * b - 1) and t * (a - 1) >= 1
    octa = [(a, b) for a, b in itertools.combinations(range(6), 2) if b != a + 3]
    assert theta_star(6, octa) == Fr(2, 5)
    print("K_{r,r}: r, exponent, beta_r of [2]")
    for r in range(3, 21):
        x = Fr(7, 6) - closed(r, r) / 6
        assert x == Fr(7, 6) - Fr(3 * r - 4, 3 * (3 * r * r - 3 * r + 1))
        assert (x > beta(r)) == (r <= 18)
        print(r, x, round(float(x), 4), round(float(beta(r)), 4))
    assert beta(10) == Fr(181, 180)
    print("all checks passed")
