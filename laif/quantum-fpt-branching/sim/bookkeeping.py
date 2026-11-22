"""Brute-force checks of the bookkeeping of the golden-ratio Cluster Editing algorithm, with V(G) = opt(G) + z(G)/2.

Weights: s > 0 edge, s < 0 non-edge, s = 0 zero-edge, s = None forbidden (never inside one cluster). opt is the
minimum over all partitions of the cost (cut edges cost s, non-edges inside a cluster cost -s).
1. Branching on an edge uv: V(G) = min(s(uv) + V(G with uv forbidden), c + V(G with u, v merged)), where c is the
   parameter decrease of the merge by the local rules: joining uw, vw of opposite signs costs min(|s(uw)|, |s(vw)|),
   minus 1/2 if the joined pair is a zero-edge; joining with a forbidden pair costs the other weight if it is an edge;
   every zero-edge among uw, vw releases 1/2 (two zero-edges joined into one release 1/2 net).
2. Removing a component C of the type graph whose pairs are all edges: V(G) = V(G - C) + z(C, G - C)/2.
3. Cash-in leaf: if the type graph is a disjoint union of cliques of edges, V(G) = z(G)/2.
4. Polynomial cases of Lemma 5 of the source, on random weights with zero-edges: Kq * (K1 + K1), opt = min(-s(uv),
   minimum u-v cut); and Kq * H for H in {C5, 3K1, 2K2} with weight 1 between Kq and H and the clique cost above the
   optimum, opt = the best partition of H with Kq joined to a largest cluster.
"""
import itertools, random
from fractions import Fraction as F
INF = float("inf")

def partitions(xs):
    if not xs:
        yield []; return
    a, rest = xs[0], xs[1:]
    for p in partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[a] + p[i]] + p[i + 1:]
        yield [[a]] + p

def g(s, u, v):
    return s[frozenset((u, v))]

def cost_of(vs, s, p):
    cl = {v: i for i, b in enumerate(p) for v in b}
    c = 0
    for u, v in itertools.combinations(vs, 2):
        w = g(s, u, v)
        if w is None:
            if cl[u] == cl[v]:
                return INF
        elif w > 0 and cl[u] != cl[v]:
            c += w
        elif w < 0 and cl[u] == cl[v]:
            c -= w
    return c

def opt(vs, s):
    return min(cost_of(vs, s, p) for p in partitions(list(vs)))

def zcount(vs, s):
    return sum(1 for u, v in itertools.combinations(vs, 2) if g(s, u, v) == 0)

def V(vs, s):
    o = opt(vs, s)
    return INF if o == INF else o + F(zcount(vs, s), 2)

def join(a, b):
    """Weight of the joined pair and the parameter decrease of the join."""
    if a is None or b is None:
        other = b if a is None else a
        dec = (other if other is not None and other > 0 else 0) + (F(1, 2) if other == 0 else 0)
        return None, dec
    w = a + b
    dec = F(0)
    if (a > 0 and b < 0) or (a < 0 and b > 0):
        dec += min(abs(a), abs(b))
        if w == 0:
            dec -= F(1, 2)
    zeros = (a == 0) + (b == 0)
    dec += F(zeros, 2) - (F(1, 2) if (w == 0 and zeros) else 0)
    return w, dec

def merge(vs, s, u, v, new):
    rest = [w for w in vs if w not in (u, v)]
    t = {frozenset((a, b)): g(s, a, b) for a, b in itertools.combinations(rest, 2)}
    c = F(0)
    for w in rest:
        jw, d = join(g(s, u, w), g(s, v, w))
        t[frozenset((new, w))] = jw; c += d
    return rest + [new], t, c

def type_components(vs, s):
    comps, seen = [], set()
    for a in vs:
        if a in seen:
            continue
        comp, st = [a], [a]; seen.add(a)
        while st:
            x = st.pop()
            for y in vs:
                if y not in seen and (g(s, x, y) or 0) > 0 and g(s, x, y) is not None:
                    seen.add(y); comp.append(y); st.append(y)
        comps.append(comp)
    return comps

def rand_inst(n, zero=0.2, forb=0.08):
    s = {}
    for a, b in itertools.combinations(range(n), 2):
        r = random.random()
        s[frozenset((a, b))] = None if r < forb else 0 if r < forb + zero else random.choice((-3, -2, -1, -1, 1, 1, 2, 3))
    return s

random.seed(5)
nb = nl = nc = 0
for _ in range(1500):
    n = random.randint(2, 6); vs = list(range(n)); s = rand_inst(n)
    v0 = V(vs, s)
    for u, v in itertools.combinations(vs, 2):          # 1. every edge as branching edge
        w = g(s, u, v)
        if w is None or w <= 0:
            continue
        sf = dict(s); sf[frozenset((u, v))] = None
        mv, ms, c = merge(vs, s, u, v, n)
        assert v0 == min(w + V(vs, sf), c + V(mv, ms)), (s, u, v)
        nb += 1
    for C in type_components(vs, s):                    # 2. clique components
        if all((g(s, a, b) or 0) > 0 and g(s, a, b) is not None for a, b in itertools.combinations(C, 2)):
            R = [x for x in vs if x not in C]
            zc = sum(1 for a in C for b in R if g(s, a, b) == 0)
            assert v0 == (V(R, s) if R else 0) + F(zc, 2), (s, C)
            nc += 1
    if all(all((g(s, a, b) or 0) > 0 and g(s, a, b) is not None for a, b in itertools.combinations(C, 2))
           for C in type_components(vs, s)):            # 3. cash-in leaf
        assert v0 == F(zcount(vs, s), 2), s
        nl += 1
print(f"bookkeeping: {nb} edge branchings, {nc} clique removals, {nl} cash-in leaves agree with V by brute force")

def mincut(vs, s, a, b):
    best = INF
    rest = [x for x in vs if x not in (a, b)]
    for bits in itertools.product((0, 1), repeat=len(rest)):
        X = {a} | {x for x, t in zip(rest, bits) if t == 0}
        best = min(best, sum(g(s, x, y) for x in X for y in vs if y not in X and (g(s, x, y) or 0) > 0))
    return best

n4 = 0
for _ in range(600):                                    # 4a. Kq * (K1 + K1)
    q = random.randint(1, 4); vs = list(range(q + 2)); u, v = q, q + 1
    s = {frozenset(p): random.randint(1, 3) for p in itertools.combinations(vs, 2)}
    s[frozenset((u, v))] = random.choice((0, -1, -2, -3))
    assert opt(vs, s) == min(-s[frozenset((u, v))], mincut(vs, s, u, v)), s
    n4 += 1
HS = {"C5": (5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]), "3K1": (3, []), "2K2": (4, [(0, 1), (2, 3)])}
for name, (h, E) in HS.items():                         # 4b. Kq * H
    for _ in range(150):
        q = random.randint(1, 6 - h if h < 6 else 1) if h < 6 else 1
        vs = list(range(q + h)); Hv = list(range(q, q + h)); Kv = list(range(q))
        s = {}
        for a, b in itertools.combinations(vs, 2):
            if a in Kv and b in Kv:
                s[frozenset((a, b))] = random.randint(1, 3)
            elif a in Kv or b in Kv:
                s[frozenset((a, b))] = 1
            else:
                inH = (a - q, b - q) in E or (b - q, a - q) in E
                s[frozenset((a, b))] = random.randint(1, 3) if inH else random.choice((0, -1, -2))
        clique = sum(-w for w in s.values() if w < 0)
        o = opt(vs, s)
        if clique <= o:
            continue                                    # the source first tests the clique, so this case is excluded
        best = INF
        for p in partitions(Hv):
            m = max(len(b) for b in p)
            for i, b in enumerate(p):
                if len(b) == m:
                    pp = [list(x) for x in p]; pp[i] = pp[i] + Kv
                    best = min(best, cost_of(vs, s, pp))
        assert o == best, (name, s)
        n4 += 1
print(f"Lemma 5 polynomial cases with zero-edges: {n4} instances agree with brute force")
print("all checks passed")
