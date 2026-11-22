"""Checks for the split step of Cluster Editing (Theorem 4).

Weighted instances as in the golden-ratio algorithm: s(uv) > 0 edge, s(uv) < 0 non-edge, s(uv) = 0 zero-edge. The type graph
has the edges s > 0. A node (G, k) of that algorithm answers yes iff V(G) <= k, with V(G) = opt(G) + z(G)/2, opt the
minimum modification cost and z the number of zero-edges (each zero-edge carries 1/2 in the bookkeeping).
1. Brute force on random weighted graphs: V(G) = V(H) + V(G - H) + z(H, G - H)/2 for a component H of the type graph,
   V(H) >= 1/2 when H is not a clique of positive pairs, and the split step decides V(G) <= k.
2. Exact: the leaf count of the split step, 2 * sum_{i in {1/2, 1, .., K}} phi^i + phi^(k - 1/2) <= phi^k for k >= K0,
   with 2K <= k, via x = phi^(1/2) > 1.272: 2 x^(1-2k+2K)/(x-1) + 1/x <= 1, the left side decreasing in k.
3. Bases: sqrt(phi) <= 1.2721 and sqrt(1.76) <= 1.3267, exactly.
"""
import itertools, random
from fractions import Fraction as F

def partitions(xs):
    if not xs:
        yield []; return
    a, rest = xs[0], xs[1:]
    for p in partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[a] + p[i]] + p[i + 1:]
        yield [[a]] + p

def V(vs, s):
    vs = list(vs)
    z = sum(1 for u, v in itertools.combinations(vs, 2) if s[u, v] == 0)
    best = None
    for p in partitions(vs):
        cl = {v: i for i, b in enumerate(p) for v in b}
        c = sum(s[u, v] if cl[u] != cl[v] else -s[u, v]
                for u, v in itertools.combinations(vs, 2) if (s[u, v] > 0) == (cl[u] != cl[v]) and s[u, v] != 0)
        best = c if best is None else min(best, c)
    return best + F(z, 2)

def components(vs, s):
    vs, comps, seen = list(vs), [], set()
    for a in vs:
        if a in seen:
            continue
        comp, st = [a], [a]; seen.add(a)
        while st:
            x = st.pop()
            for y in vs:
                if y not in seen and s[x, y] > 0:
                    seen.add(y); comp.append(y); st.append(y)
        comps.append(comp)
    return comps

def split_decides(vs, s, k):
    """The split step on the first component H, with exact value oracles."""
    cs = components(vs, s)
    H = cs[0]; R = [v for v in vs if v not in H]
    zc = sum(1 for u in H for v in R if s[u, v] == 0)
    kt = k - F(zc, 2)
    K = F(int(kt), 2) if kt >= 0 else F(-1)       # largest half-integer <= kt/2
    halves = [F(i, 2) for i in range(0, int(2 * K) + 1)]
    vH, vR = V(H, s), V(R, s)
    for i in halves:                               # value calls on H
        if vH <= i:
            return vR <= kt - i                   # tail call on G - H
    for i in halves:                               # value calls on G - H
        if vR <= i:
            return vH <= kt - i                   # tail call on H
    return False

random.seed(11)
tests = 0
for _ in range(400):
    n = random.randint(2, 7)
    s = {}
    for u, v in itertools.combinations(range(n), 2):
        s[u, v] = s[v, u] = random.choice((-2, -1, -1, 0, 1, 1, 2)) if random.random() < 0.6 else random.choice((-1, -2))
    vs = list(range(n))
    cs = components(vs, s)
    for H in cs:
        clique = all(s[u, v] > 0 for u, v in itertools.combinations(H, 2))
        assert (V(H, s) == 0) == clique and (clique or V(H, s) >= F(1, 2)), (H, s)
    if len(cs) >= 2:
        H = cs[0]; R = [v for v in vs if v not in H]
        zc = sum(1 for u in H for v in R if s[u, v] == 0)
        assert V(vs, s) == V(H, s) + V(R, s) + F(zc, 2), s
        for k2 in range(0, 2 * int(V(vs, s)) + 6):
            k = F(k2, 2)
            assert split_decides(vs, s, k) == (V(vs, s) <= k), (s, k)
        tests += 1
print(f"additivity over type-graph components and the split step: {tests} disconnected random weighted graphs, n <= 7")

X_LO = F(1272, 1000)                               # 1.272^2 < phi
assert X_LO ** 2 < F(16180339887, 10 ** 10)
def lhs(k):                                        # with 2K <= k, i.e. exponent 1 - 2k + 2K <= 1 - k
    return 2 * X_LO ** (1 - k) / (X_LO - 1) + 1 / X_LO
K0 = next(k for k in range(1, 200) if lhs(k) <= 1)
assert lhs(K0) <= 1
print(f"split leaf count <= phi^k for every k >= {K0}")

PHI_UP = F(16180339888, 10 ** 10)
assert F(12721, 10 ** 4) ** 2 >= PHI_UP and F(13267, 10 ** 4) ** 2 >= F(176, 100)
print("bases: sqrt(phi) <= 1.2721, sqrt(1.76) <= 1.3267")
print("all checks passed")
