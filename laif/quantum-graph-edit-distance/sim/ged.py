"""Checks for the quantum separator recursion for Graph Edit Distance (Theorem 1).

1. The decomposition that the nested quantum minimum finding evaluates: for a separator S of G[V'] with
   G[V'] - S = G[V1] + G[V2] (no edges between V1 and V2),
       R(V', W', c) = min over injections psi: S -> W' and bipartitions W1 + W2 = W' - psi(S), |W1| = |V1|, of
                      c_S(psi) + R(V1, W1, c^psi) + R(V2, W2, c^psi) + insertion cost of the H-edges between W1 and W2,
   where c^psi(v, w) = c(v, w) + sum over s in S of c_E({s, v}, {psi(s), w}) absorbs the edges at the separator.
   It is compared with brute force over all bijections on random small instances (G a path, tree, ladder,
   cycle or sparse graph, H arbitrary, random reasonable costs).
2. The exponents: the classical count 2^{n_i} n_i^{s(n_i)} per level and the quantum square root of it,
   summed over the levels n_i = alpha^i n, give 2^{n/(1 - alpha)} and 2^{n/(2(1 - alpha))} up to 2^{o(n)}.
3. The classical exponential-space comparison: a dynamic program over a vertex order of G whose states are the
   images of the frontier (placed vertices with a later neighbour) and the set of used images, in time and space
   2^n n^{O(frontier)}, equals brute force on the same families.
Run: python ged.py
"""
import itertools, random
from fractions import Fraction
from math import log2, comb

random.seed(7)


def instance(n, kind):
    V = list(range(n))
    if kind == "path": E = {frozenset((i, i + 1)) for i in range(n - 1)}
    elif kind == "cycle": E = {frozenset((i, (i + 1) % n)) for i in range(n)} if n >= 3 else set()
    elif kind == "tree": E = {frozenset((i, random.randrange(i))) for i in range(1, n)}
    elif kind == "ladder":
        w = 2; E = {frozenset((i, i + 1)) for i in range(n - 1) if (i + 1) % w} | {frozenset((i, i + w)) for i in range(n - w)}
    else: E = {frozenset(p) for p in itertools.combinations(V, 2) if random.random() < 0.3}
    F = {frozenset(p) for p in itertools.combinations(V, 2) if random.random() < 0.5}
    cV = {(v, w): random.randint(0, 5) for v in V for w in V}
    dele = {e: random.randint(1, 4) for e in E}
    ins = {f: random.randint(1, 4) for f in F}
    sub = {(e, f): random.randint(0, dele[e] + ins[f]) for e in E for f in F}   # reasonable: sub <= del + ins

    def cE(e, f):
        if e in E and f in F: return sub[(e, f)]
        if e in E: return dele[e]
        if f in F: return ins[f]
        return 0
    return V, E, F, cV, cE, ins


def brute(V, E, F, cV, cE):
    best = None
    for p in itertools.permutations(V):
        phi = dict(zip(V, p))
        c = sum(cV[(v, phi[v])] for v in V) + sum(cE(frozenset(e), frozenset((phi[e[0]], phi[e[1]])))
                                                  for e in itertools.combinations(V, 2))
        best = c if best is None or c < best else best
    return best


def components(Vs, E):
    Vs, comps = set(Vs), []
    while Vs:
        st, comp = [Vs.pop()], set()
        while st:
            x = st.pop(); comp.add(x)
            for y in list(Vs):
                if frozenset((x, y)) in E: Vs.discard(y); st.append(y)
        comps.append(comp)
    return comps


def separator(Vs, E):
    """Smallest nonempty S whose removal leaves V1, V2 with no edges between them and |V1|, |V2| as equal as possible."""
    Vs = sorted(Vs)
    for k in range(1, len(Vs) + 1):
        best = None
        for S in itertools.combinations(Vs, k):
            rest = [v for v in Vs if v not in S]
            comps = components(rest, E)
            # split the components into two sides, as balanced as possible
            for mask in range(1 << len(comps)):
                V1 = set().union(*[c for i, c in enumerate(comps) if mask >> i & 1]) if comps else set()
                V2 = set(rest) - V1
                key = max(len(V1), len(V2))
                if best is None or key < best[0]: best = (key, set(S), V1, V2)
        if best is not None and (k >= 2 or best[0] <= max(1, (len(Vs) - 1 + 1) // 2) or k == len(Vs)):
            return best[1:]
    return set(Vs), set(), set()


def R(Vs, Ws, cv, E, F, cE, ins):
    """SR-GED recursion on G[Vs], H[Ws] with node costs cv; returns the restricted optimum."""
    Vs, Ws = sorted(Vs), sorted(Ws)
    if len(Vs) <= 1:
        return min((cv[(v, w)] for v in Vs for w in Ws), default=0)
    S, V1, V2 = separator(Vs, E)
    S = sorted(S); best = None
    for img in itertools.permutations(Ws, len(S)):
        psi = dict(zip(S, img))
        cS = sum(cv[(s, psi[s])] for s in S) + sum(cE(frozenset((a, b)), frozenset((psi[a], psi[b])))
                                                    for a, b in itertools.combinations(S, 2))
        Wr = [w for w in Ws if w not in img]
        cpsi = {(v, w): cv[(v, w)] + sum(cE(frozenset((s, v)), frozenset((psi[s], w))) for s in S)
                for v in V1 | V2 for w in Wr}
        for W1 in itertools.combinations(Wr, len(V1)):
            W2 = [w for w in Wr if w not in W1]
            cut = sum(ins.get(frozenset((a, b)), 0) for a in W1 for b in W2)
            c = cS + R(V1, W1, cpsi, E, F, cE, ins) + R(V2, W2, cpsi, E, F, cE, ins) + cut
            best = c if best is None or c < best else best
    return best


count = 0
for kind in ("path", "cycle", "tree", "ladder", "sparse"):
    for n in range(1, 8):
        for _ in range(3 if n <= 6 else 1):
            V, E, F, cV, cE, ins = instance(n, kind)
            assert R(V, V, cV, E, F, cE, ins) == brute(V, E, F, cV, cE), (kind, n)
            count += 1
print(f"decomposition equals brute-force GED on {count} instances (n <= 7)")

# 2. exponents: per level i, N_i = n_i^{s(n_i)} * C(n_i, n_{i+1}) choices; classical sum of log2 N_i, quantum half of it
for alpha in (0.51, 0.55, 0.6):
    prev = None
    for n in (10 ** 6, 10 ** 8, 10 ** 10, 10 ** 12):
        s = lambda m: 8 * m ** 0.5                   # planar separators, c_mu * s(m) = O(sqrt m), c_mu = 8 here
        ni, cl, qu = float(n), 0.0, 0.0
        while ni >= 2:
            lgN = ni + s(ni) * log2(ni)              # bipartitions <= 2^{n_i}, separator maps <= n_i^{s(n_i)}
            cl += lgN + 1                            # two recursive calls per choice
            qu += lgN / 2 + 1 + 2 * log2(n)          # square root, two calls, error reduction O(n) per level
            ni *= alpha
        excess = qu / n - 1 / (2 * (1 - alpha))          # the 2^{o(n)} part per n, shrinking as n grows
        assert prev is None or excess < prev, (alpha, n, excess); prev = excess
        assert abs(qu / cl - 0.5) < 0.05
    print(f"alpha = {alpha}: quantum base -> 2^(1/(2(1 - alpha))) = {2 ** (1 / (2 * (1 - alpha))):.4f},"
          f" classical 2^(1/(1 - alpha)) = {2 ** (1 / (1 - alpha)):.4f}")
for eps in (0.5, 0.1, 0.01):
    mu = 0.5 - 1 / (2 * log2(2 + eps / 2))           # balance 1/2 + mu with 2^{1/(2(1/2 - mu))} = 2 + eps/2
    assert 0 < mu < 0.5 and 2 ** (1 / (2 * (0.5 - mu))) < 2 + eps


def dp(V, E, F, cV, cE, ins):
    """Exponential-space dynamic program over the vertex order of V."""
    states = {((), frozenset()): 0}
    for t, v in enumerate(V):
        old = [u for u in V[:t] if any(frozenset((u, x)) in E for x in V[t:])]
        new_front = [u for u in V[:t + 1] if any(frozenset((u, x)) in E for x in V[t + 1:])]
        nxt = {}
        for (img, used), c in states.items():
            fmap = dict(zip(old, img))
            for w in V:
                if w in used: continue
                add = cV[(v, w)] + sum(cE(frozenset((u, v)), frozenset((fmap[u], w))) for u in old)
                add += sum(ins.get(frozenset((x, w)), 0) for x in used - set(img))   # no G-edge from v to these
                m = dict(fmap); m[v] = w
                key = (tuple(m[u] for u in new_front), used | {w})
                if key not in nxt or c + add < nxt[key]: nxt[key] = c + add
        states = nxt
    return min(states.values())


random.seed(11)
cnt = 0
for kind in ("path", "cycle", "tree", "ladder", "sparse"):
    for n in range(1, 8):
        V, E, F, cV, cE, ins = instance(n, kind)
        assert dp(V, E, F, cV, cE, ins) == brute(V, E, F, cV, cE), (kind, n); cnt += 1
print(f"exponential-space dynamic program equals brute force on {cnt} instances")
print("all checks passed")
