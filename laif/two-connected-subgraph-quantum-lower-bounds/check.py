"""Checks for the lower bound for 2-connected patterns H.

1. Over all 2-connected graphs H on 3..6 vertices (by brute force):
   - planting: for every overlap size 2 <= j <= v-1, the edges of H with an
     endpoint outside any j-set number at least v-j+1, so
     (v-j)/(e - e_max(j)) <= (v-2)/(v-1);
   - star: H - x is connected for every vertex x;
   - interaction: for distinct edges i, j, every component of H - {i, j}
     contains an endpoint of i.
2. On random H-free subgraphs of a host (C4, C6 in K_{n,n}; K4 in K_{n,n,n,n}):
   the number of edges j interacting with an edge i, and the interaction count
   inside a star, are at most v! * D^(v-2), with D the maximum degree of the
   relevant graph. (Sampled inputs only: the sampler deletes one edge from
   each present copy, which does not sample the conditioned distribution.)
3. Exponent arithmetic with exact fractions.
4. The block reduction, on small graphs H with a chosen block B: attach to
   every vertex of a B-free graph G a private copy of H - E(B) with the
   vertices of B identified. Then H is not a subgraph of the result. A copy
   would split H into a B-free connected part H_G and pendants P_i at
   distinct vertices u_i, each embedding into the gadget with u_i at the
   root; the check enumerates all such splits.
"""
import itertools
import random
from fractions import Fraction as Fr
from math import factorial


def connected(vs, es):
    vs = set(vs)
    if not vs:
        return True
    adj = {x: set() for x in vs}
    for a, b in es:
        if a in vs and b in vs:
            adj[a].add(b)
            adj[b].add(a)
    start = next(iter(vs))
    seen, stack = {start}, [start]
    while stack:
        for y in adj[stack.pop()] - seen:
            seen.add(y)
            stack.append(y)
    return seen == vs


def two_connected(v, es):
    return v >= 3 and connected(range(v), es) and all(
        connected(set(range(v)) - {x}, [e for e in es if x not in e]) for x in range(v))


def check_structure(v, es):
    e = len(es)
    for j in range(2, v):
        emax = max(sum(1 for a, b in es if a in S and b in S)
                   for S in map(set, itertools.combinations(range(v), j)))
        assert e - emax >= v - j + 1
        assert Fr(v - j, e - emax) <= Fr(v - 2, v - 1)
    for i, j in itertools.permutations(es, 2):
        rest = [f for f in es if f not in (i, j)]
        adj = {x: set() for x in range(v)}
        for a, b in rest:
            adj[a].add(b)
            adj[b].add(a)
        seen, stack = set(i), list(i)
        while stack:
            for y in adj[stack.pop()] - seen:
                seen.add(y)
                stack.append(y)
        assert seen == set(range(v)), (v, es, i, j)


def all_two_connected(vmax):
    count = 0
    for v in range(3, vmax + 1):
        pairs = list(itertools.combinations(range(v), 2))
        for mask in range(1, 1 << len(pairs)):
            es = [pairs[t] for t in range(len(pairs)) if mask >> t & 1]
            if two_connected(v, es):
                check_structure(v, es)
                count += 1
    return count


def copies(pattern_edges, v, host_adj):
    """Edge sets of all copies of the pattern in the host graph."""
    out = set()
    hv = sorted(host_adj)
    for phi in itertools.permutations(hv, v):
        if all(phi[b] in host_adj[phi[a]] for a, b in pattern_edges):
            out.add(frozenset(frozenset((phi[a], phi[b])) for a, b in pattern_edges))
    return list(out)


def check_interactions(pattern_edges, v, host_adj, p, trials, rng):
    E = sorted({frozenset((a, b)) for a in host_adj for b in host_adj[a]}, key=sorted)
    K = copies(pattern_edges, v, host_adj)
    by_edge = {}
    for T in K:
        for i in T:
            by_edge.setdefault(i, []).append(T)
    bound = factorial(v)
    for _ in range(trials):
        x = {e: rng.random() < p for e in E}
        for T in K:
            if all(x[i] for i in T):
                x[rng.choice(sorted(T, key=sorted))] = False
        assert not any(all(x[i] for i in T) for T in K)
        deg = {a: sum(x[frozenset((a, b))] for b in host_adj[a]) for a in host_adj}
        D = max(deg.values())
        for i in E:
            inter = {j for T in by_edge.get(i, []) for j in T - {i}
                     if all(x[c] for c in T - {i, j})}
            assert len(inter) <= bound * D ** (v - 2)
            for w in i:  # star at w: only edges outside the star must be present
                a = next(iter(i - {w}))
                star = {j for T in by_edge.get(i, []) for j in T - {i}
                        if w in j and all(x[c] for c in T - {i, j} if w not in c)}
                Dout = max(sum(x[frozenset((s, t))] for t in host_adj[s] if t != w)
                           for s in host_adj if s != w)
                assert len(star) <= bound * Dout ** (v - 2)


def bipartite_host(n):
    L = [("L", t) for t in range(n)]
    R = [("R", t) for t in range(n)]
    adj = {a: set(R) for a in L}
    adj.update({b: set(L) for b in R})
    return adj


def complete_multipartite_host(k, n):
    V = [(a, t) for a in range(k) for t in range(n)]
    return {x: {y for y in V if y[0] != x[0]} for x in V}


def embeds(pv, pe, adj, root=None):
    """Injective homomorphism of the graph (pv, pe) into adj; root = (u, x) pins u to x."""
    padj = {a: set() for a in pv}
    for a, b in pe:
        padj[a].add(b)
        padj[b].add(a)
    order, seen = [], set()
    for s0 in ([root[0]] if root else []) + sorted(pv, key=lambda a: -len(padj[a])):
        if s0 in seen:
            continue
        seen.add(s0)
        queue = [s0]
        while queue:
            z = queue.pop(0)
            order.append(z)
            for y in padj[z] - seen:
                seen.add(y)
                queue.append(y)
    phi = {}

    def rec(k):
        if k == len(order):
            return True
        z = order[k]
        done = [phi[y] for y in padj[z] if y in phi]
        if root and z == root[0]:
            cands = {root[1]}
        elif done:
            cands = set.intersection(*(adj[t] for t in done))
        else:
            cands = set(adj)
        for c in cands - set(phi.values()):
            phi[z] = c
            if rec(k + 1):
                return True
            del phi[z]
        return False
    return rec(0)


def components(vs, adj):
    vs, out = set(vs), []
    while vs:
        comp = {vs.pop()}
        stack = list(comp)
        while stack:
            for y in adj[stack.pop()] & vs:
                vs.discard(y)
                comp.add(y)
                stack.append(y)
        out.append(comp)
    return out


def check_block_reduction(n, es, bes):
    """No split of H into a B-free part and pendants that fit the gadget."""
    adj = {a: set() for a in range(n)}
    for a, b in es:
        adj[a].add(b)
        adj[b].add(a)
    bv = {a for e in bes for a in e}
    root = min(bv)
    rel = {a: root if a in bv else a for a in range(n)}
    gadget = {rel[a]: set() for a in range(n)}
    for a, b in es:
        if (a, b) not in bes and (b, a) not in bes:
            gadget[rel[a]].add(rel[b])
            gadget[rel[b]].add(rel[a])
    pendants = []
    for u in range(n):
        comps = components(set(range(n)) - {u}, adj)
        for k in range(1, len(comps) + 1):
            for pick in itertools.combinations(comps, k):
                body = set().union(*pick)
                pv = body | {u}
                pe = [e for e in es if e[0] in pv and e[1] in pv]
                if embeds(pv, pe, gadget, (u, root)):
                    pendants.append((u, frozenset(body)))
    splits = 0
    for r in range(1, len(pendants) + 1):
        for fam in itertools.combinations(pendants, r):
            roots = {u for u, _ in fam}
            bodies = [b for _, b in fam]
            union = set().union(*bodies)
            if len(roots) < r or sum(map(len, bodies)) > len(union) or roots & union:
                continue
            rest = set(range(n)) - union
            rest_adj = {a: adj[a] & rest for a in rest}
            assert embeds(bv, list(bes), rest_adj), (es, fam)
            splits += 1
    assert splits > 0  # the search is not vacuous


def shift(es, k):
    return [(a + k, b + k) for a, b in es]


def check_block_examples():
    C4 = [(0, 1), (1, 2), (2, 3), (3, 0)]
    # two C4 sharing a vertex, condition (a)
    n, es = 7, sorted({tuple(sorted(e)) for e in C4 + [(0, 4), (4, 5), (5, 6), (6, 0)]})
    check_block_reduction(n, es, {(0, 1), (1, 2), (2, 3), (0, 3)})
    # C4, a path of length 2, C4, condition (a)
    es = sorted({tuple(sorted(e)) for e in C4 + [(0, 4), (4, 5)] + shift(C4, 5)})
    check_block_reduction(9, es, {(0, 1), (1, 2), (2, 3), (0, 3)})
    # chain of three C4 sharing vertices, middle block, condition (b)
    es = sorted({tuple(sorted(e)) for e in C4 + shift(C4, 3) + shift(C4, 6)})
    check_block_reduction(10, es, {(3, 4), (4, 5), (5, 6), (3, 6)})
    # K_{2,3} and C4 sharing a vertex, condition (a)
    K23 = [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]
    es = sorted({tuple(sorted(e)) for e in K23 + [(4, 5), (5, 6), (6, 7), (7, 4)]})
    check_block_reduction(8, es, {tuple(sorted(e)) for e in K23})
    # C6 with a pendant path, condition (a)
    C6 = [(t, (t + 1) % 6) for t in range(6)]
    es = sorted({tuple(sorted(e)) for e in C6 + [(0, 6), (6, 7)]})
    check_block_reduction(8, es, {tuple(sorted(e)) for e in C6})
    # k four-cycles sharing one vertex, condition (c)
    for k in (3, 4):
        es = sorted({tuple(sorted(e)) for i in range(k)
                     for e in [(0, 3 * i + 1), (3 * i + 1, 3 * i + 2), (3 * i + 2, 3 * i + 3), (3 * i + 3, 0)]})
        check_block_reduction(3 * k + 1, es, {(0, 1), (1, 2), (2, 3), (0, 3)})
    # two windmills of four-cycles joined by a path, condition (d)
    for w1, w2, L in [(2, 2, 1), (2, 2, 2), (3, 2, 1), (2, 2, 3)]:
        left = [e for i in range(w1) for e in [(0, 3 * i + 1), (3 * i + 1, 3 * i + 2), (3 * i + 2, 3 * i + 3), (3 * i + 3, 0)]]
        a = 3 * w1 + 1
        path = [(0, a)] + [(a + t, a + t + 1) for t in range(L - 1)]
        rc = a + L - 1
        right = [e for i in range(w2) for e in [(rc, rc + 3 * i + 1), (rc + 3 * i + 1, rc + 3 * i + 2),
                                                 (rc + 3 * i + 2, rc + 3 * i + 3), (rc + 3 * i + 3, rc)]]
        es = sorted({tuple(sorted(e)) for e in left + path + right})
        check_block_reduction(rc + 3 * w2 + 1, es, {(0, 1), (1, 2), (2, 3), (0, 3)})


def check_exponents():
    for v in range(3, 13):
        theta = Fr(v - 2, v - 1)
        for j in range(2, v):  # planting: n^{v-j} p^{v-j+1}
            assert (v - j) - theta * (v - j + 1) == Fr(2 - j, v - 1) <= 0
        assert (v - 2) - theta * (v - 1) == 0  # p * (np)^{v-2} = O(1)
        r = Fr(2, 3) * (1 - theta)  # R = (np)^{2/3}
        assert r + theta - 3 == 2 - theta - 2 * r - 3  # R/p balances n^2 p/R^2
        assert Fr(7, 6) - theta / 6 == 1 + Fr(1, 6 * (v - 1))
    assert 1 + Fr(1, 12) == Fr(13, 12) and 1 + Fr(1, 18) == Fr(19, 18)


def check_disjoint_unions(rng, trials=40):
    """Corollary 4: C is a component of H with a cycle and the most edges, t copies of it in H. For random C-free
    hosts G, the union of G with a disjoint copy of H minus one copy of C contains no copy of H; with a copy of C added
    to G, it does."""
    C4 = [(0, 1), (1, 2), (2, 3), (3, 0)]
    C6 = [(t, (t + 1) % 6) for t in range(6)]
    P5 = [(t, t + 1) for t in range(4)]
    K23 = [(a, b) for a in range(2) for b in range(2, 5)]
    W2 = C4 + [(0, 4), (4, 5), (5, 6), (6, 0)]                       # two four-cycles sharing a vertex
    P8 = [(t, t + 1) for t in range(7)]                              # a tree component with more edges than C
    cases = [[C4, C4], [C4, C6], [C4, P5], [C4, P8], [C6, C6, C4], [K23, C4, C4], [W2, C4], [C4, C4, C4, P5]]

    def union(parts):
        es, off = [], 0
        for part in parts:
            k = 1 + max(max(e) for e in part)
            es += shift(part, off)
            off += k
        return off, es

    def adj_of(nv, es):
        adj = {x: set() for x in range(nv)}
        for a, b in es:
            adj[a].add(b)
            adj[b].add(a)
        return adj

    for parts in cases:
        cyc = [q for q in parts if len(q) >= 1 + max(max(e) for e in q)]   # connected with a cycle: edges >= vertices
        big = max(len(q) for q in cyc)
        C = next(q for q in cyc if len(q) == big)
        rest = list(parts)
        rest.remove(C)
        hv, he = union(parts)
        cv = 1 + max(max(e) for e in C)
        done = 0
        while done < trials:
            n = rng.randint(6, 9)
            gp = rng.choice([0.3, 0.45, 0.6])
            ges = [e for e in itertools.combinations(range(n), 2) if rng.random() < gp]
            if embeds(range(cv), C, adj_of(n, ges)):
                continue
            rv, res = union(rest) if rest else (0, [])
            tot = n + rv
            allE = ges + shift(res, n)
            assert not embeds(range(hv), he, adj_of(tot, allE)), ("disjoint union", parts)
            planted = allE + shift(C, tot)
            assert embeds(range(hv), he, adj_of(tot + cv, planted)), ("planted", parts)
            done += 1
    return len(cases)


if __name__ == "__main__":
    rng = random.Random(1)
    print("2-connected graphs checked:", all_two_connected(6))
    C4 = [(0, 1), (1, 2), (2, 3), (3, 0)]
    C6 = [(t, (t + 1) % 6) for t in range(6)]
    K4 = list(itertools.combinations(range(4), 2))
    check_interactions(C4, 4, bipartite_host(3), 0.5, 3, rng)
    check_interactions(C4, 4, bipartite_host(4), 0.4, 2, rng)
    check_interactions(C6, 6, bipartite_host(3), 0.6, 2, rng)
    check_interactions(K4, 4, complete_multipartite_host(4, 2), 0.7, 3, rng)
    check_exponents()
    check_block_examples()
    print("disjoint unions checked:", check_disjoint_unions(rng))
    print("all checks passed")
