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
    print("all checks passed")
