"""Stage counts of adaptive X/Z learners for bipartite d-regular graph states (combinatorial level).

A stage fixes one setting W (X on W, Z elsewhere) for b copies. Every v in W with no neighbour in W
("clean") has its neighbourhood recovered; the others are detected as not clean. Here we only count stages.
"""
import sys, random
import numpy as np
from collections import deque

def bip_regular(m, d, rng):
    """Union of d random bijections L->R with pairwise disjoint edges (retry per bijection)."""
    adj = [set() for _ in range(2 * m)]
    for _ in range(d):
        p = rng.permutation(m)
        for _sweep in range(100000):
            bad = [i for i in range(m) if (m + p[i]) in adj[i]]
            if not bad:
                break
            for i in bad:  # swap targets with a random position
                j = int(rng.integers(m)); p[i], p[j] = p[j], p[i]
        else:
            raise RuntimeError("no disjoint bijection")
        for i in range(m):
            adj[i].add(m + p[i]); adj[m + p[i]].add(i)
    return adj

def components(adj, known):
    """Components of the graph of known edges (edges incident to a known vertex), with 2-colouring."""
    n = len(adj); comp = [-1] * n; col = [0] * n; c = 0
    kadj = [set() for _ in range(n)]
    for v in range(n):
        if known[v]:
            for u in adj[v]:
                kadj[v].add(u); kadj[u].add(v)
    for s in range(n):
        if comp[s] >= 0 or not kadj[s]:
            continue
        comp[s] = c; q = deque([s])
        while q:
            v = q.popleft()
            for u in kadj[v]:
                if comp[u] < 0:
                    comp[u] = c; col[u] = 1 - col[v]; q.append(u)
                else:
                    assert col[u] != col[v]
        c += 1
    return comp, col, c

def stage(adj, known, W):
    Wset = set(W); new = 0
    for v in W:
        if not known[v] and not (adj[v] & Wset):
            known[v] = True; new += 1
    return new

from math import lgamma, log
def log2binom(a, r):
    return 0.0 if r <= 0 else (lgamma(a + 1) - lgamma(r + 1) - lgamma(a - r + 1)) / log(2)

def stage_cost(adj, known, comp, col, W):
    """log2 of the number of candidate neighbourhoods, maximised over the unknown vertices of W.
    Candidates of v: unknown vertices outside W with a free stub, not in v's colour class of its component."""
    n = len(adj); Wset = set(W)
    r = [len(adj[v]) - sum(1 for u in adj[v] if known[u]) for v in range(n)]
    pool = [u for u in range(n) if not known[u] and u not in Wset and r[u] > 0]
    same = {}
    for u in pool:
        if comp[u] >= 0:
            same[(comp[u], col[u])] = same.get((comp[u], col[u]), 0) + 1
    best = 0.0
    for v in W:
        if known[v]:
            continue
        a = len(pool) - (same.get((comp[v], col[v]), 0) if comp[v] >= 0 else 0)
        best = max(best, log2binom(a, r[v]))
    return best

def run(adj, d, rng, strategy, maxst=200):
    n = len(adj); known = [False] * n; cost = 0.0
    R = [v for v in range(n) if rng.random() < 1.0 / (d + 1)]
    cost += stage_cost(adj, known, [-1] * n, [0] * n, R) + log(n) / log(2)
    stage(adj, known, R); st = 1; flip = 0
    done = lambda: all(known[v] or all(known[u] for u in adj[v]) for v in range(n))
    trace = [sum(known)]
    while not done() and st < maxst:
        comp, col, c = components(adj, known)
        sizes = np.bincount([x for x in comp if x >= 0], minlength=c)
        if strategy == "giant":
            g = int(np.argmax(sizes))
            unk = [sum(1 for v in range(n) if comp[v] == g and col[v] == f and not known[v]) for f in (0, 1)]
            f = int(unk[1] > unk[0])
            W = [v for v in range(n) if comp[v] == g and col[v] == f]
        else:  # "random": independent random side per component
            side = rng.integers(0, 2, size=c)
            W = [v for v in range(n) if comp[v] >= 0 and col[v] == side[comp[v]]]
        cost += stage_cost(adj, known, comp, col, W) + log(n) / log(2)
        stage(adj, known, W); st += 1; trace.append(sum(known))
    return st, cost / (d * log(n) / log(2))

def bfs_stages(adj):
    """Stages of the breadth-first learner of [1, Theorem 14] from vertex 0: eccentricity."""
    dist = {0: 0}; q = deque([0])
    while q:
        v = q.popleft()
        for u in adj[v]:
            if u not in dist:
                dist[u] = dist[v] + 1; q.append(u)
    assert len(dist) == len(adj)
    return max(dist.values())

def cluster_tree(nc, s, d, beta, k, rng):
    """nc clusters (random bipartite d-regular on s+s vertices) in a beta-ary tree; each tree edge
    is made of k edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep the sides and regularity."""
    adj = []
    L = []; Rr = []
    for c in range(nc):
        g = bip_regular(s, d, rng); off = len(adj)
        adj += [set(off + u for u in nb) for nb in g]
        L.append(list(range(off, off + s))); Rr.append(list(range(off + s, off + 2 * s)))
    for c in range(1, nc):
        p = (c - 1) // beta
        for _ in range(k):
            for _try in range(1000):
                a1 = int(rng.choice(L[p])); b1 = int(rng.choice(sorted(adj[a1])))
                a2 = int(rng.choice(L[c])); b2 = int(rng.choice(sorted(adj[a2])))
                if b2 not in adj[a1] and b1 not in adj[a2]:
                    break
            adj[a1].remove(b1); adj[b1].remove(a1); adj[a2].remove(b2); adj[b2].remove(a2)
            adj[a1].add(b2); adj[b2].add(a1); adj[a2].add(b1); adj[b1].add(a2)
    assert all(len(x) == d for x in adj)
    return adj

if __name__ == "__main__" and len(sys.argv) > 2:
    rng = np.random.default_rng(int(sys.argv[1]))
    for nc, s, d, beta, k in [(200, 12, 8, 3, 2), (600, 12, 8, 3, 2), (600, 12, 8, 3, 6), (300, 40, 8, 4, 3)]:
        for strat in ["giant", "random"]:
            for _ in range(2):
                g = cluster_tree(nc, s, d, beta, k, rng); st, tr = run(g, d, rng, strat)
                print(f"cluster tree nc={nc} s={s} d={d} beta={beta} k={k} {strat}: stages {st} (BFS {bfs_stages(g)}) cost/(d log2 n) {tr:.2f}")
    sys.exit()

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    for m, d in [(1000, 8), (4000, 9), (10000, 10)]:
        for strat in ["giant", "random"]:
            for _ in range(2):
                g = bip_regular(m, d, rng); st, tr = run(g, d, rng, strat)
                print(f"random bipartite n={2*m} d={d} {strat}: stages {st} (BFS {bfs_stages(g)}) cost/(d log2 n) {tr:.2f}")
