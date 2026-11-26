"""Blocking-flow phases with arc discovery by OR-queries on a hidden simple digraph.

Counts found (pairs found to be arcs, each costing O(log n) OR-queries by binary search) and no
(OR-queries answered NO). Asserts: the flow value equals that of an independent shortest-augmenting-
path computation on the full matrix; the number of phases P is at most min(f, 3 n^{2/3} + 1); and
found + no <= 3 (P n + n sqrt(f + 1)), the count used in the proof of Theorem 1.
Mutation: keeping dead-end vertices alive makes the search loop or the count blow up.
"""
import random, math, sys
from collections import deque

def reference_flow(A, s, t):
    n = len(A); f = [[0]*n for _ in range(n)]; val = 0
    while True:
        par = [-1]*n; par[s] = s; q = deque([s])
        while q and par[t] < 0:
            u = q.popleft()
            for v in range(n):
                if par[v] < 0 and (A[u][v] - f[u][v] + f[v][u]) > 0:
                    par[v] = u; q.append(v)
        if par[t] < 0: return val
        v = t
        while v != s:
            u = par[v]
            if f[v][u]: f[v][u] -= 1
            else: f[u][v] += 1
            v = u
        val += 1

def phases_or(A, s, t, mutate=False):
    n = len(A)
    known = {}            # (u,v) -> 0/1 for queried pairs of the hidden graph
    f = [[0]*n for _ in range(n)]
    stats = {"found": 0, "no": 0, "phases": 0}
    def find(u, cands):
        """Return some v in cands with an unsaturated original edge u->v, discovering it by OR-queries."""
        unknown = []
        for v in cands:
            k = known.get((u, v))
            if k == 1 and f[u][v] == 0: return v          # already known residual original arc
            if k is None: unknown.append(v)
        hits = [v for v in unknown if A[u][v]]
        for v in unknown:
            if not A[u][v]: known[(u, v)] = 0           # an OR-query NO on a block is charged once
        if not hits:
            stats["no"] += 1; return None
        v = hits[0]; known[(u, v)] = 1; stats["found"] += 1
        return v
    def res_rev(u, cands):
        for v in cands:
            if f[v][u]: return v
        return None
    val = 0
    while True:
        # BFS levels in the residual graph
        lev = [-1]*n; lev[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            while True:
                un = [v for v in range(n) if lev[v] < 0]
                v = res_rev(u, un)
                if v is None: v = find(u, un)
                if v is None: break
                lev[v] = lev[u] + 1; q.append(v)
        if lev[t] < 0: break
        stats["phases"] += 1
        dead = [False]*n
        steps = 0
        while True:
            path = [s]
            while path and path[-1] != t:
                steps += 1
                if mutate and steps > 20 * n * n: raise RuntimeError("mutation loops")
                u = path[-1]
                nxt = [v for v in range(n) if lev[v] == lev[u] + 1 and not dead[v]]
                v = res_rev(u, nxt)
                if v is None: v = find(u, nxt)
                if v is None:
                    if not mutate: dead[u] = True
                    path.pop()
                else:
                    path.append(v)
            if not path: break
            for a, b in zip(path, path[1:]):
                if f[b][a]: f[b][a] -= 1
                else: f[a][b] += 1
            val += 1
    return val, stats

def instance(n, p, rng, layered=False):
    A = [[0]*n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if u != v and rng.random() < p: A[u][v] = 1
    return A

if __name__ == "__main__":
    rng = random.Random(7)
    worst = 0.0
    for n in (12, 20, 30, 45):
        for p in (0.05, 0.15, 0.4, 0.8):
            for rep in range(6):
                A = instance(n, p, rng)
                val, st = phases_or(A, 0, n - 1)
                assert val == reference_flow(A, 0, n - 1), (n, p, rep)
                assert st["phases"] <= min(val, 3 * n ** (2 / 3) + 1), st
                bound = st["phases"] * n + n * math.sqrt(val + 1)
                ratio = (st["found"] + st["no"]) / bound
                assert ratio <= 3, (n, p, st)
                worst = max(worst, ratio)
    print(f"96 digraphs: flow values equal to the reference; max (found+no)/(P n + n sqrt(f+1)) = {worst:.3f}")
    # mutation: without marking dead ends the search revisits them
    A = instance(30, 0.3, random.Random(3))
    try:
        val, st = phases_or(A, 0, 29, mutate=True)
        bad = val != reference_flow(A, 0, 29) or st["found"] + st["no"] > 3 * (st["phases"] * 30 + 30 * math.sqrt(val + 1))
    except (RuntimeError, RecursionError):
        bad = True
    assert bad, "mutation survived"
    print("mutation (dead ends not removed) caught")
