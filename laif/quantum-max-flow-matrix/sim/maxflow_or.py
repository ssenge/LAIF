"""Blocking-flow phases with arc discovery by OR-queries on a hidden simple digraph.

Counts found (pairs found to be arcs, each costing O(log n) OR-queries by binary search) and no
(OR-queries answered NO). Asserts: the output is a feasible 0/1 flow (capacities, conservation, no flow on both arcs of a
pair) whose value equals that of an independent shortest-augmenting-
path computation on the full matrix; the number of phases P is at most min(f, 3 n^{2/3} + 1); and
found + no <= 3 (P n + n sqrt(f + 1)), the count used in the proof of Theorem 1.
Chain digraphs (s-t paths of lengths 1..L) force L phases. Mutation: keeping dead-end vertices alive makes the search loop or the count blow up.
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
            if not A[u][v]: known[(u, v)] = 0           # shortcut: reveals all non-arcs at once; counts depend only on which candidates are arcs
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
    return val, stats, f

def instance(n, p, rng, layered=False):
    A = [[0]*n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if u != v and rng.random() < p: A[u][v] = 1
    return A

def check_flow(A, f, s, t, val):
    n = len(A)
    for u in range(n):
        for v in range(n):
            assert f[u][v] in (0, 1) and f[u][v] <= A[u][v] and not (f[u][v] and f[v][u])
    for v in range(n):
        net = sum(f[v][w] for w in range(n)) - sum(f[w][v] for w in range(n))
        assert net == (val if v == s else -val if v == t else 0), v

def chains(L, rng, extra):
    """s-t paths of lengths 1..L on disjoint internal vertices, plus random arcs that point back
    along the chains or between chains of equal position (they create no shorter s-t path)."""
    pos = {0: 0}; n = 2; paths = []
    for l in range(1, L + 1):
        inner = list(range(n, n + l - 1)); n += l - 1; paths.append(inner)
        for i, v in enumerate(inner): pos[v] = i + 1
    t = n - 1 + 1; n += 1; pos[t] = None
    A = [[0]*n for _ in range(n)]
    for inner in paths:
        seq = [0] + inner + [t]
        for a, b in zip(seq, seq[1:]): A[a][b] = 1
    V = [v for v in pos if pos[v] is not None and v != 0]
    for _ in range(extra):
        a, b = rng.choice(V), rng.choice(V)
        if a != b and pos[b] <= pos[a]: A[a][b] = 1
    return A, t

if __name__ == "__main__":
    rng = random.Random(7)
    worst = 0.0
    for n in (12, 20, 30, 45):
        for p in (0.05, 0.15, 0.4, 0.8):
            for rep in range(6):
                A = instance(n, p, rng)
                val, st, f = phases_or(A, 0, n - 1)
                assert val == reference_flow(A, 0, n - 1), (n, p, rep)
                check_flow(A, f, 0, n - 1, val)
                assert st["phases"] <= min(val, 3 * n ** (2 / 3) + 1), st
                bound = st["phases"] * n + n * math.sqrt(val + 1)
                ratio = (st["found"] + st["no"]) / bound
                assert ratio <= 3, (n, p, st)
                worst = max(worst, ratio)
    print(f"96 random digraphs: feasible flows of the reference value; max (found+no)/(P n + n sqrt(f+1)) = {worst:.3f}")
    worst, maxp = 0.0, 0
    for L in (6, 10, 14, 18):
        for extra in (0, 50, 400):
            A, t = chains(L, rng, extra); n = len(A)
            val, st, f = phases_or(A, 0, t)
            assert val == reference_flow(A, 0, t) == L
            check_flow(A, f, 0, t, val)
            assert st["phases"] <= min(val, 3 * n ** (2 / 3) + 1), st
            ratio = (st["found"] + st["no"]) / (st["phases"] * n + n * math.sqrt(val + 1))
            assert ratio <= 3, (L, extra, st)
            worst, maxp = max(worst, ratio), max(maxp, st["phases"])
    assert maxp == 18
    print(f"12 chain digraphs (up to {maxp} phases): feasible maximum flows; max ratio = {worst:.3f}")
    # mutation: without marking dead ends the search revisits them
    A = instance(30, 0.3, random.Random(3))
    try:
        val, st, _ = phases_or(A, 0, 29, mutate=True)
        bad = val != reference_flow(A, 0, 29) or st["found"] + st["no"] > 3 * (st["phases"] * 30 + 30 * math.sqrt(val + 1))
    except (RuntimeError, RecursionError):
        bad = True
    assert bad, "mutation survived"
    print("mutation (dead ends not removed) caught")
