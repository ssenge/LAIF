"""Congestion of random geodesic path systems on vertex-transitive graphs.

For every ordered pair (u, w) a uniformly random shortest path is drawn independently.
By transitivity E c(v) = N (Dbar + 1) for every v, Dbar the mean distance over ordered pairs
(including u = w). The script asserts that E c(v) is the same at every vertex (computed exactly
from geodesic counts) and that the drawn system has g <= 2 N (Dbar + 1).
"""
import itertools, random
from collections import deque

def bfs(adj, s):
    n = len(adj); d = [-1] * n; cnt = [0] * n; d[s] = 0; cnt[s] = 1; q = deque([s])
    while q:
        a = q.popleft()
        for b in adj[a]:
            if d[b] < 0: d[b] = d[a] + 1; q.append(b)
            if d[b] == d[a] + 1: cnt[b] += cnt[a]
    return d, cnt

def cayley(n, gens):
    """Cayley graph of Z_n (circulant) with symmetric generator set."""
    S = set(gens) | {(-g) % n for g in gens}
    return [sorted({(a + s) % n for s in S}) for a in range(n)]

def hypercube(k):
    return [[a ^ (1 << i) for i in range(k)] for a in range(1 << k)]

def torus(m, k):
    pts = list(itertools.product(range(m), repeat=k)); idx = {p: i for i, p in enumerate(pts)}
    adj = []
    for p in pts:
        nb = set()
        for i in range(k):
            for e in (1, -1):
                q = list(p); q[i] = (q[i] + e) % m; nb.add(idx[tuple(q)])
        adj.append(sorted(nb))
    return adj

def check(name, adj, rng):
    n = len(adj); D = []; C = []
    for s in range(n):
        d, c = bfs(adj, s); D.append(d); C.append(c)
    dbar = sum(map(sum, D)) / n**2
    # exact Pr[v on uniform geodesic u->w] = cnt(u,v) cnt(v,w) / cnt(u,w) when v is on a geodesic
    Ec = [sum(C[u][v] * C[v][w] / C[u][w] for u in range(n) for w in range(n)
              if D[u][v] + D[v][w] == D[u][w]) for v in range(n)]
    assert max(Ec) - min(Ec) < 1e-6 * max(Ec), (name, min(Ec), max(Ec))
    assert abs(Ec[0] - n * (dbar + 1)) < 1e-6 * Ec[0]
    # draw one system: walk back from w choosing predecessors with probability ∝ geodesic counts
    load = [0] * n
    for u in range(n):
        for w in range(n):
            v = w; load[v] += 1
            while v != u:
                pred = [a for a in adj[v] if D[u][a] == D[u][v] - 1]
                v = rng.choices(pred, weights=[C[u][a] for a in pred])[0]; load[v] += 1
    g = max(load)
    assert g <= 2 * n * (dbar + 1), (name, g, n * (dbar + 1))
    print(f"{name:22s} N={n:4d} Dbar={dbar:6.3f} E c(v)={Ec[0]:9.1f} g={g:6d} g/(N(Dbar+1))={g / Ec[0]:.3f}")

if __name__ == "__main__":
    rng = random.Random(1)
    check("hypercube Q8", hypercube(8), rng)
    check("torus 9x9", torus(9, 2), rng)
    check("torus 5x5x5", torus(5, 3), rng)
    check("circulant Z_211 {1,13,61}", cayley(211, [1, 13, 61]), rng)
    check("circulant Z_401 {1,20,97}", cayley(401, [1, 20, 97]), rng)
    check("cycle C_150", cayley(150, [1]), rng)
    # mutation: on a graph that is not vertex-transitive (a path) the equal-load assert must fail
    try:
        check("path P_30 (mutation)", [[b for b in (a - 1, a + 1) if 0 <= b < 30] for a in range(30)], rng)
        raise SystemExit("mutation survived")
    except AssertionError:
        print("mutation (path P_30, not transitive) caught")
    print("all asserts passed")
