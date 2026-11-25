"""Exact checks of the weighted adversary for local search on staircases (small graphs).

Inputs: milestone sequences x = (1, x_2, ..., x_{L+1}) over an all-pairs path system P (BFS paths).
f_x as in the staircase construction: on the staircase, -i*n - j (i the largest segment index
containing v, j its position there); off it, dist(v, 1). Output: the unique local minimum x_{L+1}.

Checked by assert, for every input / pair / vertex:
  (1) f_x has the unique local minimum x_{L+1};
  (2) f_x(v) != f_y(v) only if v lies on tail_x(k) or tail_y(k), k = x ^ y (common prefix length);
  (3) Pr over continuations x' of prefix(y, k) of [v in tail_{x'}(k)] <= q_k(y_k, v)
      = c_{y_k}(v)/(n-1) + (L - k) c(v)/(n(n-1));
  (4) with Gamma[x,y] = w = 1/#{z : z ^ x = k} on pairs with different outputs and
      alpha_k = sqrt(q_k(x_k, v)), the spectral norm of Gamma_v (entries where f differs at v) is
      at most 3 * max_z sum_k alpha_k(z_k, v), and ||Gamma|| / max_v ||Gamma_v|| is printed.
"""
import itertools, math, random, sys
import numpy as np

def bfs_paths(adj, n):
    P = {}
    dist = []
    for u in range(n):
        par = {u: None}; d = {u: 0}; q = [u]
        for a in q:
            for b in adj[a]:
                if b not in par:
                    par[b] = a; d[b] = d[a] + 1; q.append(b)
        dist.append(d)
        for w in range(n):
            p = [w]
            while p[-1] != u:
                p.append(par[p[-1]])
            P[u, w] = p[::-1]
    return P, dist

def staircase(x, P):
    walk = []  # (vertex, segment index i (1-based), position j (1-based))
    for i in range(len(x) - 1):
        for j, v in enumerate(P[x[i], x[i + 1]]):
            walk.append((v, i + 1, j + 1))
    return walk

def fvals(x, P, dist, n):
    f = [dist[0][v] for v in range(n)]
    best = {}
    for v, i, j in staircase(x, P):  # max index i; position j in that path (BFS paths are simple)
        if v not in best or i > best[v][0]:
            best[v] = (i, j)
    for v, (i, j) in best.items():
        f[v] = -i * n - j
    return f

def tail(x, P, k):
    """vertices of segments k.. (1-based) with the first occurrence of x_k removed."""
    seq = []
    for i in range(k - 1, len(x) - 1):
        seq += P[x[i], x[i + 1]]
    seq.remove(x[k - 1])
    return set(seq)

def check(n, deg, L, seed):
    rng = random.Random(seed)
    while True:  # random connected deg-regular graph by pairing
        pts = [v for v in range(n) for _ in range(deg)]; rng.shuffle(pts)
        E = set()
        ok = True
        for a, b in zip(pts[::2], pts[1::2]):
            if a == b or (min(a, b), max(a, b)) in E: ok = False; break
            E.add((min(a, b), max(a, b)))
        if not ok: continue
        adj = [[] for _ in range(n)]
        for a, b in E: adj[a].append(b); adj[b].append(a)
        P, dist = bfs_paths(adj, n)
        if all(len(dist[u]) == n for u in range(n)): break
    cu = np.zeros((n, n)); c = np.zeros(n)
    for (u, w), p in P.items():
        for v in set(p):
            cu[u, v] += 1; c[v] += 1
    X = [(0,) + t for t in itertools.product(range(n), repeat=L)]
    F = {x: fvals(x, P, dist, n) for x in X}
    for x in X:  # (1)
        f = F[x]
        mins = [v for v in range(n) if all(f[v] <= f[u] for u in adj[v])]
        assert mins == [x[-1]], (x, mins)
    idx = {x: a for a, x in enumerate(X)}
    N = len(X)
    def pref(x, y):
        k = 0
        while k < len(x) and x[k] == y[k]: k += 1
        return k  # x_1..x_k agree, x_{k+1} differs
    q = lambda zk, v, k: cu[zk, v] / (n - 1) + (L - k) * c[v] / (n * (n - 1)) + 1e-12
    G = np.zeros((N, N)); Gv = [np.zeros((N, N)) for _ in range(n)]
    tails = {}
    for x in X:
        for k in range(1, L + 1):
            tails[x, k] = tail(x, P, k)
    for x in X:
        for y in X:
            if x[-1] == y[-1]: continue
            k = pref(x, y)
            w = 1.0 / ((n - 1) * n ** (L - k))
            G[idx[x], idx[y]] = w
            for v in range(n):
                if F[x][v] != F[y][v]:
                    assert v in tails[x, k] or v in tails[y, k]  # (2)
                    Gv[v][idx[x], idx[y]] = w
    for y in X:  # (3)
        for k in range(1, L + 1):
            conts = [z for z in X if z[:k] == y[:k] and z[k] != y[k]]
            for v in range(n):
                pr = sum(v in tails[z, k] for z in conts) / ((n - 1) * n ** (L - k))
                assert pr <= q(y[k - 1], v, k) + 1e-9, (y, k, v, pr)
    normG = np.linalg.norm(G, 2)
    worst = 0
    for v in range(n):  # (4)
        S = max(sum(math.sqrt(q(z[k - 1], v, k)) for k in range(1, L + 1)) for z in X)
        nv = np.linalg.norm(Gv[v], 2)
        assert nv <= 3 * S + 1e-9, (v, nv, S)
        worst = max(worst, nv)
    print(f"n={n} deg={deg} L={L}: inputs {N}, ||G|| = {normG:.3f}, max_v ||G_v|| = {worst:.3f}, "
          f"ratio {normG / worst:.3f}, g = {int(c.max())}")

if __name__ == "__main__":
    for n, deg, L, s in [(6, 3, 2, 1), (8, 3, 2, 2), (8, 3, 3, 3), (10, 3, 2, 4), (10, 4, 2, 5), (12, 3, 2, 6)]:
        check(n, deg, L, s)
    print("all asserts passed")
