"""Evaluates the adversary bound on random 3-regular graphs with BFS path systems.

c_u(v) is the subtree size of v in the BFS tree rooted at u, c(v) = sum_u c_u(v), g = max_v c(v).
L = floor((n^2/g)^(1/3)). For sampled staircases z the script takes the worst vertex of
Phi(z, v) = sum_k sqrt(c_{z_k}(v)/(n-1)) and prints the bound
B = L / (3 (Phi_max + L^(3/2) sqrt(g/(n(n-1))))) and B/n^(1/3).
"""
import math, random, sys
import numpy as np

def graph(n, rng):
    while True:
        pts = [v for v in range(n) for _ in range(3)]; rng.shuffle(pts)
        adj = [[] for _ in range(n)]; E = set(); ok = True
        for a, b in zip(pts[::2], pts[1::2]):
            e = (min(a, b), max(a, b))
            if a == b or e in E: ok = False; break
            E.add(e); adj[a].append(b); adj[b].append(a)
        if ok: return adj

def subtree_sizes(adj, u, n):
    par = [-1] * n; seen = [False] * n; seen[u] = True; order = [u]
    for a in order:
        for b in adj[a]:
            if not seen[b]: seen[b] = True; par[b] = a; order.append(b)
    if len(order) < n: return None
    s = np.ones(n, dtype=np.float32)
    for a in reversed(order[1:]): s[par[a]] += s[a]
    return s

def run(n, seed, samples=300):
    rng = random.Random(seed)
    while True:
        adj = graph(n, rng)
        C = np.empty((n, n), dtype=np.float32); ok = True
        for u in range(n):
            s = subtree_sizes(adj, u, n)
            if s is None: ok = False; break
            C[u] = s
        if ok: break
    assert (C <= n).all() and np.allclose(C[np.arange(n), np.arange(n)], n)
    c = C.sum(axis=0); g = float(c.max())
    L = int((n * n / g) ** (1 / 3))
    R = np.sqrt(C / (n - 1))
    phi = 0.0
    for _ in range(samples):
        z = [0] + [rng.randrange(n) for _ in range(L - 1)]
        phi = max(phi, float(R[z].sum(axis=0).max()))
    tailterm = L ** 1.5 * math.sqrt(g / (n * (n - 1)))
    B = L / (3 * (phi + tailterm))
    print(f"n={n:6d} g/(n ln n)={g / (n * math.log(n)):.3f} L={L:3d} Phi_max={phi:.3f} "
          f"tail={tailterm:.3f} B={B:.3f} B/n^(1/3)={B / n ** (1 / 3):.4f}")
    return B

if __name__ == "__main__":
    for i, n in enumerate([250, 500, 1000, 2000, 4000]):
        run(n, i + 1)
