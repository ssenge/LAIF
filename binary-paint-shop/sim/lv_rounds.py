"""Max-Cut (k = 2): Local Vector algorithm with parameter m, then r synchronous rounds of a flip rule:
a vertex flips if at least theta[i] of its d neighbours share its colour in round i. Radius m + r.
Monte Carlo on the radius-(r + 1) neighbourhood of an edge of the d-regular tree.

usage: lv_rounds.py d m tau theta1,theta2,... [samples] [seed]
"""
import sys
import numpy as np
from lv_baseline import alphas, overlaps


def all_dist(adj):
    n = len(adj); D = np.full((n, n), -1)
    for s in range(n):
        D[s, s] = 0; q = [s]
        while q:
            x = q.pop(0)
            for y in adj[x]:
                if D[s, y] < 0:
                    D[s, y] = D[s, x] + 1; q.append(y)
    return D


def tree(d, R):
    """Vertices within distance R of edge (0, 1); returns adjacency and distance to the edge."""
    adj = {0: [1], 1: [0]}
    dist = {0: 0, 1: 0}
    front = [0, 1]
    for r in range(R):
        nf = []
        for x in front:
            for _ in range(d - 1):
                y = len(adj); adj[y] = [x]; adj[x].append(y); dist[y] = r + 1; nf.append(y)
        front = nf
    return adj, dist


def run(d, m, tau, thetas, n, rng, chunk=20_000):
    r = len(thetas)
    lam, al = alphas(d, m)
    adj, dist = tree(d, r + 1)
    D = all_dist(adj)
    C = overlaps(d, m, al, Lmax=D.max())[D]
    L = np.linalg.cholesky(C + 1e-12 * np.eye(len(C)))
    inner = [x for x in adj if dist[x] <= r]
    s = s2 = 0.0; done = 0
    while done < n:
        c = min(chunk, n - done)
        X = np.einsum("ij,sjk->sik", L, rng.standard_normal((c, len(C), 2)))
        top = X.max(axis=2, keepdims=True)
        second = np.sort(X, axis=2)[:, :, -2:-1]
        M = np.where(X == top, second - top, 0.0)
        lab = {x: (X[:, x] + tau / np.sqrt(d) * M[:, adj[x]].sum(axis=1)).argmax(axis=1) for x in inner}
        for i, th in enumerate(thetas):            # round i is valid on vertices at distance <= r - 1 - i
            new = {}
            for x in lab:
                if dist[x] <= r - 1 - i:
                    same = sum((lab[y] == lab[x]).astype(int) for y in adj[x])
                    new[x] = np.where(same >= th, 1 - lab[x], lab[x])
            lab = new
        h = (lab[0] != lab[1]).astype(float)
        s += h.sum(); s2 += (h * h).sum(); done += c
    mean = s / n
    return mean, np.sqrt((s2 / n - mean ** 2) / n)


if __name__ == "__main__":
    d, m = int(sys.argv[1]), int(sys.argv[2]); tau = float(sys.argv[3])
    thetas = [int(v) for v in sys.argv[4].split(",")] if sys.argv[4] != "-" else []
    n = int(float(sys.argv[5])) if len(sys.argv) > 5 else 200_000
    rng = np.random.default_rng(int(sys.argv[6]) if len(sys.argv) > 6 else 5)
    mu, se = run(d, m, tau, thetas, n, rng)
    print(f"d={d} m={m} tau={tau} rounds={thetas}: cut {mu:.5f} +- {se:.5f}  swaps/car {2*(1-mu):.4f}", flush=True)
