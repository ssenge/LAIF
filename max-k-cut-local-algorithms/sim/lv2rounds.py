"""Local Vector algorithm of 2609.39042 with parameter m, then TWO rounds of label-count rules (rule1 at the
vertices within distance 1 of the edge, then rule2 at u, v). Radius m + 2, compared at girth 2m + 6.
Random sampling on the radius-3 neighbourhood of an edge.

usage: lv2rounds.py k d m tau [search_samples] [cert_samples]
"""
import sys, json, math
import numpy as np
from lv_baseline import alphas, overlaps
from lv_plus_rule import all_dist, apply_rule
from hybrid import rule_states


def tree(d, R):
    par = {0: None, 1: None}; adj = {0: [1], 1: [0]}; front = [0, 1]
    for _ in range(R):
        nf = []
        for x in front:
            for _ in range(d - 1):
                y = len(par); par[y] = x; adj[y] = [x]; adj[x].append(y); nf.append(y)
        front = nf
    return adj


def setup(k, d, m):
    adj = tree(d, 3); D = all_dist(adj)
    lam, al = alphas(d, m)
    C = overlaps(d, m, al, Lmax=D.max())[D]
    L = np.linalg.cholesky(C + 1e-12 * np.eye(len(C)))
    dist = np.minimum(D[0], D[1])
    return adj, L, dist


def labels(k, d, tau, adj, L, dist, n, rng):
    X = np.einsum("ij,sjk->sik", L, rng.standard_normal((n, L.shape[0], k)))
    top = X.max(axis=2, keepdims=True)
    second = np.sort(X, axis=2)[:, :, -2:-1]
    M = np.where(X == top, second - top, 0.0)
    lab = {}
    for x in adj:
        if dist[x] <= 2:
            lab[x] = (X[:, x] + tau / np.sqrt(d) * M[:, adj[x]].sum(axis=1)).argmax(axis=1)
    return lab


def run(lab, adj, dist, r1, r2, k, ru):
    lab1 = {x: (apply_rule(lab, adj, x, r1, k, ru[x]) if dist[x] <= 1 else lab[x]) for x in lab}
    cu = apply_rule(lab1, adj, 0, r2, k, ru[-1]); cv = apply_rule(lab1, adj, 1, r2, k, ru[-2])
    return (cu != cv).astype(float)


def draws(n, k, nv, rng):
    return {**{x: rng.random((n, k)) for x in range(nv)}, -1: rng.random((n, k)), -2: rng.random((n, k))}


def search(k, d, m, tau, n, rng, init=None):
    adj, L, dist = setup(k, d, m)
    lab = labels(k, d, tau, adj, L, dist, n, rng); ru = draws(n, k, len(adj), rng)
    states = rule_states(k, d)
    r1 = {s: 0 for s in states}; r2 = {s: 0 for s in states}
    if init: r1.update(init[0]); r2.update(init[1])
    f = lambda: run(lab, adj, dist, r1, r2, k, ru).mean()
    cur = f(); improved = True
    while improved:
        improved = False
        for r in (r2, r1):
            for s in states:
                for a in range(k):
                    if a == r[s]: continue
                    old = r[s]; r[s] = a; v = f()
                    if v > cur + 1e-5: cur, improved = v, True
                    else: r[s] = old
    return cur, r1, r2


def certify(k, d, m, tau, r1, r2, total, rng, chunk=100_000):
    adj, L, dist = setup(k, d, m); s = s2 = 0.0; n = 0
    while n < total:
        h = run(labels(k, d, tau, adj, L, dist, chunk, rng), adj, dist, r1, r2, k, draws(chunk, k, len(adj), rng))
        s += h.sum(); s2 += (h * h).sum(); n += chunk
    mean = s / n; var = (s2 / n - mean ** 2) * n / (n - 1); Lg = math.log(2 / 1e-4)
    return mean, math.sqrt(var / n), mean - math.sqrt(2 * var * Lg / n) - 7 * Lg / (3 * (n - 1)), n


if __name__ == "__main__":
    k, d, m = map(int, sys.argv[1:4]); tau = float(sys.argv[4])
    ns = int(float(sys.argv[5])) if len(sys.argv) > 5 else 200_000
    nc = int(float(sys.argv[6])) if len(sys.argv) > 6 else 0
    cur, r1, r2 = search(k, d, m, tau, ns, np.random.default_rng(7))
    out = {"k": k, "d": d, "m": m, "girth": 2 * m + 6, "tau": tau, "search": round(cur, 6),
           "rule1": [[s[0], list(s[1]), a] for s, a in r1.items() if a], "rule2": [[s[0], list(s[1]), a] for s, a in r2.items() if a]}
    if nc:
        mean, se, lcb, n = certify(k, d, m, tau, r1, r2, nc, np.random.default_rng(2026))
        out.update(samples=n, mean=round(mean, 6), se=round(se, 6), lcb=math.floor(lcb * 1e4) / 1e4)
    print(json.dumps(out), flush=True)
