"""Classical counterpart of the hybrid: Local Vector algorithm with parameter m (radius m for tau > 0), then one
round of a label-count rule (same rule space as hybrid_opt.py). Radius m + 1, so the
comparison girth is 2m+4. Monte Carlo on the radius-2 neighbourhood of an edge.

usage: lv_plus_rule.py k d m [samples]
"""
import sys
import numpy as np
from scipy.optimize import minimize_scalar
from lv_baseline import alphas, overlaps
from hybrid import rule_states


def tree_radius2(d):
    """Vertices within distance 2 of edge (0, 1): returns parent list and adjacency."""
    par = {0: None, 1: None}
    adj = {0: [1], 1: [0]}
    front = [0, 1]
    for _ in range(2):
        nf = []
        for x in front:
            for _ in range(d - 1):
                y = len(par); par[y] = x; adj[y] = [x]; adj[x].append(y); nf.append(y)
        front = nf
    return par, adj


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


def labels(k, d, m, tau, n, rng):
    """LV labels of the edge endpoints and their neighbours (distance <= 1), plus index lists."""
    lam, al = alphas(d, m)
    par, adj = tree_radius2(d)
    D = all_dist(adj)
    rho = overlaps(d, m, al, Lmax=D.max())
    C = rho[D]
    L = np.linalg.cholesky(C + 1e-12 * np.eye(len(C)))
    X = np.einsum("ij,sjk->sik", L, rng.standard_normal((n, len(C), k)))
    top = X.max(axis=2, keepdims=True)
    second = np.sort(X, axis=2)[:, :, -2:-1]
    M = np.where(X == top, second - top, 0.0)
    inner = [x for x in adj if D[0, x] <= 1 or D[1, x] <= 1]        # u, v and their neighbours
    lab = {}
    for x in inner:
        S = X[:, x] + tau / np.sqrt(d) * M[:, adj[x]].sum(axis=1)
        lab[x] = S.argmax(axis=1)
    return lab, adj


def apply_rule(lab, adj, x, rule, k, rng_u):
    """New label of vertex x; rule[state] = 0 keep, r>0 move to the label of count rank r-1 (ties split)."""
    own = lab[x]
    n = len(own)
    counts = np.zeros((n, k), int)
    for y in adj[x]:
        counts[np.arange(n), lab[y]] += 1
    out = own.copy()
    for s, a in rule.items():
        if a == 0:
            continue
        nown, others = s
        mine = counts[np.arange(n), own]
        oth = np.where(np.eye(k, dtype=bool)[own], 10**6, counts)       # mask own label
        srt = np.sort(oth, axis=1)[:, :k - 1]
        hit = (mine == nown) & np.all(srt == np.array(others), axis=1)
        if not hit.any():
            continue
        target = srt[:, a - 1]
        cand = (oth == target[:, None])
        # random choice among tied candidate labels
        r = rng_u[:, :k] * cand
        pick = r.argmax(axis=1)
        out[hit] = pick[hit]
    return out


def cut(lab, adj, rule, k, rng_u):
    cu = apply_rule(lab, adj, 0, rule, k, rng_u[0])
    cv = apply_rule(lab, adj, 1, rule, k, rng_u[1])
    h = (cu != cv).astype(float)
    return h.mean(), h.std() / np.sqrt(len(h))


if __name__ == "__main__":
    k, d, m = map(int, sys.argv[1:4])
    n = int(float(sys.argv[4])) if len(sys.argv) > 4 else 400_000
    rng = np.random.default_rng(7)
    states = rule_states(k, d)
    best = (0, None, None)
    for tau in (0.0, 1.0, 2.0, 3.0):
        lab, adj = labels(k, d, m, tau, n, rng)
        ru = rng.random((2, n, k))
        rule = {s: 0 for s in states}
        cur = cut(lab, adj, rule, k, ru)[0]
        improved = True
        while improved:
            improved = False
            for s in states:
                for a in range(k):
                    if a == rule[s]:
                        continue
                    old = rule[s]; rule[s] = a
                    v = cut(lab, adj, rule, k, ru)[0]
                    if v > cur + 1e-5:
                        cur, improved = v, True
                    else:
                        rule[s] = old
        if cur > best[0]:
            best = (cur, tau, dict(rule))
    cur, tau, rule = best
    import json
    with open(f"lvrule_{k}_{d}_{m}.json", "w") as fh:
        json.dump({"k": k, "d": d, "m": m, "tau": tau, "rule": [[list(s[:1]) + list(s[1]), a] for s, a in rule.items()]}, fh)
    lab, adj = labels(k, d, m, tau, 4 * n, rng)
    fresh = cut(lab, adj, rule, k, rng.random((2, 4 * n, k)))
    print(f"k={k} d={d} LV m={m} + 1 round (girth {2*m+4}): tau={tau} search {cur:.5f} "
          f"fresh {fresh[0]:.5f} +- {fresh[1]:.5f}  moves={sum(1 for a in rule.values() if a)}")
