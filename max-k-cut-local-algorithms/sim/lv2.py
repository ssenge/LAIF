"""Max-Cut (k = 2) version of lv_plus_rule.py with exact Gaussian reduction. For k = 2 the Local Vector label of
vertex v is 1 iff z_v = Y_v - (tau / sqrt d) sum_{w ~ v} Y_w > 0 with Y = X_1 - X_2, so only the 2d vertices at
distance <= 1 from the edge are sampled, from the covariance of z. Then one round of the label-count rule.

usage: lv2.py d m [search_samples] [cert_samples] [thr]
"""
import sys, json, math
import numpy as np
from lv_baseline import alphas, overlaps
from lv_plus_rule import tree_radius2, all_dist, apply_rule
from hybrid import rule_states

def zcov(d, m, tau):
    lam, al = alphas(d, m)
    par, adj = tree_radius2(d)
    D = all_dist(adj)
    C = overlaps(d, m, al, Lmax=D.max())
    C = np.asarray(C)[D]
    inner = [x for x in adj if D[0, x] <= 1 or D[1, x] <= 1]
    T = np.zeros((len(inner), len(C)))
    for r, x in enumerate(inner):
        T[r, x] = 1.0
        for w in adj[x]:
            T[r, w] -= tau / np.sqrt(d)
    S = T @ C @ T.T
    return inner, adj, np.linalg.cholesky(S + 1e-12 * np.eye(len(S)))

def sample(inner, L, n, rng):
    z = rng.standard_normal((n, len(inner))) @ L.T
    return {x: (z[:, r] > 0).astype(int) for r, x in enumerate(inner)}

def cutvals(lab, adj, rule, rng):
    ru = rng.random((2, len(lab[0]), 2))
    cu = apply_rule(lab, adj, 0, rule, 2, ru[0]); cv = apply_rule(lab, adj, 1, rule, 2, ru[1])
    return (cu != cv).astype(float)

def search(d, m, n, rng):
    states = rule_states(2, d); best = (0, None, None)
    for tau in (0.0, 0.5, 1.0, 1.5, 2.0, 3.0):
        inner, adj, L = zcov(d, m, tau)
        lab = sample(inner, L, n, rng); seed = int(rng.integers(1 << 30))
        f = lambda rule: cutvals(lab, adj, rule, np.random.default_rng(seed)).mean()
        rule = {s: 0 for s in states}; cur = f(rule); improved = True
        while improved:
            improved = False
            for s in states:
                old = rule[s]; rule[s] = 1 - old
                v = f(rule)
                if v > cur + 1e-5: cur, improved = v, True
                else: rule[s] = old
        if cur > best[0]: best = (cur, tau, dict(rule))
    return best

def search_thr(d, m, n, rng):
    """Threshold rules only (flip if at least t neighbours share my label), for large d."""
    best = (0, None, None)
    for tau in (0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 5.0):
        inner, adj, L = zcov(d, m, tau)
        lab = sample(inner, L, n, rng); seed = int(rng.integers(1 << 30))
        for t in range(d // 2 + 1, d + 1):
            rule = {(c, (d - c,)): 1 for c in range(t, d + 1)}
            v = cutvals(lab, adj, rule, np.random.default_rng(seed)).mean()
            if v > best[0]: best = (v, tau, rule)
    return best

def certify(d, m, tau, rule, total, rng, chunk=200_000):
    inner, adj, L = zcov(d, m, tau); s = s2 = 0.0; n = 0
    while n < total:
        h = cutvals(sample(inner, L, chunk, rng), adj, rule, rng)
        s += h.sum(); s2 += (h * h).sum(); n += chunk
    mean = s / n; var = (s2 / n - mean ** 2) * n / (n - 1)
    Lg = math.log(2 / 1e-4)
    lcb = mean - math.sqrt(2 * var * Lg / n) - 7 * Lg / (3 * (n - 1))      # empirical Bernstein, confidence 1 - 1e-4
    return mean, math.sqrt(var / n), lcb, n

if __name__ == "__main__":
    d, m = int(sys.argv[1]), int(sys.argv[2])
    ns = int(float(sys.argv[3])) if len(sys.argv) > 3 else 400_000
    nc = int(float(sys.argv[4])) if len(sys.argv) > 4 else 4_000_000
    cur, tau, rule = (search_thr if "thr" in sys.argv else search)(d, m, ns, np.random.default_rng(7))
    mean, se, lcb, n = certify(d, m, tau, rule, nc, np.random.default_rng(2026))
    print(json.dumps({"k": 2, "d": d, "m": m, "girth": 2 * m + 4, "tau": tau, "search": round(cur, 6), "samples": n,
                      "mean": round(mean, 6), "se": round(se, 6), "lcb": math.floor(lcb * 1e4) / 1e4,
                      "rule": [[list(s[:1]) + list(s[1]), a] for s, a in rule.items() if a]}), flush=True)
