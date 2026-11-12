"""Exact-in-distribution evaluation of multi-round local rules for LocalMaxCut on the d-regular tree: a forest of
independent trees of radius R around a root, leaves padded with self-loops. A rule whose output at u depends on
the seeds within distance r of u gives the correct satisfaction of the root when R >= r + 1; the padding only
changes outputs farther out. Two-sided Hoeffding bound at failure 1e-9.
Usage: tree_eval.py rule chunks seed"""
import sys, json, numpy as np
from lmc_eval import T
def forest(N, R, d=3):
    """Neighbour array of N disjoint radius-R trees, BFS order per tree, root at offset 0 of each tree."""
    par = [-1]; depth = [0]; kids = [[]]
    for v in range(10**9):
        if v >= len(par): break
        if depth[v] == R: continue
        for _ in range(d if v == 0 else d - 1):
            kids[v].append(len(par)); par.append(v); depth.append(depth[v] + 1); kids.append([])
    m = len(par); nb = np.zeros((m, d), int)
    for v in range(m):
        l = ([par[v]] if par[v] >= 0 else []) + kids[v]; nb[v] = l + [v] * (d - len(l))
    NB = (nb[None, :, :] + m * np.arange(N)[:, None, None]).reshape(-1, d)
    return NB, m
def unsat(z, NB): return (z[NB] != z[:, None]).sum(1) < 2
def flip_all(z, NB): return z ^ unsat(z, NB)
def flip_prio(z, NB, pr):
    u = unsat(z, NB); cand = np.where(u, pr, -np.inf); return z ^ (u & (cand > cand[NB].max(1)))
RULES = {   # name: (output radius, function of (g, h, NB))
    "r1": (1, lambda g, h, NB: g > T(g[NB], 0.25)),
    "r1+prio": (3, lambda g, h, NB: flip_prio(g > T(g[NB], 0.25), NB, h)),
    "r1+prio+all": (4, lambda g, h, NB: flip_all(flip_prio(g > T(g[NB], 0.25), NB, h), NB)),
    "r1+all+prio": (4, lambda g, h, NB: flip_prio(flip_all(g > T(g[NB], 0.25), NB), NB, h)),
    "rand+prio": (2, lambda g, h, NB: flip_prio(g > 0, NB, h)),
}
def run(rule, N, rng, pad=0):
    r, f = RULES[rule]; NB, m = forest(N, r + 1 + pad)
    g = rng.standard_normal(len(NB)); h = rng.random(len(NB)); z = f(g, h, NB)
    roots = m * np.arange(N); return np.count_nonzero(~unsat(z, NB)[roots])
if __name__ == "__main__":
    rule, chunks, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = np.random.default_rng(seed)
    n = 200_000; k = sum(run(rule, n, rng) for _ in range(chunks)); N = n * chunks; f = k / N
    t = np.sqrt(np.log(2 / 1e-9) / (2 * N))
    print(json.dumps({"rule": rule, "radius": RULES[rule][0], "N": N, "seed": seed, "value": f,
                      "se": float(np.sqrt(f * (1 - f) / N)), "hoeffding_lower": f - t}), flush=True)
