"""k copies of the ear-chain gadget: does the hybrid cost reach sqrt n?

cost_d    = min_r [(r+1) + d_r]        one phase per unit of deficiency (an upper bound on phases)
cost_pass = min_r [(r+1) + passes_r]   passes from the rounded matching
pure      = passes from the empty matching, no LP
Noise edges join A-chains of different copies and keep each bridge necessary for a PM.
Objective: random perturbation chosen by the algorithm.
"""
import random
import sys

import networkx as nx
import numpy as np

import rounds as R
from copies import passes
from ear_chain import instance, objective
from flat import d_components
from hybrid import nu


def build(k, m, noise, rng):
    size = 2 * (3 + 2 * m)
    G0, depth0 = instance(m)
    G = nx.disjoint_union_all([G0.copy() for _ in range(k)])
    a_side = 3 + 2 * m  # A-chain of copy i is size*i .. size*i + a_side - 1
    for _ in range(int(noise * k * m)):
        i, j = random.Random(rng.random()).sample(range(k), 2) if k > 1 else (0, 0)
        if i != j:
            G.add_edge(size * i + rng.randrange(a_side), size * j + rng.randrange(a_side))
    return G


def evaluate(G, seed=0, cap=400):
    edges = list(G.edges)
    opt = nu(G)
    c = objective(G, {}, "rnd", seed)
    H = nx.Graph()
    H.add_nodes_from(G.nodes)
    F = []
    best_d, best_p, d0, used = 10**9, 10**9, None, 0
    for r in range(cap):
        if r + 1 >= min(best_d, best_p):
            break
        used = r
        x, _ = R.solve_lp(G, edges, F, c)
        H.add_edges_from(e for e, xe in zip(edges, x) if xe > R.EPS)
        M = nx.max_weight_matching(H, maxcardinality=True)
        d = opt - len(M)
        if r == 0:
            d0 = d
        best_d = min(best_d, r + 1 + d)
        best_p = min(best_p, r + 1 + passes(G, M, order_seed=seed))
        if d == 0:
            break
        new = [S for S in R.support_components(G, edges, x)
               if len(S) % 2 == 1 and R.set_value(S, edges, x) > (len(S) - 1) / 2 + 1e-6]
        new += [S for S in d_components(H) if R.set_value(S, edges, x) > (len(S) - 1) / 2 + 1e-6]
        if not new:
            new = R.padberg_rao(G, edges, x)
        known = {frozenset(S) for S in F}
        fresh = []
        for S in new:
            if frozenset(S) not in known:
                known.add(frozenset(S))
                fresh.append(S)
        if not fresh:
            break
        F += fresh
    return best_d, best_p, passes(G, order_seed=seed), d0, used


if __name__ == "__main__":
    G = build(3, 2, 0.5, random.Random(0))
    assert nu(G) == G.number_of_nodes() // 2, "noise must keep a perfect matching"
    print("self-check ok")
    print("    k    m noise     n  sqrt(n)  d0  rounds_used  cost_d  cost_pass  pure_passes")
    for k, m in ((4, 8), (8, 8), (8, 16), (16, 8), (16, 16), (32, 8), (32, 16)):
        for noise in (0.0, 0.5, 2.0):
            G = build(k, m, noise, random.Random(k * 100 + m))
            d, p, pure, d0, used = evaluate(G)
            n = G.number_of_nodes()
            print(f"{k:5d} {m:4d} {noise:5.1f} {n:5d} {n**.5:8.1f} {d0:3d} {used:12d} {d:7d} {p:10d} {pure:12d}", flush=True)
