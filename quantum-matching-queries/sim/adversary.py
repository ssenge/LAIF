"""Hill-climb for gadgets where the LP support misses a maximum matching for many rounds.

r_primal(G) = first LP round r with nu(union of supports) = nu(G). If some family has
r_primal linear in s, then ~sqrt(n) disjoint-looking copies of it force hybrid cost ~sqrt n,
and the LP rounds give nothing over Hopcroft-Karp phases. Plain simplex and random objective
perturbations are both tried, so "max" below is over the tie-breaks we sampled, not all vertices.

Usage: adversary.py s1 s2 ... [--secs N]   writes best graphs to adversary_best.json
"""
import json
import random
import sys
import time

import networkx as nx
import numpy as np

import rounds as R
from hybrid import nu


def r_primal(G, seeds=4, cap=400):
    edges = list(G.edges)
    if not edges:
        return 0
    n, opt, worst = G.number_of_nodes(), nu(G), 0
    for seed in range(seeds):
        c = np.ones(len(edges))
        if seed:
            c += np.random.default_rng(seed).random(len(edges)) / (4 * n * len(edges))
        H = nx.Graph()
        H.add_nodes_from(G.nodes)
        F, last, r = [], None, 0
        for r in range(cap):
            x, duals = R.solve_lp(G, edges, F, c)
            H.add_edges_from(e for e, xe in zip(edges, x) if xe > R.EPS)
            if nu(H) == opt:
                break
            if last is not None and c @ x < last - 1e-9 and F:
                F = [S for S, dd in zip(F, duals) if abs(dd) > R.EPS]
            last = c @ x
            new = [S for S in R.support_components(G, edges, x)
                   if len(S) % 2 == 1 and R.set_value(S, edges, x) > (len(S) - 1) / 2 + 1e-6]
            if not new:
                new = R.padberg_rao(G, edges, x)
            known = {frozenset(S) for S in F}
            fresh = [S for S in new if frozenset(S) not in known]
            if not fresh:
                break
            F += fresh
        worst = max(worst, r)
    return worst


def mutate(G, rng):
    H = G.copy()
    nodes = list(H.nodes)
    for _ in range(rng.choice((1, 1, 2, 3))):
        u, v = rng.sample(nodes, 2)
        if H.has_edge(u, v):
            H.remove_edge(u, v)
        else:
            H.add_edge(u, v)
    return H


def climb(s, secs, seed):
    rng = random.Random(seed)
    G = nx.gnp_random_graph(s, 3 / s, seed=rng.randrange(10**9))
    best = r_primal(G)
    end, restart = time.time() + secs, 0
    top, topG = best, G
    while time.time() < end:
        restart += 1
        H = mutate(G, rng)
        v = r_primal(H)
        if v >= best:
            G, best = H, v
            if v > top:
                top, topG = v, H.copy()
        if restart % 3000 == 0:  # restart from noise, keeping the record
            G = nx.gnp_random_graph(s, 3 / s, seed=rng.randrange(10**9))
            best = r_primal(G)
    return top, topG


if __name__ == "__main__":
    tri = nx.cycle_graph(3)
    assert r_primal(tri) == 0  # the first LP support already holds a maximum matching
    args = sys.argv[1:]
    secs = 60
    if "--secs" in args:
        i = args.index("--secs")
        secs = int(args[i + 1])
        del args[i:i + 2]
    out = {}
    for s in [int(a) for a in args] or [10, 14, 20, 28, 40]:
        top, G = 0, None
        for seed in range(3):
            t, g = climb(s, secs, seed)
            if t >= top:
                top, G = t, g
        out[s] = {"r_primal": top, "m": G.number_of_edges(), "edges": list(map(list, G.edges))}
        print(f"s={s:3d} worst r_primal={top:3d}  m={G.number_of_edges()}", flush=True)
        with open("adversary_best.json", "w") as f:
            json.dump(out, f)
