"""Worst case attempt against the Gallai-Edmonds cut rule.

S_0 is a triangle. S_{i+1} = S_i plus an ear a-u-v-b with a = u_i, b = b_i (the previous anchor),
so that a-u-v-b-v_i-a is an odd cycle whose removal leaves S_i minus its path perfectly matchable.
Two such chains A and B are joined by one bridge, which every perfect matching needs.

Objective "adv": ear edges to the anchors get a penalty growing with depth, and the bridge the
largest, so the LP touches ear i+1 only once S_i is cut. This models a worst-case choice of
optimal vertex. Objective "rnd": random perturbation chosen by the algorithm, which the
instance cannot anticipate. Reports r_primal for the rule of flat.py.
"""
import random
import sys

import networkx as nx
import numpy as np

import rounds as R
from flat import d_components
from hybrid import nu


def chain(m, base=0):
    """Returns (graph, depth of each penalized edge). Size 3 + 2m."""
    G = nx.Graph()
    t = [base, base + 1, base + 2]
    G.add_edges_from([(t[0], t[1]), (t[1], t[2]), (t[0], t[2])])
    depth = {}
    nid = base + 3
    a, b = t[0], t[1]  # u_0 := t[0], with path a - t[2] - b of two edges closing an odd cycle
    prev_v = t[2]
    for i in range(1, m + 1):
        u, v = nid, nid + 1
        nid += 2
        G.add_edges_from([(a, u), (u, v), (v, b)])
        depth[(a, u)] = i
        depth[(v, b)] = i
        # next ear: from the new u, back through v to the current anchor b (two edges)
        a, b, prev_v = u, b, v
    return G, depth, nid


def instance(m):
    A, da, nid = chain(m, 0)
    B, db, nid = chain(m, nid)
    G = nx.compose(A, B)
    bridge = (0, 3 + 2 * m)
    G.add_edge(*bridge)
    depth = {**da, **db}
    depth[bridge] = m + 2
    return G, depth


def run(G, c, rule="ge", cap=2000):
    edges = list(G.edges)
    opt = nu(G)
    H = nx.Graph()
    H.add_nodes_from(G.nodes)
    F = []
    for r in range(cap):
        x, _ = R.solve_lp(G, edges, F, c)
        H.add_edges_from(e for e, xe in zip(edges, x) if xe > R.EPS)
        if nu(H) == opt:
            return r, len(F)
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
            return -1, len(F)
        F += fresh
    return cap, len(F)


def objective(G, depth, kind, seed=0):
    edges = list(G.edges)
    n = G.number_of_nodes()
    c = np.ones(len(edges))
    if kind == "adv":
        for i, (u, v) in enumerate(edges):
            d = depth.get((u, v), depth.get((v, u), 0))
            c[i] -= d / (8 * n * n)
    elif kind == "rnd":
        c += np.random.default_rng(seed).random(len(edges)) / (4 * n * len(edges))
    return c


if __name__ == "__main__":
    G, depth = instance(2)
    assert nu(G) == G.number_of_nodes() // 2, "the bridge must complete a perfect matching"
    for m in (1, 3, 6):
        G, _ = instance(m)
        assert nu(G) == G.number_of_nodes() // 2, m
        assert not nx.is_bipartite(G)
    print("self-check ok")
    print("    m     n  sqrt(n)  plain   adv: r,|F|   rnd: worst r of 10 seeds")
    for m in [int(a) for a in sys.argv[1:]] or [2, 4, 8, 16, 32, 64, 128]:
        G, depth = instance(m)
        n = G.number_of_nodes()
        plain = run(G, objective(G, depth, "none"))[0]
        adv = run(G, objective(G, depth, "adv"))
        rnd = max(run(G, objective(G, depth, "rnd", s))[0] for s in range(10))
        print(f"{m:5d} {n:5d} {n**.5:8.1f} {plain:6d} {adv[0]:7d},{adv[1]:<5d} {rnd:6d}", flush=True)
