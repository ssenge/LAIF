"""Hand-built hard instances, and two cut rules, with an adversarial objective.

hidden_pairs: k pairs of odd factor-critical sets (A_i, B_i) with one bridge e_i. A perfect
matching needs every e_i. The objective is slightly lower on bridges, so the LP avoids them
until forced, which imitates a worst-case choice of optimal vertex.
Rule "comp": cut odd components of the current fractional support (what hybrid.py did).
Rule "ge":   also cut the odd D-components of the Gallai-Edmonds decomposition of everything
             revealed so far. These have the flat form of the Tutte-Berge dual.
Reports r_primal: first LP round whose accumulated support holds a maximum matching.
"""
import random
import sys

import networkx as nx
import numpy as np

import rounds as R
from copies import augment_search
from hybrid import nu


def d_components(H):
    """Odd components of H[D], where D = vertices missed by some maximum matching of H."""
    idx = {v: i for i, v in enumerate(H.nodes)}
    back = list(H.nodes)
    adj = [[idx[w] for w in H[v]] for v in H.nodes]
    match = [-1] * len(adj)
    for u, v in nx.max_weight_matching(H, maxcardinality=True):
        match[idx[u]], match[idx[v]] = idx[v], idx[u]
    D = set()
    everyone = set(range(len(adj)))
    for v in range(len(adj)):
        if match[v] == -1:
            D.add(v)
            continue
        m = list(match)
        w = m[v]
        m[v], m[w] = -1, -1
        end, _ = augment_search(adj, m, w, everyone - {v})
        if end is not None:
            D.add(v)
    sub = H.subgraph(back[v] for v in D)
    return [set(c) for c in nx.connected_components(sub) if len(c) % 2 == 1 and len(c) >= 3]


def run(G, penal, rule, cap=300):
    edges = list(G.edges)
    n, opt = G.number_of_nodes(), nu(G)
    c = np.ones(len(edges))
    for i, (u, v) in enumerate(edges):
        if (u, v) in penal or (v, u) in penal:
            c[i] -= 1 / (4 * n)
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
        if rule == "ge":
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


def odd_set(s, chords, base, rng):
    """Odd Hamiltonian cycle plus random chords: factor-critical on s vertices."""
    assert s % 2 == 1
    G = nx.cycle_graph(s)
    for _ in range(int(chords * s)):
        u, v = rng.randrange(s), rng.randrange(s)
        if u != v:
            G.add_edge(u, v)
    return nx.relabel_nodes(G, {i: base + i for i in range(s)})


def hidden_pairs(k, s, chords, rng, noise=0.0):
    parts, bridges, nid, anchors = [], set(), 0, []
    for _ in range(k):
        A = odd_set(s, chords, nid, rng)
        nid += s
        B = odd_set(s, chords, nid, rng)
        nid += s
        e = (rng.choice(list(A.nodes)), rng.choice(list(B.nodes)))
        bridges.add(e)
        parts += [A, B]
        anchors.append(sorted(A.nodes))
    G = nx.compose_all(parts)
    G.add_edges_from(bridges)
    # noise joins A-sides only: an independent family of A sets keeps e_i necessary for a PM
    for _ in range(int(noise * k * s)):
        i, j = rng.randrange(k), rng.randrange(k)
        if i != j:
            G.add_edge(rng.choice(anchors[i]), rng.choice(anchors[j]))
    return G, bridges


if __name__ == "__main__":
    rng = random.Random(0)
    G, b = hidden_pairs(3, 7, 1.0, rng)
    assert nu(G) == G.number_of_nodes() // 2, "bridges must give a perfect matching"
    assert all(len(S) >= 3 for S in d_components(nx.cycle_graph(5)))
    print("self-check ok")
    print("   k    s chords noise     n  sqrt(n)   comp: r,|F|     ge: r,|F|     (worst of 3 seeds; -1 = stuck)")
    for k, s in ((1, 21), (1, 41), (1, 81), (3, 21), (3, 41), (7, 21), (7, 41), (15, 21)):
        for chords in (0.5, 2.0):
            for noise in (0.0, 0.3):
                if k == 1 and noise:
                    continue
                res = {}
                for rule in ("comp", "ge"):
                    w = (-2, 0)
                    for seed in range(3):
                        G, b = hidden_pairs(k, s, chords, random.Random(seed), noise)
                        w = max(w, run(G, b, rule))
                    res[rule] = w
                n = G.number_of_nodes()
                print(f"{k:4d} {s:4d} {chords:6.1f} {noise:5.1f} {n:5d} {n**.5:8.1f}"
                      f"{res['comp'][0]:>9d},{res['comp'][1]:<5d}{res['ge'][0]:>8d},{res['ge'][1]:<5d}", flush=True)
