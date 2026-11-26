"""Fraction of Gomory-Hu tree edges whose value is below the trivial bound min(deg u, deg v) on dense simple graphs:
random G(n, p) and planted two-community graphs (dense blocks joined by a sparser bipartite part)."""
import numpy as np, networkx as nx
def stats(G):
    nx.set_edge_attributes(G, 1, "capacity"); T = nx.gomory_hu_tree(G, capacity="capacity")
    deg = dict(G.degree()); bad = 0
    for u, v, w in T.edges(data="weight"):
        # value of tree edge (u, v) is lambda(u, v); trivial bound min(deg u, deg v)
        assert w <= min(deg[u], deg[v])
        bad += w < min(deg[u], deg[v])
    return bad, T.number_of_edges()
rng = np.random.default_rng(1)
for n in (60, 120, 200):
    for p in (0.2, 0.5):
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(1e9)))
        if not nx.is_connected(G): continue
        b, e = stats(G); print(f"G({n},{p}): nontrivial GH values {b}/{e}", flush=True)
    G = nx.stochastic_block_model([n // 2, n // 2], [[0.6, 0.15], [0.15, 0.6]], seed=n)
    b, e = stats(G); print(f"SBM({n}; 0.6/0.15): nontrivial GH values {b}/{e}", flush=True)
