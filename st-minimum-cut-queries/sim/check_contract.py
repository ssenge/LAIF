"""Numerical test of the repeated contraction for s-t minimum cut on simple graphs. See the README.

Run: uv run --no-project --with networkx python check_contract.py

H_K is a uniform sample of G[K] with rate 1/2 and weight 2, standing in for a cut sparsifier. Peeled edges are exact.
Tests, by assertion, at the stable partition P:
1. P respects the minimum s-t cut X returned by networkx, and lambda(G/P) = lambda(G).
2. Lemma A: residual core weight between parts is at most k(t_K - 1).
3. Lemma B: flow on core edges between parts is at most 2 b f_H + 2 s sqrt(W f_H), with W = 2.
4. Lemma D: s D / 4 <= C.
Prints t_K, s, b and C, the crossing edges of G[K], against n(1 + f/D).

Limits: small n, a sampling stand-in for the sparsifier, and k taken from the error on the one cut X, so test 1
checks only X. Lemma C uses the sparsifier property and is reported as a ratio, not asserted.
"""
import math
import random

import networkx as nx


def peel(G, D):
    g = G.copy()
    while True:
        low = [v for v, d in g.degree if d < D]
        if not low:
            return set(g.nodes)
        g.remove_nodes_from(low)


def strong_partition(g, k):
    """k-strong partition: split along any cut lighter than k, recursively."""
    out, todo = [], [set(g.nodes)]
    while todo:
        part = todo.pop()
        if len(part) == 1:
            out.append(part)
            continue
        sub = g.subgraph(part)
        if not nx.is_connected(sub):
            todo += [set(c) for c in nx.connected_components(sub)]
            continue
        w, (a, b) = nx.stoer_wagner(sub, weight="weight")
        if w >= k:
            out.append(part)
        else:
            todo += [set(a), set(b)]
    return out


def min_cost_flow(edges, nodes, s, t):
    """edges: (a, b, weight, cost) between parts. Returns value and flow per edge, by successive shortest paths."""
    # nodes for arcs: each undirected edge gets its own middle node on each arc, to allow parallel edges.
    d = nx.DiGraph()
    d.add_nodes_from(nodes)
    for i, (a, b, w, c) in enumerate(edges):
        d.add_edge(a, ("f", i), capacity=w, weight=c)
        d.add_edge(("f", i), b, capacity=w, weight=0)
        d.add_edge(b, ("g", i), capacity=w, weight=c)
        d.add_edge(("g", i), a, capacity=w, weight=0)
    val = nx.maximum_flow_value(d, s, t)
    d.add_node(s, demand=-val)
    d.add_node(t, demand=val)
    fl = nx.min_cost_flow(d)
    used = []
    for i, (a, b, w, c) in enumerate(edges):
        used.append(abs(fl[a][("f", i)] - fl[b][("g", i)]))
    return val, used


def run(G, s, t, D, seed):
    rnd = random.Random(seed)
    K = peel(G, D)
    sampled = {}
    for u, v in G.edges:
        if u in K and v in K:
            if rnd.random() < 0.5:
                sampled[(u, v)] = 2
        else:
            sampled[(u, v)] = 1
    core = lambda e: e[0] in K and e[1] in K
    d0 = nx.Graph()
    d0.add_nodes_from(G.nodes)
    for (u, v), w in sampled.items():
        d0.add_edge(u, v, capacity=w)
    f0 = nx.minimum_cut_value(d0, s, t)
    gg = nx.Graph()
    gg.add_nodes_from(G.nodes)
    gg.add_edges_from(((u, v, {"capacity": 1}) for u, v in G.edges))
    val, (X, Y) = nx.minimum_cut(gg, s, t)
    tau = sum(w for (u, v), w in sampled.items() if (u in X) != (v in X)) - f0
    k = tau + 1
    parts = [{v} for v in G.nodes]
    while True:
        idx = {v: i for i, p in enumerate(parts) for v in p}
        edges = [(idx[u], idx[v], w, 1 if core((u, v)) else 0, (u, v)) for (u, v), w in sampled.items() if idx[u] != idx[v]]
        f_H, used = min_cost_flow([e[:4] for e in edges], range(len(parts)), idx[s], idx[t])
        r = nx.Graph()
        r.add_nodes_from(range(len(parts)))
        for e, x in zip(edges, used):
            if e[2] - x > 0:
                w = r[e[0]][e[1]]["weight"] if r.has_edge(e[0], e[1]) else 0
                r.add_edge(e[0], e[1], weight=w + e[2] - x)
        sp = strong_partition(r, k)
        if len(sp) == len(parts):
            break
        parts = [set().union(*(parts[i] for i in c)) for c in sp]
    for p in parts:
        assert p <= X or p <= Y, "partition splits the minimum cut"
    q = nx.Graph()
    q.add_nodes_from(range(len(parts)))
    for u, v in G.edges:
        if idx[u] != idx[v]:
            w = q[idx[u]][idx[v]]["capacity"] if q.has_edge(idx[u], idx[v]) else 0
            q.add_edge(idx[u], idx[v], capacity=w + 1)
    assert nx.minimum_cut_value(q, idx[s], idx[t]) == val
    meeting = [p for p in parts if p & K]
    big = [p for p in meeting if len(p & K) >= D / 2]
    b, sv = len(big), sum(len(p & K) for p in meeting if len(p & K) < D / 2)
    tK = len(meeting)
    res = sum(e[2] - x for e, x in zip(edges, used) if e[3] == 1)
    F = sum(x for e, x in zip(edges, used) if e[3] == 1)
    W = 2
    C = sum(1 for u, v in G.edges if u in K and v in K and idx[u] != idx[v])
    assert res <= k * max(tK - 1, 0) + 1e-9, ("lemma A", res, k, tK)
    assert F <= 2 * b * f_H + 2 * sv * math.sqrt(W * f_H) + 1e-9, ("lemma B", F, b, sv, f_H)
    assert sv * D / 4 <= C + 1e-9, ("lemma D", sv, C)
    return dict(n=G.number_of_nodes(), K=len(K), lam=val, k=k, tK=tK, b=b, s=sv, C=C, ratio=C / (res + F) if res + F else 0, bound=G.number_of_nodes() * (1 + val / D))


def clusters_with_medium(n, clusters, medium, d, rnd):
    """Dense clusters, a set of medium vertices of degree about d, and two hubs s and t joined to everything."""
    G = nx.Graph()
    G.add_nodes_from(range(n))
    s, t = 0, 1
    rest = list(range(2, n))
    med, core = rest[:medium], rest[medium:]
    size = len(core) // clusters
    for c in range(clusters):
        part = core[c * size : (c + 1) * size]
        G.add_edges_from((u, v) for i, u in enumerate(part) for v in part[i + 1 :] if rnd.random() < 0.8)
    for u in med:
        for v in rnd.sample(rest, d):
            if u != v:
                G.add_edge(u, v)
    for v in rnd.sample(rest, n // 2):
        G.add_edge(s, v)
    for v in rnd.sample(rest, n // 2):
        G.add_edge(t, v)
    return G, s, t


def bipartite_hubs(n, hubs, rnd):
    """A few high degree vertices joined to many low degree ones, plus a dense cluster."""
    G = nx.Graph()
    G.add_nodes_from(range(n))
    H = list(range(hubs))
    L = list(range(hubs, n // 2))
    Q = list(range(n // 2, n))
    G.add_edges_from((u, v) for u in H for v in L if rnd.random() < 0.7)
    G.add_edges_from((u, v) for i, u in enumerate(Q) for v in Q[i + 1 :] if rnd.random() < 0.7)
    G.add_edges_from((u, rnd.choice(Q)) for u in L)
    return G, 0, n - 1


def path_of_blocks(blocks, size, cross, rnd):
    G = nx.Graph()
    b = [list(range(i * size, (i + 1) * size)) for i in range(blocks)]
    for p in b:
        G.add_edges_from((u, v) for i, u in enumerate(p) for v in p[i + 1 :])
    for i in range(blocks - 1):
        for _ in range(cross):
            G.add_edge(rnd.choice(b[i]), rnd.choice(b[i + 1]))
    return G, b[0][0], b[-1][-1]


rnd = random.Random(5)
cases = [
    ("clusters + medium", *clusters_with_medium(150, 2, 40, 12, rnd), 12),
    ("clusters + medium, sparse", *clusters_with_medium(150, 3, 70, 6, rnd), 6),
    ("hubs + low degree", *bipartite_hubs(150, 12, rnd), 8),
    ("hubs + low degree, D high", *bipartite_hubs(150, 12, rnd), 25),
    ("path of blocks", *path_of_blocks(6, 25, 40, rnd), 15),
    ("path of blocks, thin", *path_of_blocks(10, 15, 10, rnd), 8),
]
print(f"{'case':28} {'n':>4} {'|K|':>4} {'lam':>4} {'D':>3} {'k':>4} {'tK':>4} {'b':>3} {'s':>4} {'C':>6} {'n(1+f/D)':>9} {'C/H':>5}")
for name, G, s, t, D in cases:
    for seed in range(1, 5):
        r = run(G, s, t, D, seed)
        print(f"{name:28} {r['n']:>4} {r['K']:>4} {r['lam']:>4} {D:>3} {r['k']:>4} {r['tK']:>4} {r['b']:>3} {r['s']:>4} {r['C']:>6} {r['bound']:>9.0f} {r['ratio']:>5.2f}")
