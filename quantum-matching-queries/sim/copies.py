"""Do copies of the adversary's gadgets force hybrid cost ~ sqrt n?

Three numbers per instance, each counted in units of O(n) edge reveals:
  cost_d    = min_r [(r+1) + d_r]        LP rounds, then one phase per unit of deficiency
  cost_pass = min_r [(r+1) + passes_r]   LP rounds, then passes from the rounded matching
  pure      = passes from the empty matching, with no LP at all (the baseline to beat)
A pass finds a maximal set of disjoint augmenting paths, not only shortest ones.

ponytail: dense O(n^3) blossom search, fine up to a few thousand vertices.
"""
import json
import random
import sys

import networkx as nx
import numpy as np

import rounds as R
from hybrid import nu


def augment_search(adj, match, root, alive):
    """Edmonds search from free vertex root inside alive. Returns (path end or None, visited)."""
    n = len(adj)
    parent, base = [-1] * n, list(range(n))
    used, blossom = [False] * n, [False] * n
    used[root] = True
    visited = {root}
    queue = [root]

    def lca(a, b):
        seen = set()
        while True:
            a = base[a]
            seen.add(a)
            if match[a] == -1:
                break
            a = parent[match[a]]
        while True:
            b = base[b]
            if b in seen:
                return b
            b = parent[match[b]]

    def mark(v, b, child):
        while base[v] != b:
            blossom[base[v]] = blossom[base[match[v]]] = True
            parent[v] = child
            child = match[v]
            v = parent[match[v]]

    i = 0
    while i < len(queue):
        v = queue[i]
        i += 1
        for to in adj[v]:
            if to not in alive or base[v] == base[to] or match[v] == to:
                continue
            if to == root or (match[to] != -1 and parent[match[to]] != -1):
                b = lca(v, to)
                for k in range(n):
                    blossom[k] = False
                mark(v, b, to)
                mark(to, b, v)
                for k in range(n):
                    if blossom[base[k]]:
                        base[k] = b
                        if not used[k]:
                            used[k] = True
                            visited.add(k)
                            queue.append(k)
            elif parent[to] == -1:
                parent[to] = v
                visited.add(to)
                if match[to] == -1:
                    u = to
                    while u != -1:
                        p = parent[u]
                        nxt = match[p]
                        match[u], match[p] = p, u
                        u = nxt
                    return to, visited
                used[match[to]] = True
                visited.add(match[to])
                queue.append(match[to])
    return None, visited


def passes(G, start=(), order_seed=0):
    """Passes until maximum, counting the final pass that certifies optimality."""
    idx = {v: i for i, v in enumerate(G.nodes)}
    adj = [[] for _ in idx]
    for u, v in G.edges:
        adj[idx[u]].append(idx[v])
        adj[idx[v]].append(idx[u])
    rng = random.Random(order_seed)
    for a in adj:
        rng.shuffle(a)
    match = [-1] * len(adj)
    for u, v in start:
        match[idx[u]], match[idx[v]] = idx[v], idx[u]
    count = 0
    while True:
        count += 1
        alive, found = set(range(len(adj))), 0
        free = [v for v in range(len(adj)) if match[v] == -1]
        rng.shuffle(free)
        for root in free:
            if root not in alive or match[root] != -1:
                continue
            end, visited = augment_search(adj, match, root, alive)
            alive -= visited
            found += end is not None
        if not found:
            assert sum(m != -1 for m in match) // 2 == nu(G)
            return count


def evaluate(G, cap=400):
    edges = list(G.edges)
    n, opt = G.number_of_nodes(), nu(G)
    pure = passes(G)
    c = np.ones(len(edges))
    H = nx.Graph()
    H.add_nodes_from(G.nodes)
    F, last = [], None
    best_d, best_p = 10**9, 10**9
    for r in range(cap):
        if r + 1 >= min(best_d, best_p):
            break
        x, duals = R.solve_lp(G, edges, F, c)
        H.add_edges_from(e for e, xe in zip(edges, x) if xe > R.EPS)
        M = nx.max_weight_matching(H, maxcardinality=True)
        d = opt - len(M)
        best_d = min(best_d, r + 1 + d)
        best_p = min(best_p, r + 1 + passes(G, M))
        if d == 0:
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
    return best_d, best_p, pure


if __name__ == "__main__":
    # self-check: the pass counter must reach the true maximum on random graphs (asserted inside)
    for seed in range(200):
        g = nx.gnp_random_graph(30, 0.1, seed=seed)
        passes(g, order_seed=seed)
    print("self-check ok")
    best = json.load(open("adversary_best.json"))
    print("  s  r_prim   c  bridge     n  sqrt(n)  cost_d  cost_pass  pure_passes")
    for s, rec in best.items():
        g = nx.Graph()
        g.add_edges_from(rec["edges"])
        g = nx.convert_node_labels_to_integers(g)
        size = g.number_of_nodes()
        for c in (1, 5, 10, 20):
            for bridge in (0, 1.0):
                if c == 1 and bridge:
                    continue
                rng = random.Random(c)
                G = nx.disjoint_union_all([g.copy() for _ in range(c)])
                for _ in range(int(bridge * c)):
                    i, j = rng.randrange(c), rng.randrange(c)
                    if i != j:
                        G.add_edge(size * i + rng.randrange(size), size * j + rng.randrange(size))
                d, p, pure = evaluate(G)
                n = G.number_of_nodes()
                print(f"{s:>3s} {rec['r_primal']:>6d} {c:>3d} {bridge:>7.1f} {n:>5d} {n**.5:>8.1f} {d:>7d} {p:>10d} {pure:>12d}", flush=True)
