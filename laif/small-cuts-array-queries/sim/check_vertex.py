"""Check that the capped scan of Section 4 gives a vertex-connectivity certificate (classical simulation).

For each forest index i <= k, the forest F_i of the capped scan must be a scan-first search forest of
G_{i-1} = G - (F_1 u ... u F_{i-1}) in the scan order (Lemma 5): whenever an unscanned vertex is marked
at level i (r(w) >= i), the next scanned vertex is marked at level i, and F_i holds exactly the edges by
which each vertex is first reached in G_{i-1}. Then asserts kappa(H_k) >= min(k, kappa(G)), and
kappa(H_k) = kappa(G) whenever kappa(H_k) < k (Corollary 6). Mutation: two maximal spanning forests
that are not scan-first, on a 2-connected graph with 5 vertices, whose union has a cut vertex.
"""
import random
import networkx as nx
from check_scan import scan, graphs


def scan_order(G, k, rng):
    r = {v: 0 for v in G}; scanned = []; F = [[] for _ in range(k)]; S = set()
    while len(S) < len(G):
        best = max(min(k, r[w]) for w in G if w not in S)
        v = rng.choice([w for w in G if w not in S and min(k, r[w]) == best])
        for i in range(1, k + 1):   # scan-first rule at level i
            if any(r[w] >= i for w in G if w not in S):
                assert r[v] >= i, "scan-first rule"
        S.add(v); scanned.append(v)
        for w in G[v]:
            if w not in S and r[w] < k:
                F[r[w]].append((v, w)); r[w] += 1
    return F, scanned


def first_reach_forest(G, used, order):
    """Scan-first search forest of G - used in the given scan order."""
    pos = {v: j for j, v in enumerate(order)}; T = set()
    for w in G:
        nb = [u for u in G[w] if pos[u] < pos[w] and frozenset((u, w)) not in used]
        if nb:
            T.add(frozenset((min(nb, key=pos.get), w)))
    return T


def kappa(G):
    n = len(G)
    return n - 1 if G.number_of_edges() == n * (n - 1) // 2 else nx.node_connectivity(G)


def main():
    rng = random.Random(11); cnt = 0
    for G in graphs(rng):
        if not nx.is_connected(G):
            continue
        kg = kappa(G)
        for k in (1, 2, 3, 5):
            F, order = scan_order(G, k, rng)
            used = set()
            for i in range(k):
                assert {frozenset(e) for e in F[i]} == first_reach_forest(G, used, order), ("forest", i)
                used |= {frozenset(e) for e in F[i]}
            H = nx.Graph(); H.add_nodes_from(G); H.add_edges_from(e for Fi in F for e in Fi)
            kh = kappa(H) if nx.is_connected(H) else 0
            assert kh >= min(k, kg) and kh <= kg, (kh, kg, k)
            if kh < k:
                assert kh == kg
            cnt += 1
    print(f"{cnt} capped scans checked: scan-first forests, kappa(H_k) >= min(k, kappa(G))")
    # mutation: maximal spanning forests that are not scan-first. G is 2-connected (a 5-cycle 0-1-2-3-4
    # with chords 1-3, 1-4); F_1 = path 4-0-1-2-3 is a spanning tree, F_2 = {13, 14} is a maximal spanning
    # forest of the triangle 1-3-4 that is left, and vertex 1 cuts F_1 u F_2.
    G = nx.Graph([(0, 1), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (3, 4)])
    F1 = [(4, 0), (0, 1), (1, 2), (2, 3)]; F2 = [(1, 3), (1, 4)]
    R = nx.Graph(G); R.remove_edges_from(F1)
    assert nx.is_tree(nx.Graph(F1)) and len(nx.Graph(F1)) == 5
    assert nx.is_forest(nx.Graph(F2)) and all(nx.has_path(nx.Graph(F2), a, b) for a, b in R.edges())
    assert kappa(G) == 2 and kappa(nx.Graph(F1 + F2)) == 1, "mutation survived"
    for seed in range(50):
        F, _ = scan_order(G, 2, random.Random(seed))
        assert kappa(nx.Graph([e for Fi in F for e in Fi])) == 2
    print("mutation (maximal spanning forests that are not scan-first): kappa drops from 2 to 1 on a 5-vertex graph")

if __name__ == "__main__":
    main()
