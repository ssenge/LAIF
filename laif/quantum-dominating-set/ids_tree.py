"""Decision version of the basic branching of Bourgeois, Escoffier and Paschos (arXiv:0905.1993, Lemma 1) for
Independent Dominating Set: with free vertices W, pick a vertex v of minimum degree, preferring one with a neighbour
of larger degree; some free u in N[v] is in the solution; branch over u in increasing degree order, marking the
neighbours already tried. Each branch removes N[u] and lowers the budget by one, so the procedure is an OR tree. A
connected component with at most K vertices is solved directly, with one call on the rest. The full algorithm refines
the choice of branchings and keeps this form. Compared with brute force on random graphs. On disjoint unions of
regular graphs, a root-leaf path has at most 4n/K branchings on a vertex of a regular component of degree 2 to 5."""
import itertools
import random
import networkx as nx

random.seed(7)


def small(G, H, W):
    """Smallest independent set inside W that dominates the vertex set H of a component of G, or None."""
    for r in range(len(H) + 1):
        for D in itertools.combinations(sorted(H & W, key=str), r):
            if all(not G.has_edge(a, b) for a, b in itertools.combinations(D, 2)) and \
               all(x in D or any(G.has_edge(x, d) for d in D) for x in H):
                return r
    return None


def decide(G, W, k, K, bad=0, stats=None):
    """True iff some independent set D inside W of size at most k dominates every vertex of G. With stats, the tree is
    explored in full, and stats[0] records the largest number of bad branchings on a root-leaf path."""
    if stats is not None:
        stats[0] = max(stats[0], bad)
    if G.number_of_nodes() == 0:
        return k >= 0
    for H in map(set, nx.connected_components(G)):
        if len(H) <= K:                                # one call on the rest
            opt = small(G, H, W)
            if opt is None:
                return False
            R = G.copy()
            R.remove_nodes_from(H)
            return decide(R, W - H, k - opt, K, bad, stats)
    if k <= 0:
        return False
    delta = min(d for _, d in G.degree())
    mins = sorted((x for x in G.nodes() if G.degree(x) == delta), key=str)
    v = next((x for x in mins if any(G.degree(y) > delta for y in G.neighbors(x))), mins[0])
    regular = all(G.degree(x) == delta for x in nx.node_connected_component(G, v))
    bad += regular and 2 <= delta <= 5
    choices = sorted((u for u in set(G.neighbors(v)) | {v} if u in W), key=lambda x: (G.degree(x), str(x)))
    tried, found = set(), False
    for u in choices:                                  # OR over the vertex that dominates v
        H = G.copy()
        H.remove_nodes_from(set(G.neighbors(u)) | {u})
        if decide(H, (W - set(G.neighbors(u)) - {u}) - tried, k - 1, K, bad, stats):
            if stats is None:
                return True
            found = True
        tried.add(u)                                   # later branches may not use u
    return found


if __name__ == "__main__":
    for K in (0, 4):
        for trial in range(200):
            n = random.randint(3, 13)
            G = nx.gnp_random_graph(n, random.choice([0.2, 0.35, 0.5]), seed=random.randint(0, 10**9))
            g, k = small(G, set(G.nodes()), set(G.nodes())), 0
            while not decide(G, set(G.nodes()), k, K):
                k += 1
            assert k == g, (n, list(G.edges()), k, g)
    print("400 random graphs, n = 3..13, K = 0 and 4: smallest accepted budget = independent domination number in every case")

    parts = [nx.cycle_graph(5), nx.cycle_graph(8), nx.complete_bipartite_graph(3, 3), nx.complete_bipartite_graph(4, 4),
             nx.complete_graph(5), nx.complete_graph(6), nx.petersen_graph()]
    K, worst = 4, 0
    for trial in range(60):
        G = nx.disjoint_union_all(random.choices(parts, k=random.randint(1, 3)))
        stats = [0]
        decide(G, set(G.nodes()), G.number_of_nodes(), K, 0, stats)
        assert stats[0] <= 4 * G.number_of_nodes() / K, list(G.edges())
        worst = max(worst, stats[0] / G.number_of_nodes())
    print(f"60 unions of regular graphs, K = {K}: bad branchings on a path / n at most {worst:.3f} <= 4/K = {4 / K}")

    triangles = nx.disjoint_union_all([nx.complete_graph(3)] * 6)
    without, with_rule = [0], [0]
    decide(triangles, set(triangles.nodes()), 18, 0, 0, without)
    decide(triangles, set(triangles.nodes()), 18, 4, 0, with_rule)
    assert (without[0], with_rule[0]) == (6, 0)
    print(f"6 disjoint triangles: {without[0]} bad branchings on a path with K = 0, {with_rule[0]} with K = 4")
