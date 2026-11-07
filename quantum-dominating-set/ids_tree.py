"""Decision version of the basic branching of Bourgeois, Escoffier and Paschos (arXiv:0905.1993, Lemma 1) for
Independent Dominating Set: with free vertices W, pick a vertex v of minimum degree; some free u in N[v] is in the
solution; branch over u in increasing degree order, marking the neighbours already tried. Each branch removes N[u]
and lowers the budget by one, so the procedure is an OR tree. The full algorithm refines the choice of branchings
and keeps this form. Compared with brute force on random graphs."""
import itertools
import random
import networkx as nx

random.seed(7)


def decide(G, W, k, cnt):
    """True iff some independent set D inside W of size at most k dominates every vertex of G."""
    cnt[0] += 1
    if G.number_of_nodes() == 0:
        return k >= 0
    if k <= 0:
        return False
    v = min(G.nodes(), key=lambda x: (G.degree(x), str(x)))
    choices = sorted((u for u in set(G.neighbors(v)) | {v} if u in W), key=lambda x: (G.degree(x), str(x)))
    tried = set()
    for u in choices:                                  # OR over the vertex that dominates v
        H = G.copy()
        H.remove_nodes_from(set(G.neighbors(u)) | {u})
        if decide(H, (W - set(G.neighbors(u)) - {u}) - tried, k - 1, cnt):
            return True
        tried.add(u)                                   # later branches may not use u
    return False


def brute(G):
    V = list(G.nodes())
    for r in range(len(V) + 1):
        for D in itertools.combinations(V, r):
            if all(not G.has_edge(a, b) for a, b in itertools.combinations(D, 2)) and \
               all(x in D or any(G.has_edge(x, d) for d in D) for x in V):
                return r


if __name__ == "__main__":
    for trial in range(400):
        n = random.randint(3, 13)
        G = nx.gnp_random_graph(n, random.choice([0.2, 0.35, 0.5]), seed=random.randint(0, 10**9))
        g, k, cnt = brute(G), 0, [0]
        while not decide(G, set(G.nodes()), k, cnt):
            k += 1
        assert k == g, (n, list(G.edges()), k, g)
    print("400 random graphs, n = 3..13: smallest accepted budget = independent domination number in every case")
