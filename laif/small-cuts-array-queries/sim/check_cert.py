"""Check of the forest certificate and of the round algorithm (classical simulation).

Graphs are simple, given as adjacency arrays in random order. Round i builds a maximal
spanning forest F_i of G_i = G - (F_1 u ... u F_{i-1}) in two phases:
  Phase 1: grow stars from vertices of largest residual degree (DHHM Lemma 10 with residual degrees),
           reading list entries in order; known entries are free, unknown removed entries are read once.
  Phase 2: repeatedly take the unfinished component of least total list length N_C and search its
           lists for an entry that is a residual edge leaving C; a search with t marked entries is
           charged sqrt(N_C / t), a search with none sqrt(N_C) (times a log factor, counted apart).
Asserts:
  - every F_i is a maximal spanning forest of G_i, a star joins only a component of at least d + 1
    vertices (d the residual degree of its root), and the Phase 1 components satisfy
    sum of residual degrees <= |C|^2;
  - certificate: for every s-t pair, lambda_st(H) >= min(k, lambda_st(G)) for H = F_1 u ... u F_k,
    and lambda(H) = lambda(G) when lambda(H) < k;
  - the query count of round i is at most C0 * (n + sqrt(2 n |R_i|)) + (holes read), reported as a ratio.
"""
import math
import random
import networkx as nx


class Arr:
    def __init__(self, G, rng):
        self.n = G.number_of_nodes()
        self.lst = {v: rng.sample(sorted(G[v]), len(G[v])) for v in G}
        self.known = {v: {} for v in G}  # position -> neighbour
        self.queries = 0

    def deg(self, v):
        return len(self.lst[v])

    def read(self, v, j):
        if j not in self.known[v]:
            self.queries += 1
            self.known[v][j] = self.lst[v][j]
        return self.known[v][j]


def edge(u, w):
    return (u, w) if u < w else (w, u)


def one_round(A, R, rng):
    """Maximal spanning forest of G - R. Returns forest edges, phase-1 query count, phase-2 cost."""
    n = A.n
    V = list(range(n))
    rdeg = {u: A.deg(u) for u in V}
    for (a, b) in R:
        rdeg[a] -= 1
        rdeg[b] -= 1
    comp = {}
    members = {}
    F = []
    q0 = A.queries
    S = set(V)
    k = 0
    while S:
        v = max(S, key=lambda u: (rdeg[u], -u))
        D = [v]
        merged = None
        for j in range(A.deg(v)):
            w = A.read(v, j)
            if edge(v, w) in R:
                continue
            if w in comp:
                merged = comp[w]
                F.append(edge(v, w))
                break
            if w in S and w not in D:
                D.append(w)
                F.append(edge(v, w))
        if merged is None:
            k += 1
            cid = k
            members[cid] = []
        else:
            cid = merged
            assert len(members[cid]) >= rdeg[v] + 1, "phase-1 a >= d + 1"
        for u in D:
            comp[u] = cid
            members[cid].append(u)
            S.discard(u)
    for cid, mem in members.items():
        assert sum(rdeg[u] for u in mem) <= len(mem) ** 2, "phase-1 degree bound"
    q1 = A.queries - q0
    # phase 2
    N = {cid: sum(A.deg(u) for u in mem) for cid, mem in members.items()}
    unfinished = set(members)
    cost_succ = 0.0
    cost_fail = 0.0
    while unfinished:
        c = min(unfinished, key=lambda x: (N[x], x))
        marked = [(u, j) for u in members[c] for j in range(A.deg(u))
                  if comp[A.lst[u][j]] != c and edge(u, A.lst[u][j]) not in R]
        if not marked:
            cost_fail += math.sqrt(N[c])
            unfinished.discard(c)
            continue
        cost_succ += math.sqrt(N[c] / len(marked))
        u, j = rng.choice(marked)
        w = A.read(u, j)
        F.append(edge(u, w))
        d = comp[w]
        # merge d into c
        for x in members[d]:
            comp[x] = c
        members[c] += members[d]
        N[c] += N[d]
        del members[d], N[d]
        unfinished.discard(d)
    return F, q1, cost_succ, cost_fail


def check_forest(G, R, F):
    Gi = G.copy()
    Gi.remove_edges_from(R)
    T = nx.Graph()
    T.add_nodes_from(G)
    T.add_edges_from(F)
    assert all(Gi.has_edge(*e) for e in F)
    assert nx.is_forest(T)
    assert nx.number_connected_components(T) == nx.number_connected_components(Gi)
    for c in nx.connected_components(Gi):
        assert nx.is_connected(T.subgraph(c))


def certificate(G, k, rng):
    A = Arr(G, rng)
    R = set()
    Fs = []
    stats = []
    n = G.number_of_nodes()
    for i in range(k):
        F, q1, cs, cf = one_round(A, R, rng)
        check_forest(G, R, F)
        bound = n + math.sqrt(2 * n * len(R))
        stats.append((q1, cs, cf, bound))
        R |= set(F)
        Fs.append(F)
    H = nx.Graph()
    H.add_nodes_from(G)
    H.add_edges_from(R)
    return H, stats


def lam_st(G, s, t):
    if not nx.has_path(G, s, t):
        return 0
    return nx.edge_connectivity(G, s, t)


def lam(G):
    if not nx.is_connected(G):
        return 0
    return nx.edge_connectivity(G)


def graphs(rng):
    for _ in range(30):
        n = rng.randint(6, 16)
        yield nx.gnp_random_graph(n, rng.choice([0.2, 0.4, 0.6, 0.9]), seed=rng.randrange(10**9))
    for _ in range(15):
        a, b = rng.randint(3, 8), rng.randint(3, 8)
        G = nx.disjoint_union(nx.complete_graph(a), nx.complete_graph(b))
        f = rng.randint(0, min(a, b))
        for i in range(f):
            G.add_edge(i, a + i)
        yield G
    for _ in range(10):
        n = rng.randint(8, 16)
        d = rng.choice([2, 3, 4])
        if n * d % 2 == 0:
            yield nx.random_regular_graph(d, n, seed=rng.randrange(10**9))
    for _ in range(10):  # hubs: few centers joined to everything plus sparse rest
        n = rng.randint(8, 16)
        G = nx.gnp_random_graph(n, 0.15, seed=rng.randrange(10**9))
        for h in range(rng.randint(1, 3)):
            for v in range(n):
                if v != h:
                    G.add_edge(h, v)
        yield G


def main():
    rng = random.Random(1)
    worst = 0.0
    count = 0
    for G in graphs(rng):
        G = nx.convert_node_labels_to_integers(G)
        for k in (1, 2, 3, 4, 6):
            H, stats = certificate(G, k, rng)
            count += 1
            n = G.number_of_nodes()
            for s in range(n):
                for t in range(s + 1, n):
                    assert lam_st(H, s, t) >= min(k, lam_st(G, s, t))
            lh = lam(H)
            if lh < k:
                assert lh == lam(G)
            else:
                assert lam(G) >= k
            for (q1, cs, cf, bound) in stats:
                worst = max(worst, (q1 + cs + cf) / bound)
    print(f"{count} certificates checked, worst (round cost)/(n + sqrt(2n|R|)) = {worst:.2f}")
    # scaling on larger graphs: cost of k rounds against n k^{3/2} and n k
    for (name, G) in [("dense gnp n=300 p=0.5", nx.gnp_random_graph(300, 0.5, seed=3)),
                      ("two cliques n=300 joined by 3 edges", None),
                      ("hubs n=300", None)]:
        if G is None and name.startswith("two"):
            G = nx.disjoint_union(nx.complete_graph(150), nx.complete_graph(150))
            for i in range(3):
                G.add_edge(i, 150 + i)
        if G is None and name.startswith("hubs"):
            G = nx.gnp_random_graph(300, 0.05, seed=4)
            for h in range(10):
                for v in range(300):
                    if v != h:
                        G.add_edge(h, v)
        n = G.number_of_nodes()
        for k in (1, 2, 4, 8, 16):
            H, stats = certificate(G, k, random.Random(k))
            tot = sum(q1 + cs + cf for (q1, cs, cf, _) in stats)
            print(f"{name}: k={k:2d} cost={tot:9.0f}  /(n k)={tot/(n*k):5.2f}  /(n k^1.5)={tot/(n*k**1.5):5.2f}"
                  f"  lambda(H)={lam(H)}")


if __name__ == "__main__":
    main()
