"""Classical check of the steps of the vertex connectivity algorithm (exact arithmetic, small graphs).

(a) s-t reduction to bipartite matching: for non-adjacent s, t,
    kappa(s,t) = |N(s) & N(t)| + nu(B) - |V0 - (A | B)|, with V0 = V - {s,t} - (N(s) & N(t)),
    A = N(s) - N(t), B = N(t) - N(s), and B the bipartite graph of Lemma 2.
(b) one sink for all: in the graph G2 of Lemma 3 (copy V' of V joined to a new vertex s*, copies B_i of
    V - N[s_i] for sampled s_i, each joined inside by G and to the copies in V' of its neighbours in N(s_i)), the least |N(L)| over nonempty L inside the copies equals kappa(G) when
    some s_i lies on the larger side of a minimum cut, and is never below kappa(G).
(c) cluster formula of Lemma 5: |N(L)| = a_C + b_C(L) for all nonempty L inside a vertex set C.
(d) Lemma 4: in a minimum t-sink cut (L, S, R), |N(u) ^ N(v)| <= 2|L| for u, v in L.
(e) both phases: Phase 1 (three sampled sources) is never below the minimum t-sink cut and attains it
    when a source lies in a minimizer; Phase 2 (closed neighbourhoods of the exact difference graph with
    threshold 2 l0, l0 = 2, as clusters) is never below it and attains it when a minimizer has at most l0
    vertices.
Mutations: (a) without the common neighbours, (b) with B_i joined to the copies of all neighbours,
(c) without the term a_C; each must fail.
"""
import itertools, random
import networkx as nx

def kappa(G):
    n = len(G)
    return n - 1 if G.number_of_edges() == n * (n - 1) // 2 else nx.node_connectivity(G)

def st_by_matching(G, s, t, common=True):
    Ns, Nt = set(G[s]), set(G[t]); C = Ns & Nt
    V0 = set(G) - {s, t} - C; A = Ns - Nt; B = Nt - Ns
    H = nx.Graph(); X = [("x", v) for v in V0 - B]; Y = [("y", v) for v in V0 - A]
    H.add_nodes_from(X, bipartite=0); H.add_nodes_from(Y, bipartite=1)
    for v in V0 - A - B:
        H.add_edge(("x", v), ("y", v))
    for u, w in G.edges():
        for a, b in ((u, w), (w, u)):
            if a in V0 - B and b in V0 - A:
                H.add_edge(("x", a), ("y", b))
    nu = len(nx.bipartite.hopcroft_karp_matching(H, top_nodes=X)) // 2 if H.number_of_edges() else 0
    return (len(C) if common else 0) + nu - len(V0 - A - B)

def NL(G, L):
    return set().union(*(set(G[v]) for v in L)) - set(L)

def min_sink_cut(G, t):
    U = [v for v in G if v != t and v not in G[t]]
    return min(nx.node_connectivity(G, v, t) for v in U) if U else None

def combined(G, sinks, printed=False):
    G2 = nx.Graph(); G2.add_node("s*")
    for v in G:
        G2.add_edge("s*", ("c", v))
    for i, si in enumerate(sinks):
        Bi = [v for v in G if v != si and v not in G[si]]
        for v in Bi:
            G2.add_node((i, v))
            for u in G[v]:
                if u in Bi:
                    G2.add_edge((i, v), (i, u))
                if printed or u not in Bi:   # u in N(s_i): the copy of u in V'
                    G2.add_edge((i, v), ("c", u))
    return G2

def graphs(rng, N):
    for _ in range(N):
        n = rng.randint(6, 12)
        yield nx.gnp_random_graph(n, rng.choice([0.3, 0.5, 0.7, 0.85]), seed=rng.randrange(10**9))
    for _ in range(N):   # small side L attached to a separator S inside a dense rest
        l, s, r = rng.randint(1, 3), rng.randint(1, 4), rng.randint(3, 7)
        G = nx.complete_graph(l + s + r)
        for a in range(l):
            for b in range(l + s, l + s + r):
                G.remove_edge(a, b)
        for _ in range(rng.randint(0, 6)):
            a, b = rng.sample(range(l + s + r), 2)
            if G.has_edge(a, b) and rng.random() < 0.5:
                G.remove_edge(a, b)
        yield G

def phase2(G, t, l0, rng):
    U = [v for v in G if v != t and v not in G[t]]
    # difference graph with the exact threshold 2 l0 (the sketch is a probability statement, not simulated)
    Gd = nx.Graph(); Gd.add_nodes_from(U)
    for u, v in itertools.combinations(U, 2):
        if len(set(G[u]) ^ set(G[v])) <= 2 * l0:
            Gd.add_edge(u, v)
    clusters = [set(Gd[v]) | {v} for v in U]   # closed neighbourhoods: a cover, not sparse
    best = None
    for C in clusters:
        c = next(iter(C)); D = set().union(*(set(G[c]) ^ set(G[v]) for v in C))
        a = len(set(G[c]) - D - C)
        for k in range(1, min(len(C), l0) + 1):
            for L in itertools.combinations(sorted(C), k):
                b = 0
                for x in (D | C) - set(L):
                    if any((x in G[c]) != (x in (set(G[c]) ^ set(G[v]))) for v in L):
                        b += 1
                val = a + b
                assert val == len(NL(G, L))
                best = val if best is None else min(best, val)
    return best

def main():
    rng = random.Random(2); na = nb = nc = nd = ne = 0; mut_a = mut_b = mut_c = 0
    for G in graphs(rng, 40):
        if not nx.is_connected(G) or G.number_of_edges() == len(G) * (len(G) - 1) // 2:
            continue
        # (a)
        for s, t in itertools.combinations(G, 2):
            if not G.has_edge(s, t):
                k = nx.node_connectivity(G, s, t)
                assert st_by_matching(G, s, t) == k; na += 1
                mut_a += st_by_matching(G, s, t, common=False) != k
        kg = kappa(G)
        # (b) all vertices as sinks: equality; random sinks: never below
        G2 = combined(G, list(G))
        Ls = [v for v in G2 if v != "s*" and v[0] != "c"]
        val = min(nx.node_connectivity(G2, v, "s*") for v in Ls)
        assert val == kg, (val, kg); nb += 1
        Gp = combined(G, list(G), printed=True)
        mut_b += min(nx.node_connectivity(Gp, v, "s*") for v in Ls) != kg
        G3 = combined(G, rng.sample(list(G), 2))
        Ls3 = [v for v in G3 if v != "s*" and v[0] != "c"]
        if Ls3:
            assert min(nx.node_connectivity(G3, v, "s*") for v in Ls3) >= kg
        # (c) random sets C, every L
        C = set(rng.sample(list(G), min(len(G), 5))); c = next(iter(C))
        D = set().union(*(set(G[c]) ^ set(G[v]) for v in C)); a = len(set(G[c]) - D - C)
        for k in range(1, len(C) + 1):
            for L in itertools.combinations(sorted(C), k):
                b = sum(1 for x in (D | C) - set(L)
                        if any((x in G[c]) != (x in (set(G[c]) ^ set(G[v]))) for v in L))
                assert a + b == len(NL(G, L)); nc += 1
                mut_c += (b != len(NL(G, L)))
        # (d), (e) for each sink
        for t in G:
            U = [v for v in G if v != t and v not in G[t]]
            if not U:
                continue
            m = min_sink_cut(G, t)
            for k in range(1, len(U) + 1):
                for L in itertools.combinations(U, k):
                    if len(NL(G, L)) == m:
                        for u, v in itertools.combinations(L, 2):
                            assert len(set(G[u]) ^ set(G[v])) <= 2 * len(L)
                        nd += 1
            l0 = 2
            P = rng.sample(U, min(len(U), 3))
            ph1 = min(nx.node_connectivity(G, v, t) for v in P)
            assert ph1 >= m
            if any(len(NL(G, L)) == m for k in range(1, len(U) + 1) for L in itertools.combinations(U, k)
                   if set(L) & set(P)):
                assert ph1 == m
            # minimizers with |L| > l0 must be hit by P for Phase 1; record whether a small minimizer exists
            small = any(len(NL(G, L)) == m for k in range(1, l0 + 1) for L in itertools.combinations(U, k))
            ph2 = phase2(G, t, l0, rng)
            assert ph2 >= m
            if small:
                assert ph2 == m
            ne += 1
    assert mut_a > 0 and mut_b > 0 and mut_c > 0, "mutation survived"
    print(f"(a) {na} pairs, (b) {nb} graphs, (c) {nc} sets, (d) {nd} minimizers, (e) {ne} sinks: all asserts passed")
    print(f"mutations: (a) without common neighbours wrong on {mut_a} pairs, (b) as printed in [3] wrong on {mut_b} graphs, (c) without a_C wrong on {mut_c} sets")

if __name__ == "__main__":
    main()
