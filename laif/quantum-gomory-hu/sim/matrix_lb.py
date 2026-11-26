"""Hard family for all-pairs minimum cut in the adjacency-matrix model.

V = L ∪ R, L = L1 ∪ L2, R = R1 ∪ R2, |L1| = |R1| = s, |L2| = |R2| = h, s < h, s >= 3.
L and R are cliques, L2 x R2 is complete bipartite, and B ⊆ L1 x R1 is arbitrary (the hidden part).
Claim: every cut with both sides of size >= 2 has value >= Δ = 2h + s - 1 (the degree of L2 and R2),
so λ(u, v) = min(deg u, deg v) for all pairs, and λ(x, y) = deg x for x in L1, y in L2. Hence the
all-pairs values give |B| = Σ_{x in L1} (deg x - (h + s - 1)).
Checks: brute force over all cuts (n = 16), Gomory-Hu values on random B (n up to 40), and a mutation
without the L2 x R2 block, where the claim must fail."""
import itertools, random
import networkx as nx

def build(h, s, B, block=True):
    L1 = [f"l1_{i}" for i in range(s)]; L2 = [f"l2_{i}" for i in range(h)]
    R1 = [f"r1_{i}" for i in range(s)]; R2 = [f"r2_{i}" for i in range(h)]
    G = nx.Graph(); G.add_nodes_from(L1 + L2 + R1 + R2)
    for side in (L1 + L2, R1 + R2):
        G.add_edges_from(itertools.combinations(side, 2))
    if block:
        G.add_edges_from((a, b) for a in L2 for b in R2)
    G.add_edges_from((L1[i], R1[j]) for i, j in B)
    return G, L1, L2

def min_nontrivial_cut(G):
    """Minimum value of a cut with both sides of size >= 2 (brute force)."""
    V = list(G); n = len(V); idx = {v: i for i, v in enumerate(V)}
    E = [(idx[a], idx[b]) for a, b in G.edges()]; best = None
    for mask in range(1, 1 << (n - 1)):          # vertex n-1 always on side T
        k = bin(mask).count("1")
        if k < 2 or n - k < 2: continue
        c = sum(((mask >> a) & 1) != ((mask >> b) & 1) for a, b in E)
        best = c if best is None else min(best, c)
    return best

def all_pairs_trivial(G):
    nx.set_edge_attributes(G, 1, "capacity"); T = nx.gomory_hu_tree(G)
    deg = dict(G.degree())
    for u, v in itertools.combinations(G, 2):
        path = nx.shortest_path(T, u, v)
        lam = min(T[a][b]["weight"] for a, b in zip(path, path[1:]))
        if lam != min(deg[u], deg[v]): return False, None
    return True, T

rng = random.Random(7)
h, s = 5, 3; Delta = 2 * h + s - 1
for trial in range(6):
    B = [(i, j) for i in range(s) for j in range(s) if rng.random() < 0.5]
    G, _, _ = build(h, s, B)
    c = min_nontrivial_cut(G)
    assert c >= Delta, (B, c)
    print(f"n=16 B={len(B)}: min cut with both sides >= 2 is {c} >= Δ = {Delta}")
for h, s in ((6, 4), (8, 5), (11, 9)):
    for trial in range(5):
        B = [(i, j) for i in range(s) for j in range(s) if rng.random() < rng.random()]
        G, L1, L2 = build(h, s, B)
        ok, T = all_pairs_trivial(G); assert ok
        deg = dict(G.degree())
        # recover |B| from the values λ(x, y), x in L1, y in L2
        rec = 0
        for x in L1:
            path = nx.shortest_path(T, x, L2[0])
            lam = min(T[a][b]["weight"] for a, b in zip(path, path[1:]))
            rec += lam - (h + s - 1)
        assert rec == len(B), (rec, len(B))
    print(f"n={2*(h+s)}: all λ(u,v) = min(deg u, deg v) and |B| recovered, 5 random B")
# mutation: without the L2 x R2 block the side S = L can be a cheap cut
B = [(0, 0)]
G, _, _ = build(5, 3, B, block=False)
ok, _ = all_pairs_trivial(G)
assert not ok
print("mutation without the L2 x R2 block: nontrivial values appear, as expected")
print("all asserts passed")
