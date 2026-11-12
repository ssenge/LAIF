"""Checks of the st-connectivity reduction for trees made of a path p_1..p_k with leaves at three consecutive
path vertices. The auxiliary multigraph G' is built explicitly: s, t, one node per vertex of a path colour, and for
every pair (x, y) with consecutive path colours a private chain
    x -- [leaf bundles of x] -- [edge A_xy] -- [leaf bundles of y] -- y,
where a leaf bundle of x for a leaf colour c is a set of parallel edges labelled A_xu, one per u of colour c.
Checked on random small graphs and colourings:
  soundness:    s, t connected in G'(G)  =>  T is a subgraph of G (brute force),
  completeness: a copy of T coloured by its own vertex names  =>  s, t connected,
  resistance:   on correctly coloured inputs, R_st <= k + 1 + 2(#leaves), the length of the copy's chain path,
  capacitance:  min cut (absent edges cost 1, present edges are uncuttable)
                <= #absent consecutive pairs + sum over present consecutive pairs of the smallest false bundle.
Zig-zag walks with shared leaves: never accepted without a copy for three consecutive positions; accepted without\na copy for four."""
import itertools
import random
import networkx as nx
from networkx.algorithms import isomorphism

random.seed(5)


def tree(k, i, d):
    """Path p_0..p_{k-1}; d[j] leaves at p_{i+j}. Returns (T, path, leaf lists)."""
    T, leaves = nx.path_graph(k), {}
    nxt = k
    for j, cnt in enumerate(d):
        leaves[i + j] = list(range(nxt, nxt + cnt))
        T.add_edges_from((i + j, w) for w in leaves[i + j])
        nxt += cnt
    return T, list(range(k)), leaves


def aux(G, col, k, leaves):
    """G' as a MultiGraph; every edge has attribute lab = None (free) or the pair (a, b) of G it reads."""
    H = nx.MultiGraph()
    H.add_nodes_from(["s", "t"])
    by = {c: [v for v in G if col[v] == c] for c in set(col.values())}
    for v in by.get(0, []):
        H.add_edge("s", ("v", v), lab=None)
    for v in by.get(k - 1, []):
        H.add_edge(("v", v), "t", lab=None)
    for j in range(k - 1):
        for x in by.get(j, []):
            for y in by.get(j + 1, []):
                chain = [("v", x)]
                segs = [(x, c) for c in leaves.get(j, [])] + ["edge"] + [(y, c) for c in leaves.get(j + 1, [])]
                for idx, seg in enumerate(segs):
                    a, b = chain[-1], ("c", x, y, idx) if idx < len(segs) - 1 else ("v", y)
                    if seg == "edge":
                        H.add_edge(a, b, lab=(x, y))
                    else:
                        z, c = seg
                        for u in by.get(c, []):
                            H.add_edge(a, b, lab=(z, u))
                    chain.append(b)
    return H


def present(H, G):
    P = nx.Graph()
    P.add_nodes_from(H)
    P.add_edges_from((a, b) for a, b, lab in H.edges(data="lab") if lab is None or G.has_edge(*lab))
    return P


def min_cut(H, G):
    F = nx.DiGraph()
    F.add_nodes_from(["s", "t"])
    for a, b, lab in H.edges(data="lab"):
        cap = float("inf") if lab is None or G.has_edge(*lab) else 1
        for u, v in ((a, b), (b, a)):
            F.add_edge(u, v, capacity=F[u][v]["capacity"] + cap if F.has_edge(u, v) else cap)
    return nx.minimum_cut_value(F, "s", "t")


def cut_bound(G, col, k, leaves):
    by = {c: [v for v in G if col[v] == c] for c in set(col.values())}
    total = 0
    for j in range(k - 1):
        for x in by.get(j, []):
            for y in by.get(j + 1, []):
                if not G.has_edge(x, y):
                    total += 1
                    continue
                sizes = [len(by.get(c, [])) for z, cs in ((x, leaves.get(j, [])), (y, leaves.get(j + 1, [])))
                         for c in cs if not any(col[u] == c for u in G[z])]
                total += min(sizes, default=0)
    return total


def contains(G, T):
    return any(True for _ in isomorphism.GraphMatcher(G, T).subgraph_monomorphisms_iter())


def run(k, i, d, trials, nmax, p):
    T, path, leaves = tree(k, i, d)
    colours = list(T.nodes())
    sound = comp = 0
    for _ in range(trials):
        n = random.randint(len(T), nmax)
        G = nx.gnp_random_graph(n, p, seed=random.randint(0, 10**9))
        has = contains(G, T)
        if has and random.random() < 0.5:               # plant the colouring of one copy
            phi = next(isomorphism.GraphMatcher(G, T).subgraph_monomorphisms_iter())   # G-vertex -> T-vertex
            col = {v: phi.get(v, random.choice(colours)) for v in G}
        else:
            col = {v: random.choice(colours) for v in G}
        H = aux(G, col, k, leaves)
        conn = nx.has_path(present(H, G), "s", "t")
        if conn:
            assert has, ("soundness", k, i, d, list(G.edges()), col)
            sound += 1
        else:
            assert min_cut(H, G) <= cut_bound(G, col, k, leaves), "capacitance"
        if has:
            gm = isomorphism.GraphMatcher(G, T)
            for phi2 in itertools.islice(gm.subgraph_monomorphisms_iter(), 20):
                if all(col[v] == t for v, t in phi2.items()):
                    assert conn, ("completeness", list(G.edges()), col)
                    P = present(H, G)
                    R = nx.resistance_distance(nx.Graph(P.subgraph(nx.node_connected_component(P, "s"))), "s", "t")
                    assert R <= k + 1 + 2 * sum(d) + 1e-9, R      # length of the chain path of the copy
                    comp += 1
                    break
    return sound, comp


def main():
    cases = [(6, 2, (0, 1, 1)), (6, 1, (1, 1, 1)), (7, 2, (1, 0, 2)), (5, 1, (2, 2, 2)), (7, 2, (1, 1, 1)), (4, 1, (1, 1, 0))]
    for k, i, d in cases:
        s, c = run(k, i, d, trials=400, nmax=11, p=random.choice([0.3, 0.4]))
        print(f"k={k} leaves at p_{i+1}..p_{i+3} counts {d}: soundness on {s} connected instances, completeness on {c} planted copies")

    rng = random.Random(11)
    for k, pos in [(5, (1, 2, 3)), (7, (2, 3, 4)), (8, (3, 4, 5)), (6, (1, 3)), (7, (2, 4))]:
        assert zigzag_check(k, pos, rng, 3000) == 0, (k, pos)
        print(f"zig-zag walks, k={k}, leaves at positions {[q + 1 for q in pos]}: 3000 instances, all contain T")
    bad = zigzag_check(6, (1, 2, 3, 4), rng, 3000)
    assert bad > 0
    print(f"zig-zag walks, k=6, leaves at positions [2, 3, 4, 5]: {bad} of 3000 instances accepted without a copy of T")


def zigzag_instance(k, leaves, rng):
    """A random walk over the path colours 0..k-1 with steps +-1 (distinct vertices), each walk vertex of colour j
    joined to one leaf of every leaf colour of position j, the leaves drawn from a pool of two per colour so that
    walk vertices share them. G' is connected by construction."""
    walk, j = [0], 0
    while j < k - 1:
        j += rng.choice([-1, 1]) if j > 0 else 1
        walk.append(j)
    G, col = nx.Graph(), {}
    for idx, j in enumerate(walk):
        col[("w", idx)] = j
        if idx:
            G.add_edge(("w", idx - 1), ("w", idx))
        for c in leaves.get(j, []):
            u = ("l", c, rng.randrange(2))
            col[u] = c
            G.add_edge(("w", idx), u)
    G.add_nodes_from(col)
    return G, col


def zigzag_check(k, pos, rng, trials):
    """pos: the path positions carrying one leaf each. Returns the number of instances without a copy of T."""
    T = nx.path_graph(k)
    leaves = {}
    for j in pos:
        leaves[j] = [len(T)]
        T.add_edge(j, len(T))
    bad = 0
    for _ in range(trials):
        G, col = zigzag_instance(k, leaves, rng)
        assert nx.has_path(present(aux(G, col, k, leaves), G), "s", "t")
        bad += not contains(G, T)
    return bad


if __name__ == "__main__":
    main()
