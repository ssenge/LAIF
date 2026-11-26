"""Check of the contraction step by brute force on small graphs.
G is a random simple graph, H a reweighting of G whose cut error eps is computed exactly over all cuts.
F is a maximum s-t flow in H and H' = H - |F|. The parts are the classes of the relation
lambda_{H'}(u, v) >= k with k = 3 eps n, read off a Gomory-Hu tree of H'. Asserted:
(1) no minimum s-t cut of G splits a class, so contracting the classes keeps lambda_st;
(2) the classes have total H'-boundary at most 2 k (t - 1).
"""
import itertools, random
import networkx as nx

def cut(w, X, n):
    return sum(w.get((min(u, v), max(u, v)), 0) for u in X for v in range(n) if v not in X)

def classes(Hp, n, k):
    g = nx.Graph(); g.add_nodes_from(range(n))
    for (u, v), c in Hp.items():
        if c > 1e-12: g.add_edge(u, v, capacity=c)
    T = nx.gomory_hu_tree(g, capacity="capacity")
    T2 = nx.Graph(); T2.add_nodes_from(range(n))
    T2.add_edges_from((u, v) for u, v, d in T.edges(data=True) if d["weight"] >= k - 1e-9)
    return [set(c) for c in nx.connected_components(T2)]

random.seed(7)
tested = nontrivial = 0
for trial in range(4000):
    n = random.randint(5, 10)
    p = random.uniform(0.5, 1.0)
    E = [(u, v) for u, v in itertools.combinations(range(n), 2) if random.random() < p]
    if not E: continue
    G = {e: 1.0 for e in E}
    H = {e: random.uniform(0.85, 1.15) for e in E}
    eps = 0.0
    for r in range(1, n):
        for X in itertools.combinations(range(n), r):
            if 0 not in X: continue
            X = set(X); g = cut(G, X, n)
            if g > 0: eps = max(eps, abs(cut(H, X, n) / g - 1))
            elif cut(H, X, n) > 0: eps = 1
    if eps >= 1 / 3: continue
    s, t = 0, n - 1
    gh = nx.Graph(); gh.add_nodes_from(range(n))
    for (u, v), c in H.items(): gh.add_edge(u, v, capacity=c)
    fH, flow = nx.maximum_flow(gh, s, t, capacity="capacity")
    Hp = {(u, v): c - max(flow[u][v], flow[v][u]) for (u, v), c in H.items()}
    assert min(Hp.values()) > -1e-9
    k = 3 * eps * n
    P = classes(Hp, n, k)
    # (2) boundary bound
    bsum = sum(cut(Hp, A, n) for A in P)
    assert bsum <= 2 * k * (len(P) - 1) + 1e-9, (bsum, k, len(P))
    # (1) every minimum s-t cut of G keeps every class on one side, and the contracted value is lambda_st
    lam = min(cut(G, set(X), n) for r in range(1, n) for X in itertools.combinations(range(n), r) if s in X and t not in X)
    for r in range(1, n):
        for X in itertools.combinations(range(n), r):
            X = set(X)
            if s in X and t not in X and cut(G, X, n) == lam:
                assert all(A <= X or not (A & X) for A in P)
    a = next(i for i, A in enumerate(P) if s in A); b = next(i for i, A in enumerate(P) if t in A)
    assert a != b
    lam2 = min(cut(G, set().union(*[P[i] for i in S]), n)
               for r in range(1, len(P)) for S in itertools.combinations(range(len(P)), r) if a in S and b not in S)
    assert abs(lam2 - lam) < 1e-9
    tested += 1
    nontrivial += any(len(A) > 1 for A in P) and len(P) > 2
print(f"{tested} instances passed, {nontrivial} with a nontrivial contraction")
assert tested >= 200 and nontrivial >= 50
