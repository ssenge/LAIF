"""Check of the core lemma and the star model (classical simulation, sparsifier H = G).

Instances: dense clusters (G(a, p), p high) joined by few edges, plus pairs of adjacent "middle" vertices with more
neighbours in one cluster than in another, placed in the cluster where they have fewer neighbours. Clusters get a
certified conductance lower bound φ_C w.r.t. full degrees. With c_max the largest nontrivial pair value, the lemma gives
|X| <= b_C := floor(c_max / (φ_C δ)), and a non-terminal core vertex on the small side would have d_C(x) <= d_x/2 + b_C.
Shaving Z = {x in C : d_C(x) <= d_x/2 + b_C}. Asserts: (1) every nontrivial min u-v cut found meets each core in a set of
the form allowed by the lemma; (2) the star model has the same value λ(u, v) as G for every pair. Mutation: no shaving,
where the star model must fail on some instance."""
import itertools, random
import networkx as nx

def instance(rng, a=20, p=0.95, nclu=2, cross=3, nmid=2):
    G = nx.Graph(); clusters = []; nid = 0
    for c in range(nclu):
        vs = list(range(nid, nid + a)); nid += a; clusters.append(vs)
        G.add_nodes_from(vs)
        G.add_edges_from((x, y) for x, y in itertools.combinations(vs, 2) if rng.random() < p)
    for c in range(nclu - 1):
        for _ in range(cross):
            G.add_edge(rng.choice(clusters[c]), rng.choice(clusters[c + 1]))
    home = [list(c) for c in clusters]          # cluster assignment used by the algorithm
    for c in range(nclu - 1):
        mids = list(range(nid, nid + nmid)); nid += nmid
        for m in mids:
            for y in rng.sample(clusters[c], 9): G.add_edge(m, y)
            for y in rng.sample(clusters[c + 1], 6): G.add_edge(m, y)
            home[c + 1].append(m)                  # placed where it has fewer neighbours
        G.add_edges_from(itertools.combinations(mids, 2))
    return G, home

def phi_lower(G, C):
    """Lower bound on min_X e(X, C∖X) / min(vol X, vol C∖X), volumes = full degrees in G: by the easy direction of
    Cheeger's inequality for the pencil (L_C, D), with L_C the Laplacian of G[C] and D the full degrees,
    e(X, C∖X) vol(C) / (vol X vol C∖X) >= λ2, so the ratio is >= λ2 / 2."""
    import numpy as np
    idx = {x: i for i, x in enumerate(C)}; a = len(C)
    L = np.zeros((a, a)); Cs = set(C)
    for x in C:
        for y in G[x]:
            if y in Cs: L[idx[x], idx[y]] -= 1; L[idx[x], idx[x]] += 1
    d = np.array([G.degree(x) for x in C], float); Dm = np.diag(d ** -0.5)
    ev = np.linalg.eigvalsh(Dm @ L @ Dm)
    return max(ev[1] / 2 - 1e-9, 0.0)

def lam_all(G, weight="capacity"):
    T = nx.gomory_hu_tree(G, capacity=weight)
    def lam(u, v):
        path = nx.shortest_path(T, u, v)
        return min(T[x][y]["weight"] for x, y in zip(path, path[1:]))
    return lam

def star_model(G, cores):
    core_of = {x: i for i, C in enumerate(cores) for x in C}
    Gs = nx.Graph(); Gs.add_nodes_from(G)
    for x, y in G.edges():
        if core_of.get(x, -1) == core_of.get(y, -2): continue
        Gs.add_edge(x, y, capacity=1)
    for i, C in enumerate(cores):
        K = ("K", i); Cs = set(C)
        for x in C:
            w = sum(1 for y in G[x] if y in Cs)
            if w: Gs.add_edge(x, K, capacity=w)
    return Gs

def run(rng, shave=True, verbose=True):
    G, home = instance(rng)
    nx.set_edge_attributes(G, 1, "capacity")
    deg = dict(G.degree()); delta = min(deg.values())
    lam = lam_all(G)
    nontriv = [(u, v, lam(u, v)) for u, v in itertools.combinations(G, 2) if lam(u, v) < min(deg[u], deg[v])]
    cmax = max((c for _, _, c in nontriv), default=0)
    cores = []
    for C in home:
        Cs = set(C); phi = phi_lower(G, C); b = int(cmax / (phi * delta))
        Z = {x for x in C if sum(1 for y in G[x] if y in Cs) <= deg[x] / 2 + b} if shave else set()
        cores.append([x for x in C if x not in Z])
    # (1) lemma on the min cuts found
    for u, v, c in nontriv:
        cut, (S, T) = nx.minimum_cut(G, u, v, capacity="capacity")
        assert cut == c
        for C in cores:
            Cs = set(C)
            ok = (Cs & S) <= {u} or (Cs & T) <= {v}
            if shave: assert ok, (u, v, c)
    # (2) star model values
    Gs = star_model(G, cores); lam_s = lam_all(Gs)
    bad = sum(lam_s(u, v) != lam(u, v) for u, v in itertools.combinations(G, 2))
    if verbose:
        W = sum(1 for x, y in Gs.edges() if not isinstance(y, tuple) and not isinstance(x, tuple))
        print(f"n={G.number_of_nodes()} m={G.number_of_edges()} δ={delta} nontrivial pairs={len(nontriv)} "
              f"c_max={cmax} core sizes={[len(C) for C in cores]} edges outside cores={W} star mismatches={bad}")
    return bad, len(nontriv)

rng = random.Random(3)
tot = 0
for t in range(4):
    bad, nt = run(rng); assert bad == 0; tot += nt
assert tot > 0
fails = sum(run(rng, shave=False, verbose=False)[0] > 0 for t in range(4))
print(f"mutation without shaving: star model wrong on {fails} of 4 instances")
assert fails > 0
print("all asserts passed")
