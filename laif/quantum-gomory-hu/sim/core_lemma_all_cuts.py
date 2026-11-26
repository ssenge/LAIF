"""Exhaustive check of Lemma 3 (with a general shaving margin) and of the star model on small graphs.
H = G with independent edge weights in [0.9, 1.1] (a valid (1±0.1) cut sparsifier for the inequalities used).
Clusters: planted, phi_C = exact H-conductance (full H-volumes). beta_C = max_c 1.1c/(0.9 phi_C delta).
Core = {x in C : d_C(x) >= d_x/2 + beta_C}  (the lemma's contrapositive). Checks EVERY min u-v cut of G."""
import itertools, random, sys
import numpy as np, networkx as nx

def all_cut_values(n, E):
    masks = np.arange(1 << n, dtype=np.int64)
    val = np.zeros(1 << n)
    for (a, b), w in E.items():
        val += w * (((masks >> a) & 1) != ((masks >> b) & 1))
    return masks, val

def check(rng, n, clusters, p_in, p_out, wiggle=True, zero=False):
    G = nx.Graph(); G.add_nodes_from(range(n))
    cl = {x: i for i, C in enumerate(clusters) for x in C}
    for x, y in itertools.combinations(range(n), 2):
        if rng.random() < (p_in if cl[x] == cl[y] else p_out): G.add_edge(x, y)
    if not nx.is_connected(G): return None
    deg = dict(G.degree()); delta = min(deg.values())
    EH = {e: (rng.uniform(0.9, 1.1) if wiggle else 1.0) for e in G.edges()}
    EG = {e: 1.0 for e in G.edges()}
    masks, valG = all_cut_values(n, EG)
    degH = {x: 0.0 for x in G}
    for (a, b), w in EH.items(): degH[a] += w; degH[b] += w
    # nontrivial pairs and all their min cuts
    side = [((masks >> u) & 1) for u in range(n)]
    nontriv = []
    for u, v in itertools.combinations(range(n), 2):
        sep = side[u] != side[v]
        c = valG[sep].min()
        if c < min(deg[u], deg[v]) - 1e-9:
            nontriv.append((u, v, c, masks[sep & (np.abs(valG - c) < 1e-9)]))
    if not nontriv: return None
    cmax = max(c for *_, c, _ in nontriv)
    cores = []
    for C in clusters:
        Cs = set(C); phi = float("inf")
        for r in range(1, len(C)):
            for X in itertools.combinations(C, r):
                Xs = set(X); e = sum(w for (a, b), w in EH.items() if (a in Xs) != (b in Xs) and a in Cs and b in Cs)
                vx = sum(degH[x] for x in X); vy = sum(degH[x] for x in Cs - Xs)
                phi = min(phi, e / min(vx, vy))
        beta = 0 if (zero or phi == float("inf")) else (1.1 * cmax / (0.9 * phi * delta) if phi > 0 else float("inf"))
        cores.append([x for x in C if sum(1 for y in G[x] if y in Cs) >= deg[x] / 2 + beta])
    # lemma on every min cut
    viol = 0
    for u, v, c, Ms in nontriv:
        for M in Ms:
            S = {x for x in range(n) if (M >> x) & 1}
            if u not in S: S = set(range(n)) - S
            T = set(range(n)) - S
            for K in cores:
                Ks = set(K)
                if not ((Ks & S) <= {u} or (Ks & T) <= {v}): viol += 1; None
    # star model
    core_of = {x: i for i, K in enumerate(cores) for x in K}
    Gs = nx.Graph(); Gs.add_nodes_from(G)
    for x, y in G.edges():
        if core_of.get(x, -1) != core_of.get(y, -2): Gs.add_edge(x, y, capacity=1)
    for i, K in enumerate(cores):
        Ks = set(K)
        for x in K:
            w = sum(1 for y in G[x] if y in Ks)
            Gs.add_edge(x, ("K", i), capacity=w)
    bad = 0
    for u, v in itertools.combinations(range(n), 2):
        sep = side[u] != side[v]; lg = valG[sep].min()
        ls, (A, B) = nx.minimum_cut(Gs, u, v, capacity="capacity")
        Sv = {x for x in A if not isinstance(x, tuple)}
        gval = sum(1 for x, y in G.edges() if (x in Sv) != (y in Sv))
        if abs(ls - lg) > 1e-9 or abs(gval - lg) > 1e-9: bad += 1; None
    return viol, bad, len(nontriv), [len(K) for K in cores], sum(len(Ms) for *_, Ms in nontriv)

def sweep(seed, trials, zero=False):
    rng = random.Random(seed); stats = [0, 0, 0, 0]
    for t in range(trials):
        n = rng.choice([10, 11, 12, 13, 14])
        k = rng.choice([2, 3]); perm = list(range(n)); rng.shuffle(perm)
        cuts = sorted(rng.sample(range(1, n), k - 1)); clusters = [perm[a:b] for a, b in zip([0] + cuts, cuts + [n])]
        r = check(rng, n, clusters, rng.uniform(0.7, 1.0), rng.uniform(0.02, 0.25), wiggle=rng.random() < 0.7, zero=zero)
        if r is None: continue
        stats[0] += 1; stats[1] += r[0]; stats[2] += r[1]; stats[3] += r[4]
    return stats

st = sweep(1, 400)
print(f"instances {st[0]}, minimum cuts checked {st[3]}, lemma violations {st[1]}, star mismatches {st[2]}")
assert st[0] > 0 and st[3] > 0 and st[1] == 0 and st[2] == 0
mu = sweep(1, 400, zero=True)
print(f"mutation with margin 0: lemma violations {mu[1]}, star mismatches {mu[2]}")
assert mu[1] > 0
print("all asserts passed")
