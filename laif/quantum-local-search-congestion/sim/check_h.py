"""Hypothesis H of Theorem 6 on random d-regular graphs: the union of the radius-s balls around a uniform
non-backtracking walk of length T = n^{1/3} induces a forest. Prints the fraction of walks where it fails (expected to drop
with n, annealed bound N^2/(nd) with N = (T+1) d (d-1)^{s+1}). Mutation: on a graph of girth 4 (torus) H must fail."""
import sys, numpy as np, networkx as nx

def walk(G, T, rng):
    z = [0, int(rng.choice(list(G[0])))]
    while len(z) < T + 1: z.append(int(rng.choice([w for w in G[z[-1]] if w != z[-2]])))
    return z

def H(G, z, s):
    U = set()
    for x in set(z): U |= set(nx.single_source_shortest_path_length(G, x, cutoff=s))
    S = G.subgraph(U)
    return nx.is_forest(S)

rng = np.random.default_rng(11); s = 2
for d in (3, 4):
    for n in (1000, 8000, 64000, 256000):
        G = nx.random_regular_graph(d, n, seed=n + d); T = round(n ** (1 / 3))
        fails = sum(not H(G, walk(G, T, rng), s) for _ in range(200))
        N = (T + 1) * d * (d - 1) ** (s + 1)
        print(f"d={d} n={n:6d} T={T:2d} s={s}: H fails in {fails/200:.3f} of walks; annealed bound N^2/(nd) = {N*N/(n*d):.2f}", flush=True)
Tor = nx.convert_node_labels_to_integers(nx.grid_2d_graph(30, 30, periodic=True))
assert not any(H(Tor, walk(Tor, 10, rng), 2) for _ in range(20)), "mutation survived"
print("mutation (torus, girth 4) caught")
