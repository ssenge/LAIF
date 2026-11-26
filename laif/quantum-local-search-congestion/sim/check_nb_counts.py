"""Checks of input (0): NB walk counts A_t by brute force against the recurrence and the Chebyshev form,
and the entry bound (N1) on Ramanujan graphs (Petersen, Heawood, K_{4,4}, McGee-free small cages via networkx)."""
import itertools, numpy as np, networkx as nx
from numpy.polynomial import chebyshev as C

def brute(G, t):
    n = G.number_of_nodes(); M = np.zeros((n, n), int)
    def rec(path):
        if len(path) == t + 1: M[path[0], path[-1]] += 1; return
        for w in G[path[-1]]:
            if len(path) < 2 or w != path[-2]: rec(path + [w])
    for x in G: rec([x])
    return M

def U(k, X):  # Chebyshev 2nd kind via recurrence, matrix argument
    if k < 0: return np.zeros_like(X)
    a, b = np.eye(len(X)), 2 * X
    if k == 0: return a
    for _ in range(k - 1): a, b = b, 2 * X @ b - a
    return b

for name, G in [("Petersen", nx.petersen_graph()), ("Heawood", nx.heawood_graph()), ("K44", nx.complete_bipartite_graph(4, 4)),
                ("Tutte 8-cage", nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5))]:
    G = nx.convert_node_labels_to_integers(G); A = nx.to_numpy_array(G); n = len(A); d = int(A.sum(1)[0])
    ev = np.linalg.eigvalsh(A); nontriv = [m for m in ev if abs(abs(m) - d) > 1e-9]
    assert max(map(abs, nontriv)) <= 2 * np.sqrt(d - 1) + 1e-9, name           # Ramanujan
    At = [np.eye(n), A.copy(), A @ A - d * np.eye(n)]
    for t in range(3, 9): At.append(A @ At[-1] - (d - 1) * At[-2])
    X = A / (2 * np.sqrt(d - 1))
    for t in range(1, 7):
        assert np.array_equal(brute(G, t), At[t].round().astype(int)), (name, t)                  # recurrence
    for t in range(2, 9):
        cheb = (d - 1) ** (t / 2) * (U(t, X) - U(t - 2, X) / (d - 1))
        assert np.allclose(cheb, At[t]), (name, t)                                                # Chebyshev form
        bound = 2 * d * (d - 1) ** (t - 1) / n + 2 * (t + 1) * (d - 1) ** (t / 2)
        assert At[t].max() <= bound + 1e-9, (name, t, At[t].max(), bound)                         # (N1)
    print(f"{name:14s} n={n:3d} d={d} girth={nx.girth(G)}: recurrence, Chebyshev form, (N1) ok")
# mutation: (N1) without its spectral term must fail (bipartite K44)
G = nx.complete_bipartite_graph(4, 4); A = nx.to_numpy_array(G); At = [np.eye(8), A, A @ A - 4 * np.eye(8)]
for t in range(3, 9): At.append(A @ At[-1] - 3 * At[-2])
assert any(At[t].max() > 4 * 3 ** (t - 1) / 8 + 0.0 * t for t in range(2, 9)), "mutation survived"
print("mutation (spectral term dropped) caught; all asserts passed")
