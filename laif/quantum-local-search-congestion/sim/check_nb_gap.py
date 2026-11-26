"""Theorem 5 input: on a d-regular graph whose eigenvalues other than ±d have |mu| <= lam < d, put
lam_* = max(sqrt(d-1), (lam + sqrt(max(lam^2 - 4(d-1), 0)))/2). Then for every t >= 1
  A_t(x, y) <= 2 d (d-1)^{t-1} / n + 2 (t+1) lam_*^t        (W1')
Brute-force check on non-Ramanujan regular graphs (random, circulants, prism, torus), with a mutation (lam_* replaced by sqrt(d-1)) that must fail."""
import numpy as np, networkx as nx

def At_list(A, d, tmax):
    n = len(A); L = [np.eye(n), A.copy(), A @ A - d * np.eye(n)]
    while len(L) <= tmax: L.append(A @ L[-1] - (d - 1) * L[-2])
    return L

def lam_star(A, d):
    ev = np.linalg.eigvalsh(A); lam = max([abs(m) for m in ev if abs(abs(m) - d) > 1e-8] or [0])
    return max(np.sqrt(d - 1), (lam + np.sqrt(max(lam * lam - 4 * (d - 1), 0))) / 2), lam

graphs = [("random 3-reg 200", nx.random_regular_graph(3, 200, seed=1)), ("random 4-reg 150", nx.random_regular_graph(4, 150, seed=2)),
          ("prism C30 x K2", nx.circular_ladder_graph(30)), ("torus 8x8", nx.grid_2d_graph(8, 8, periodic=True)),
          ("circulant Z_101 {1,7}", nx.circulant_graph(101, [1, 7]))]
caught = False
for name, G in graphs:
    G = nx.convert_node_labels_to_integers(G); A = nx.to_numpy_array(G); n = len(A); d = int(A.sum(1)[0])
    assert nx.is_connected(G) and (A.sum(1) == d).all()
    ls, lam = lam_star(A, d); L = At_list(A, d, 40)
    for t in range(1, 41):
        assert L[t].max() <= 2 * d * (d - 1) ** (t - 1) / n + 2 * (t + 1) * ls ** t + 1e-6 * L[t].max(), (name, t)
        if L[t].max() > 2 * d * (d - 1) ** (t - 1) / n + 2 * (t + 1) * np.sqrt(d - 1) ** t: caught = True
    print(f"{name:22s} n={n:4d} d={d} lam={lam:.3f} lam*={ls:.3f} theta={ls/(d-1):.3f}: (W1') ok for t <= 40")
assert caught, "mutation survived"
print("mutation (lam* -> sqrt(d-1)) caught on a non-Ramanujan graph; all asserts passed")
