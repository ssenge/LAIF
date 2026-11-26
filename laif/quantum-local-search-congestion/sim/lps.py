"""Bipartite graphs X^{p,q} of [9] ((p/q) = -1) as Cayley graphs on PGL(2, q), an instance class of Theorem 4.
Asserts order, regularity, connectivity, bipartiteness, the Ramanujan bound (the spectrum of a bipartite graph is symmetric,
so the second largest eigenvalue suffices) and the girth bound of [9]; then evaluates max_v Phi for sampled walks."""
import sys, itertools, numpy as np, networkx as nx, scipy.sparse.linalg as sla
import phi_nb
def lps(p, q):
    i = next(x for x in range(q) if (x * x + 1) % q == 0)
    gens = []
    r = int(p ** 0.5) + 1
    for a in itertools.product(range(-r, r + 1), repeat=4):
        if sum(x * x for x in a) == p and a[0] > 0 and a[0] % 2 == 1 and all(x % 2 == 0 for x in a[1:]):
            a0, a1, a2, a3 = a
            gens.append(((a0 + a1 * i) % q, (a2 + a3 * i) % q, (-a2 + a3 * i) % q, (a0 - a1 * i) % q))
    assert len(gens) == p + 1
    inv = {x: pow(x, q - 2, q) for x in range(1, q)}
    def norm(m):
        for x in m:
            if x: s = inv[x]; return tuple(y * s % q for y in m)
    def mul(m, n):
        a, b, c, d = m; e, f, g, h = n
        return norm(((a*e+b*g) % q, (a*f+b*h) % q, (c*e+d*g) % q, (c*f+d*h) % q))
    start = norm((1, 0, 0, 1)); seen = {start: 0}; order = [start]; edges = []
    for m in order:
        for gm in gens:
            w = mul(m, gm)
            if w not in seen: seen[w] = len(order); order.append(w)
            edges.append((seen[m], seen[w]))
    G = nx.Graph(); G.add_edges_from(edges); return G
if __name__ == "__main__":
    p, q = int(sys.argv[1]), int(sys.argv[2])
    G = lps(p, q); n = G.number_of_nodes(); d = p + 1
    assert n == q * (q * q - 1) and all(deg == d for _, deg in G.degree()) and nx.is_connected(G) and nx.is_bipartite(G)
    A = nx.to_scipy_sparse_array(G, format="csr", dtype=float)
    ev = sla.eigsh(A, k=4, which="LA", return_eigenvectors=False)
    lam2 = sorted(ev)[-2]
    g = nx.girth(G); lb = 4 * np.log(q) / np.log(p) - np.log(4) / np.log(p)
    print(f"X^{p},{q}: n={n} d={d} bipartite, lambda2={lam2:.4f} <= 2sqrt(p)={2*p**0.5:.4f}: {lam2 <= 2*p**0.5+1e-9}; girth={g} (LPS bound {lb:.2f}); (2/3)log_p n={2/3*np.log(n)/np.log(p):.2f}")
    assert lam2 <= 2 * p ** 0.5 + 1e-9 and g >= lb - 1e-9 and g >= (2 / 3 + 1 / 2) * np.log(n) / np.log(p)  # hypothesis of Theorem 4 with eps = 1/2
    G = nx.convert_node_labels_to_integers(G); T = round(n ** (1 / 3)); rng = np.random.default_rng(3)
    m = [phi_nb.phi_nb(G, d, T, rng)[0] for _ in range(int(sys.argv[3]) if len(sys.argv) > 3 else 6)]
    print(f"T={T}: NB max_v Phi over sampled walks: mean {np.mean(m):.3f} max {np.max(m):.3f}")
