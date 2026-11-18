"""Heavy-hex nearest-neighbour HUBO of arXiv:2506.20655 and arXiv:2510.26735 on the 156-qubit IBM Heron coupling map:
H(z) = sum_i h_i z_i + sum_<ij> J_ij z_i z_j + sum_<ijk> K_ijk z_i z_j z_k, z in {-1, +1}^156, with all one-body terms, all
176 edges and all 244 paths i-j-k of length two, coefficients drawn uniformly from the Sidon set {+-8/28, +-13/28, +-19/28, +-1}.
Exact methods by variable elimination along a min-degree order of the interaction graph:
  log_z(beta): ln Z exactly;  sample(beta, n): n independent exact Boltzmann samples;  ground(): a ground state."""
import itertools, numpy as np, networkx as nx

SIDON = np.array([8, 13, 19, 28]) / 28

def heron156():
    """8 rows of 16 qubits (0-15, 20-35, ...), joined by 4 bridge qubits per gap at columns 3, 7, 11, 15 and 1, 5, 9, 13
    alternately (Heron r2 numbering)."""
    G = nx.Graph(); rows = [list(range(20 * r, 20 * r + 16)) for r in range(8)]
    for r in rows: G.add_edges_from(zip(r, r[1:]))
    for g in range(7):
        cols = (3, 7, 11, 15) if g % 2 == 0 else (1, 5, 9, 13)
        for b, c in enumerate(cols): q = 20 * g + 16 + b; G.add_edge(rows[g][c], q); G.add_edge(q, rows[g + 1][c])
    G = nx.convert_node_labels_to_integers(G, ordering="sorted")
    assert G.number_of_nodes() == 156 and G.number_of_edges() == 176 and nx.is_connected(G)
    return G

def instance(seed, G=None):
    G = heron156() if G is None else G; rng = np.random.default_rng(seed)
    draw = lambda m: rng.choice(SIDON, m) * rng.choice([-1, 1], m)
    E2 = sorted(tuple(sorted(e)) for e in G.edges())
    E3 = sorted((min(a, b), j, max(a, b)) for j in G for a, b in itertools.combinations(sorted(G[j]), 2))
    terms = [((i,), c) for i, c in zip(sorted(G), draw(G.number_of_nodes()))]
    terms += [(e, c) for e, c in zip(E2, draw(len(E2)))] + [(t, c) for t, c in zip(E3, draw(len(E3)))]
    return G.number_of_nodes(), terms

def energy(terms, Z):
    """Energies of the rows of Z (entries +-1)."""
    Z = np.atleast_2d(Z); e = np.zeros(len(Z))
    for idx, c in terms: e += c * np.prod(Z[:, list(idx)], axis=1)
    return e

class Eliminator:
    def __init__(self, n, terms):
        self.n, self.terms = n, terms
        H = nx.Graph(); H.add_nodes_from(range(n))
        for idx, _ in terms: H.add_edges_from(itertools.combinations(idx, 2))
        order = []; Hc = H.copy()
        while Hc:
            v = min(Hc, key=lambda u: (Hc.degree(u), u)); nb = list(Hc[v])
            Hc.add_edges_from(itertools.combinations(nb, 2)); Hc.remove_node(v); order.append(v)
        self.order = order

    def _factors(self, beta):
        """Log-factors exp(-beta c prod z) over sorted variable tuples; axis value 0 means z = +1, 1 means z = -1."""
        F = []
        for idx, c in self.terms:
            k = len(idx); t = np.empty((2,) * k)
            for a in itertools.product((0, 1), repeat=k): t[a] = -beta * c * np.prod([1 - 2 * x for x in a])
            F.append((tuple(idx), t))
        return F

    def run(self, beta, mode="sum"):
        F = self._factors(beta); self.steps = []; width = 0; red = np.logaddexp.reduce if mode == "sum" else np.max
        for v in self.order:
            mine = [f for f in F if v in f[0]]; F = [f for f in F if v not in f[0]]
            U = tuple(sorted(set().union(*[set(f[0]) for f in mine]))); width = max(width, len(U))
            T = np.zeros((2,) * len(U))
            for vs, t in mine:
                T = T + t.reshape([2 if u in vs else 1 for u in U])
            ax = U.index(v); self.steps.append((v, U, T))
            F.append((U[:ax] + U[ax + 1:], red(T, axis=ax)))
        self.width = width
        return sum(float(t) for _, t in F)          # only scalar factors remain

    def log_z(self, beta): return self.run(beta, "sum")

    def sample(self, beta, m, rng):
        self.run(beta, "sum"); X = np.full((m, self.n), -1, np.int64)
        for v, U, T in reversed(self.steps):
            ax = U.index(v); others = [u for u in U if u != v]
            Tv = np.moveaxis(T, ax, -1)                                   # shape (2,)*len(others) + (2,)
            L = Tv[tuple(X[:, u] for u in others)] if others else np.broadcast_to(Tv, (m, 2))
            p1 = 1 / (1 + np.exp(L[:, 0] - L[:, 1]))                       # P(axis value 1)
            X[:, v] = (rng.random(m) < p1).astype(np.int64)
        return 1 - 2 * X                                                  # back to z = +-1

    def ground(self):
        e = self.run(1.0, "max"); x = np.full(self.n, -1, np.int64)       # beta = 1: maximise -H
        for v, U, T in reversed(self.steps):
            ax = U.index(v); others = [u for u in U if u != v]
            Tv = np.moveaxis(T, ax, -1); L = Tv[tuple(x[u] for u in others)] if others else Tv
            x[v] = int(np.argmax(L))
        return -e, 1 - 2 * x

if __name__ == "__main__":
    G = heron156(); n, terms = instance(0, G)
    print("terms by order:", {k: sum(len(i) == k for i, _ in terms) for k in (1, 2, 3)})
    El = Eliminator(n, terms); El.log_z(1.0); print("elimination width", El.width)
