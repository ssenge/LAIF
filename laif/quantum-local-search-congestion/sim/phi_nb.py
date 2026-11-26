"""Phi(z, v) = sum_k sqrt(q_k(z_k, v)) for unit-step staircases on random regular graphs.
q_k(u, v) <= sum_{t=1}^{T-k} Pr[walk from step k is at v at time t] (union bound over times).
Walks: non-backtracking (NB, state = directed edge) and simple random walk (SRW), T = n^{1/3}.
Reports max over v for sampled walks z. Random regular graphs have short cycles, so they lie outside
the class of Theorem 4; the script shows the size of Phi, not the girth condition."""
import sys, numpy as np, networkx as nx, scipy.sparse as sp

def graph(n, d, seed):
    G = nx.random_regular_graph(d, n, seed=seed)
    assert nx.is_connected(G)
    return G

def nb_ops(G, d):
    arcs = [(u, v) for u, v in G.edges()] + [(v, u) for u, v in G.edges()]
    idx = {a: i for i, a in enumerate(arcs)}
    rows, cols = [], []
    for (u, v), i in idx.items():
        for w in G[v]:
            if w != u: rows.append(i); cols.append(idx[(v, w)])
    P = sp.csr_matrix((np.full(len(rows), 1.0 / (d - 1)), (rows, cols)), shape=(len(arcs),) * 2)
    head = sp.csr_matrix((np.ones(len(arcs)), (range(len(arcs)), [v for _, v in arcs])), shape=(len(arcs), G.number_of_nodes()))
    return arcs, idx, P.T.tocsr(), head

def phi_nb(G, d, T, rng):
    arcs, idx, PT, head = nb_ops(G, d)
    n = G.number_of_nodes(); u0 = 0
    # draw a NB walk z_1..z_{T+1}
    z = [u0, int(rng.choice(list(G[u0])))]
    while len(z) < T + 1:
        z.append(int(rng.choice([w for w in G[z[-1]] if w != z[-2]])))
    phi = np.zeros(n)
    for k in range(1, T):                    # tail after step k leaves from arc (z_{k-1}, z_k)
        x = np.zeros(len(arcs)); x[idx[(z[k - 1], z[k])]] = 1.0; acc = np.zeros(n)
        for t in range(T - k):
            x = PT @ x; acc += head.T @ x
        phi += np.sqrt(np.minimum(acc, 1.0))
    return phi.max(), T ** 1.5 / np.sqrt(n)

def phi_srw(G, T, rng):
    n = G.number_of_nodes(); A = nx.to_scipy_sparse_array(G, format="csr"); P = sp.csr_matrix(A.multiply(1.0 / A.sum(1).reshape(-1, 1))).T.tocsr()
    z = [0]
    while len(z) < T + 1: z.append(int(rng.choice(list(G[z[-1]]))))
    phi = np.zeros(n)
    for k in range(T):
        x = np.zeros(n); x[z[k]] = 1.0; acc = np.zeros(n)
        for t in range(T - k):
            x = P @ x; acc += x
        phi += np.sqrt(np.minimum(acc, 1.0))
    return phi.max()

if __name__ == "__main__":
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rng = np.random.default_rng(7)
    for n in (1000, 4000, 16000, 64000):
        G = graph(n, d, seed=n); T = round(n ** (1 / 3))
        nb = [phi_nb(G, d, T, rng) for _ in range(12)]
        sr = [phi_srw(G, T, rng) for _ in range(6)] if n <= 16000 else []
        m = [a for a, _ in nb]
        print(f"d={d} n={n:6d} T={T:3d}  NB max_v Phi: mean {np.mean(m):.2f} max {np.max(m):.2f}  floor T^1.5/sqrt(n)={nb[0][1]:.2f}"
              + (f"  SRW mean {np.mean(sr):.2f}" if sr else ""), flush=True)
