"""Exact maximum independent sets of the portfolio-selection (PSP-MIS) market graphs of arXiv:2607.01037.

Graph: the assets of an OR-Library portfolio file (port1..port5: n, then n lines of mean and standard deviation of the
weekly returns, then lines "i j c_ij"), with an edge i-j when |c_ij| > lambda.
Kernel: repeated removal of exposed corner (simplicial) vertices, i.e. a vertex whose closed neighbourhood is a clique
is taken into the set and its neighbourhood is deleted. This keeps a maximum independent set.
Exact MIS: maximum clique of the complement of the kernel by branch and bound with a greedy-colouring bound, bitsets as
Python integers. No sampling and no quantum subroutine.
Usage: python -I psp_mis.py FILE LAMBDA   |   python -I psp_mis.py test"""
import sys, json, time, itertools
import numpy as np

def read_port(path):
    tok = open(path).read().split(); n = int(tok[0]); k = 1 + 2 * n; C = np.eye(n)
    while k + 2 < len(tok):
        i, j, c = int(tok[k]) - 1, int(tok[k + 1]) - 1, float(tok[k + 2]); C[i, j] = C[j, i] = c; k += 3
    return C

def graph(C, lam):
    n = len(C); adj = [0] * n
    for i in range(n):
        for j in range(n):
            if i != j and abs(C[i, j]) > lam: adj[i] |= 1 << j
    return adj

def reduce_corners(adj, alive):
    """Exposed corner removal until none is left: returns the kernel vertex mask and the vertices taken."""
    taken = []; changed = True
    while changed:
        changed = False
        for v in range(len(adj)):
            if not alive >> v & 1: continue
            N = adj[v] & alive; ok = True; m = N
            while m:
                u = (m & -m).bit_length() - 1; m &= m - 1
                if (N & ~(1 << u)) & ~adj[u]: ok = False; break
            if ok: taken.append(v); alive &= ~(N | 1 << v); changed = True
    return alive, taken

def max_clique(cadj, cand):
    """Maximum clique of the graph cadj restricted to the vertex mask cand (colouring bound, Tomita-style)."""
    best = [0, 0]                                             # size, mask
    def colour_order(P):
        order, bounds, col, U = [], [], 0, P
        while U:
            col += 1; Q = U
            while Q:
                v = (Q & -Q).bit_length() - 1; Q &= ~(1 << v) & ~cadj[v]; U &= ~(1 << v); order.append(v); bounds.append(col)
        return order, bounds
    def expand(R, size, P):
        order, bounds = colour_order(P)
        for k in range(len(order) - 1, -1, -1):
            if size + bounds[k] <= best[0]: return
            v = order[k]; NP = P & cadj[v]
            if NP: expand(R | 1 << v, size + 1, NP)
            elif size + 1 > best[0]: best[0], best[1] = size + 1, R | 1 << v
            P &= ~(1 << v)
    expand(0, 0, cand)
    return best[0], best[1]

def solve(C, lam):
    t0 = time.perf_counter(); adj = graph(C, lam); n = len(adj); full = (1 << n) - 1
    K, taken = reduce_corners(adj, full); t1 = time.perf_counter()
    cadj = [(~adj[v]) & K & ~(1 << v) for v in range(n)]
    sz, mask = max_clique(cadj, K); t2 = time.perf_counter()
    S = taken + [v for v in range(n) if mask >> v & 1]
    assert all(not (adj[a] >> b & 1) for a, b in itertools.combinations(S, 2))     # independent in the full graph
    kn = bin(K).count("1"); ke = sum(bin(adj[v] & K).count("1") for v in range(n) if K >> v & 1) // 2
    return dict(n=n, edges=sum(bin(a).count("1") for a in adj) // 2, lam=lam, kernel_nodes=kn,
                kernel_density=round(2 * ke / (kn * (kn - 1)), 4) if kn > 1 else 0.0, corners_taken=len(taken),
                mis=len(S), mis_set=sorted(S), t_reduce=t1 - t0, t_exact=t2 - t1, t_total=t2 - t0)

if __name__ == "__main__":
    if sys.argv[1] == "test":
        import networkx as nx
        rng = np.random.default_rng(1)
        for trial in range(60):                               # against networkx on random correlation-like matrices
            n = int(rng.integers(8, 40)); A = rng.normal(size=(n, 3 * n)); C = np.corrcoef(A); lam = float(rng.uniform(0.05, 0.3))
            r = solve(C, lam); G = nx.Graph(); G.add_nodes_from(range(n))
            G.add_edges_from((i, j) for i in range(n) for j in range(i + 1, n) if abs(C[i, j]) > lam)
            ref = max(len(c) for c in nx.find_cliques(nx.complement(G)))
            assert r["mis"] == ref, (trial, r["mis"], ref)
        print("psp_mis self-checks passed"); sys.exit()
    r = solve(read_port(sys.argv[1]), float(sys.argv[2])); r["file"] = sys.argv[1].split("/")[-1]; print(json.dumps(r))
