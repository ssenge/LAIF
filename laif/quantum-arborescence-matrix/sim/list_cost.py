"""The algorithm of Theorem 1 with in-adjacency lists (Theorem 2): a batch of b rows from a group C
costs sqrt(D_C b) log, D_C the number of arcs into C. Random sparse digraphs with a spanning
in-tree from the root planted, of average in-degree d; asserts the weight against networkx and
prints cost / (sqrt(n m) L^2)."""
import math, random
import networkx as nx
from lsm_cost import run

def sparse(n, d, rng, chain=False):
    W = [[math.inf] * n for _ in range(n)]
    for v in range(1, n):                      # planted arborescence keeps the instance feasible
        u = v - 1 if chain else rng.randrange(v)
        W[u][v] = 1.0 + 1e-3 * rng.random() if chain else rng.random()
    p = d / n
    for u in range(n):
        for v in range(1, n):
            if u != v and W[u][v] == math.inf and rng.random() < p:
                W[u][v] = (2.0 + u / n + 1e-3 * rng.random()) if (chain and u > v) else rng.random() + (3.0 if chain else 0.0)
    return W

def opt(W):
    n = len(W)
    D = nx.DiGraph([(u, v, {"weight": W[u][v]}) for u in range(n) for v in range(1, n) if u != v and W[u][v] < math.inf])
    return sum(e["weight"] for _, _, e in nx.minimum_spanning_arborescence(D).edges(data=True))

if __name__ == "__main__":
    rng = random.Random(23)
    for chain in (False, True):
        for d in (4, 16, 64):
            for n in (65, 129, 257):
                if d >= n: continue
                W = sparse(n, d, rng, chain)
                m = sum(1 for u in range(n) for v in range(n) if u != v and W[u][v] < math.inf)
                tot, cost = run(W, check=n <= 65, model="list")
                assert abs(tot - opt(W)) < 1e-9 * max(1, tot), (chain, d, n)
                L = math.log2(n) + 1
                print(f"{'chain ' if chain else 'random'} d={d:3d} n={n:4d} m={m:6d} cost/(sqrt(nm) L^2)={cost / (math.sqrt(n * m) * L * L):6.3f}", flush=True)
    from contraction_cost import chain_family
    for d in (8, 32):                          # the dense chain family of the matrix model, thinned to in-degree about d
        for n in (65, 129, 257):
            W = chain_family(n, rng)
            for u in range(n):
                for v in range(n):
                    if u != v and abs(u - v) > 1 and rng.random() > d / n: W[u][v] = math.inf
            m = sum(1 for u in range(n) for v in range(n) if u != v and W[u][v] < math.inf)
            tot, cost = run(W, check=n <= 65, model="list")
            assert abs(tot - opt(W)) < 1e-9 * max(1, tot), ("thinned chain", d, n)
            L = math.log2(n) + 1; st = run.last
            print(f"thinned chain d={d:3d} n={n:4d} m={m:6d} cost/(sqrt(nm) L^2)={cost / (math.sqrt(n * m) * L * L):6.3f} groups/vertex={st['maxmemb']}", flush=True)
    print("all invariants hold")
