"""Does the FO meta-algorithm with unpacking return minimum-cost arborescences? Reference: arb.py with its dual
check, and networkx. Also reports the iteration count against ceil(log2 n)."""
import math
import sys
import numpy as np
import networkx as nx

sys.dont_write_bytecode = True
import arb
import instances as I
import fo

INF = arb.INF


def nx_cost(W, root=0):
    G = nx.DiGraph()
    n = W.shape[0]
    for u in range(n):
        for v in range(n):
            if u != v and v != root and W[u, v] < INF:
                G.add_edge(u, v, weight=int(W[u, v]))
    A = nx.algorithms.tree.branchings.minimum_spanning_arborescence(G)
    return int(sum(d["weight"] for _, _, d in A.edges(data=True)))


def check(W, tag):
    n = W.shape[0]
    run, res = fo.solve(W)
    r2, res2 = arb.solve(W)
    if res2 is None:
        assert res is None, ("FO found a tree, arb none", tag)
        return run.iters
    assert res is not None, ("FO reports none", tag)
    parent, total = res
    for v in range(n):
        x, steps = v, 0
        while x != 0:
            x = int(parent[x])
            assert x >= 0, ("bad parent", tag)
            steps += 1
            assert steps <= n, ("cycle in output", tag)
    cost = sum(int(W[parent[v], v]) for v in range(1, n))
    assert all(W[parent[v], v] < INF for v in range(1, n)), ("nonedge", tag)
    assert cost == res2[1], ("not optimal", tag, cost, res2[1])
    assert total == cost, ("dual sum differs", tag, total, cost)
    return run.iters


def hard_random(n, rng):
    """Small weights, many ties and zero cycles, sparse or dense."""
    p = rng.choice([0.2, 0.4, 0.7, 1.0])
    top = int(rng.choice([2, 3, 5, 20, 1000]))
    W = rng.integers(0, top, (n, n), dtype=np.int64)
    W[rng.random((n, n)) > p] = INF
    W[0, 1:] = np.where(W[0, 1:] >= INF, top * n, W[0, 1:]) if rng.random() < 0.8 else W[0, 1:]
    np.fill_diagonal(W, INF)
    W[:, 0] = INF
    return W


def main():
    rng = np.random.default_rng(1)
    runs = 0
    worst = 0
    for trial in range(4000):
        n = int(rng.integers(2, 13))
        W = hard_random(n, rng)
        it = check(W, ("rand", trial))
        if n > 1:
            assert it <= math.ceil(math.log2(n)) + 1, ("iterations", it, n)
            worst = max(worst, it - math.ceil(math.log2(n)))
        runs += 1
    print("random small: runs", runs, "ok, max iterations - ceil(log2 n) =", worst)
    # networkx as a second reference
    k = 0
    for trial in range(300):
        n = int(rng.integers(3, 12))
        W = rng.integers(1, 30, (n, n), dtype=np.int64)
        np.fill_diagonal(W, INF)
        run, res = fo.solve(W)
        cost = sum(int(W[res[0][v], v]) for v in range(1, n))
        assert cost == nx_cost(W), "networkx disagrees"
        k += 1
    print("networkx: runs", k, "ok")
    for name, f in I.FAMILIES.items():
        for n in (8, 16, 33, 64, 128, 256):
            W = f(n)
            W[:, 0] = INF
            it = check(W, (name, n))
            print(f"{name:10s} n={n:4d} iterations={it} ceil(log2 n)={math.ceil(math.log2(n))}")
    for n in (8, 32, 128):
        W = I.hub(n)
        W[:, 0] = INF
        print("hub", n, check(W, ("hub", n)))
        W = I.random_sparse(n, 4)
        W[:, 0] = INF
        print("sparse", n, check(W, ("sparse", n)))


if __name__ == "__main__":
    main()
