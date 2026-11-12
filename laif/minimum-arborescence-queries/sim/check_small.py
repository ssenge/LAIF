"""Correctness tests. Run from this folder. Exits nonzero on any failure.

Limits: small sizes and hand-built or random families. Each answer is checked three ways: brute force
over all arborescences (n <= 6), networkx (n <= 60), and the dual certificate of Run.verify (all sizes).
"""
import itertools
import sys
import numpy as np
import networkx as nx
from arb import INF, solve
import instances as I


def brute(W):
    n = W.shape[0]
    best = None
    for p in itertools.product(*[[u for u in range(n) if u != v and W[u, v] < INF] for v in range(1, n)]):
        parent = (-1,) + p
        ok = True
        for v in range(1, n):
            x, k = v, 0
            while x != 0 and k <= n:
                x, k = parent[x], k + 1
            ok &= x == 0
        if ok:
            c = sum(int(W[parent[v], v]) for v in range(1, n))
            best = c if best is None else min(best, c)
    return best


def nx_cost(W):
    n = W.shape[0]
    G = nx.DiGraph()
    G.add_nodes_from(range(n))
    for u in range(n):
        for v in range(1, n):  # no edge enters the root, so 0 is the root of any spanning arborescence
            if u != v and W[u, v] < INF:
                G.add_edge(u, v, weight=int(W[u, v]))
    try:
        return int(nx.minimum_spanning_arborescence(G).size(weight="weight"))
    except nx.NetworkXException:
        return None


def check(W, want, tag, mode="exact", seed=0, budget=None):
    r, out = solve(W, mode=mode, seed=seed, budget=budget)
    if out is None:
        assert want is None, f"{tag}: reported none, expected {want}"
        return r
    parent, cost = out
    assert cost == want, f"{tag}: cost {cost}, expected {want}"
    r.verify(parent, cost)
    return r


def main():
    rng = np.random.default_rng(1)
    count = 0
    for n in (2, 3, 4, 5, 6):  # negative weights, which the proof allows
        for s in range(40):
            W = rng.integers(-9, 10, (n, n)).astype(np.int64)
            np.fill_diagonal(W, INF)
            check(W, brute(W), f"negative n={n} s={s}")
            count += 1
    for n in (2, 3, 4, 5, 6):
        for s in range(150 if n < 6 else 40):
            top = int(rng.choice([3, 10, 1000]))
            W = I.random_dense(n, int(rng.integers(1 << 30)), top)
            W[rng.random((n, n)) < rng.choice([0.0, 0.3, 0.6])] = INF
            np.fill_diagonal(W, INF)
            check(W, brute(W), f"brute n={n} s={s}")
            count += 1
    print("brute force agreed on", count, "instances")
    count = 0
    for n in (8, 16, 32, 60):
        cases = [(k, f(n)) for k, f in I.FAMILIES.items()]
        cases += [(f"sparse{s}", I.random_sparse(n, 3, s)) for s in range(3)] + [("hub", I.hub(n)), ("unreach", I.unreachable(n))]
        for tag, W in cases:
            check(W, nx_cost(W), f"{tag} n={n}")
            count += 1
    print("networkx and the dual certificate agreed on", count, "instances")
    count = 0
    for n in (8, 16, 32):
        for tag, f in I.FAMILIES.items():
            W = f(n)
            for s in range(3):
                check(W, nx_cost(W), f"bbht {tag} n={n}", mode="bbht", seed=s)  # run until no good element remains
                count += 1
    print("Grover-statistics back end agreed on", count, "runs")


if __name__ == "__main__":
    main()
    print("ok")
    sys.exit(0)
