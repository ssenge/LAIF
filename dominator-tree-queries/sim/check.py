"""Correctness and query counts for dom.py. Exits nonzero on any mismatch. Budget 32 for correctness, 16 for counts.

Each answer is compared with an independent computation: networkx dominators and brute-force removal for dominators,
and networkx strongly connected components with brute-force removal of each edge and vertex for bridges and points.
Limits: finite sizes and these families.
"""
import math
import sys
import numpy as np
import networkx as nx
from dom import *


def random_graph(n, p, r):
    A = r.random((n, n)) < p
    np.fill_diagonal(A, False)
    return A


def layered(n, seed):
    """Long chain of width-2 layers: a deep dominator tree with many strong bridges when closed into a cycle."""
    r = np.random.default_rng(seed)
    A = np.zeros((n, n), dtype=bool)
    for i in range(n - 1):
        A[i, i + 1] = True
        if i + 2 < n and r.random() < 0.5:
            A[i, i + 2] = True
    A[n - 1, 0] = True
    return A


def idom_nx(A, root):
    D = nx.from_numpy_array(A.astype(int), create_using=nx.DiGraph)
    return dict(nx.immediate_dominators(D, root))


def brute_strong(A):
    D = nx.from_numpy_array(A.astype(int), create_using=nx.DiGraph)
    base = nx.number_strongly_connected_components(D)
    B, P = set(), set()
    for e in list(D.edges):
        H = D.copy()
        H.remove_edge(*e)
        if nx.number_strongly_connected_components(H) > base:
            B.add((int(e[0]), int(e[1])))
    for v in list(D.nodes):
        H = D.copy()
        H.remove_node(v)
        if nx.number_strongly_connected_components(H) > base:
            P.add(int(v))
    return B, P


def brute_bridges(A, root):
    D = nx.from_numpy_array(A.astype(int), create_using=nx.DiGraph)
    seen = nx.descendants(D, root) | {root}
    out = set()
    for u, v in list(D.edges):
        if u in seen and v in seen and v != root:
            H = D.copy()
            H.remove_edge(u, v)
            if v not in nx.descendants(H, root):
                out.add((int(u), int(v)))
    return out


def checks():
    rng = np.random.default_rng(0)
    cnt = 0
    for n in (2, 3, 4, 5, 8, 12, 20):
        for s in range(40):
            r = np.random.default_rng(1000 * n + s)
            A = random_graph(n, r.choice([1.5 / n, 3.0 / n, 0.3]), r)
            for mode in ("matrix", "array"):
                got, _ = bridges(G(A, rng, mode, 32), 0, 1, np.ones(n, dtype=bool))
                assert set(got) == brute_bridges(A, 0), (n, s, mode)
                cnt += 1
    print("flow-graph bridges agreed with brute force on", cnt, "runs")
    cnt = 0
    for n in (2, 3, 4, 5, 8, 12, 20, 40, 80):
        for s in range(20):
            r = np.random.default_rng(100 * n + s)
            for A in (random_graph(n, min(1, 2.0 / n), r), random_graph(n, min(1, 4.0 / n), r), random_graph(n, 0.3, r), layered(n, s)):
                for mode in ("matrix", "array"):
                    g = G(A, rng, mode, 32)
                    idom, _ = dominators(g, 0)
                    want = idom_nx(A, 0)
                    got = {v: int(idom[v]) for v in range(n) if idom[v] != -1}
                    # networkx >= 3 omits the root's self-entry in some versions
                    want[0] = 0
                    assert got == {int(k): int(v) for k, v in want.items()}, (n, s, mode)
                    cnt += 1
                    if n <= 20:
                        B, P = strong(G(A, rng, mode, 32))
                        wb, wp = brute_strong(A)
                        assert B == wb and P == wp, (n, s, mode, B ^ wb, P ^ wp)
                        cnt += 1
    print("dominators and strong bridges and points agreed on", cnt, "runs")


def scaling(top):
    ns = [2 ** k for k in range(6, top + 1)]
    fams = {"dense": lambda n, r: random_graph(n, 0.5, r), "sparse": lambda n, r: random_graph(n, 8.0 / n, r), "cycle": lambda n, r: layered(n, int(r.integers(1 << 20)))}
    print("\ndominators, matrix model: oracle applications, budget 16, mean of 3, against n^2")
    print(f"{'family':8} " + " ".join(f"{n:>9}" for n in ns) + "  exponent")
    for name, f in fams.items():
        ys = []
        for n in ns:
            xs = []
            for s in range(3):
                r = np.random.default_rng(s)
                A = f(n, r)
                g = G(A, r, "matrix", 16)
                dominators(g, 0)
                xs.append(g.apps)
            ys.append(float(np.mean(xs)))
        print(f"{name:8} " + " ".join(f"{y:9.0f}" for y in ys) + f"  {np.polyfit(np.log(ns[-3:]), np.log(ys[-3:]), 1)[0]:.3f}", flush=True)
    print("         " + " ".join(f"{n * n:9d}" for n in ns) + "  (n^2)")
    print("\ndominators, array model, m edges: applications / sqrt(nm), budget 16, and classical reads m")
    print(f"{'family':8} " + " ".join(f"{n:>9}" for n in ns))
    for name, f in fams.items():
        out = []
        for n in ns:
            r = np.random.default_rng(1)
            A = f(n, r)
            g = G(A, r, "array", 16)
            dominators(g, 0)
            out.append(g.apps / math.sqrt(n * max(1, A.sum())))
        print(f"{name:8} " + " ".join(f"{y:9.2f}" for y in out), flush=True)


if __name__ == "__main__":
    checks()
    scaling(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
    print("ok")
