"""Rounds of the odd-set cutting-plane method for maximum cardinality matching.

Each round solves max x(E) s.t. x(delta(v)) <= 1, x(E[S]) <= (|S|-1)/2 for S in F,
then adds violated odd sets. Output: rounds r and the largest |F| seen, per family.
Why it matters: if one LP costs ~O(n) edge reveals, the quantum query bound is
~O(n^{3/2} sqrt(r)), so r = o(sqrt n) would beat n^{7/4}. See ../NOTES.md.

ponytail: rebuilds every LP from scratch, n of a few thousand at most.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

EPS = 1e-7


def solve_lp(G, edges, F, c):
    idx = {e: i for i, e in enumerate(edges)}
    nodes = list(G.nodes)
    pos = {v: i for i, v in enumerate(nodes)}
    rows, cols = [], []
    for i, (u, v) in enumerate(edges):
        rows += [pos[u], pos[v]]
        cols += [i, i]
    b = [1.0] * len(nodes)
    r = len(nodes)
    for S in F:
        for i, (u, v) in enumerate(edges):
            if u in S and v in S:
                rows.append(r)
                cols.append(i)
        b.append((len(S) - 1) / 2)
        r += 1
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(r, len(edges)))
    res = linprog(-c, A_ub=A, b_ub=b, bounds=(0, None), method="highs-ds")
    assert res.status == 0, res.message
    return res.x, res.ineqlin.marginals[len(nodes):] if F else np.array([])


def support_components(G, edges, x):
    H = nx.Graph()
    for e, xe in zip(edges, x):
        if EPS < xe < 1 - EPS:
            H.add_edge(*e)
    return [set(c) for c in nx.connected_components(H)]


def set_value(S, edges, x):
    return sum(xe for (u, v), xe in zip(edges, x) if u in S and v in S)


def padberg_rao(G, edges, x):
    """Violated odd sets via a Gomory-Hu tree on the slack graph (cut value < 1)."""
    H = nx.Graph()
    H.add_nodes_from(G.nodes)
    z = "z"
    H.add_node(z)
    load = {v: 0.0 for v in G.nodes}
    for (u, v), xe in zip(edges, x):
        if xe > EPS:
            H.add_edge(u, v, capacity=xe)
            load[u] += xe
            load[v] += xe
    for v in G.nodes:
        H.add_edge(v, z, capacity=max(0.0, 1 - load[v]))
    T = nx.gomory_hu_tree(H)
    found = []
    for u, v, d in list(T.edges(data=True)):
        if d["weight"] >= 1 - 1e-6:
            continue
        T.remove_edge(u, v)
        side = nx.node_connected_component(T, u)
        T.add_edge(u, v, **d)
        S = set(side) if z not in side else set(H.nodes) - set(side)
        if len(S) % 2 == 1 and len(S) >= 3 and set_value(S, edges, x) > (len(S) - 1) / 2 + 1e-6:
            found.append(S)
    return found


def rounds(G, perturb=None, cap=100000):
    """Returns (rounds, max|F|, value). Perturbation is small enough to keep cardinality optimal."""
    edges = list(G.edges)
    if not edges:
        return 0, 0, 0
    n = G.number_of_nodes()
    c = np.ones(len(edges))
    if perturb is not None:
        c += perturb.random(len(edges)) / (4 * n * len(edges))
    F, best, last = [], 0, None
    for r in range(cap):
        x, duals = solve_lp(G, edges, F, c)
        value = float(np.ones(len(edges)) @ x)
        if np.all(np.minimum(np.abs(x), np.abs(x - 1)) < EPS):
            return r, best, round(value)
        # ponytail: drop slack cuts only after a strict objective drop, which keeps termination.
        if last is not None and c @ x < last - 1e-9 and F:
            F = [S for S, d in zip(F, duals) if abs(d) > EPS]
        last = c @ x
        new = [S for S in support_components(G, edges, x)
               if len(S) % 2 == 1 and set_value(S, edges, x) > (len(S) - 1) / 2 + 1e-6]
        if not new:
            new = padberg_rao(G, edges, x)
        assert new, "fractional vertex with no violated odd set"
        known = {frozenset(S) for S in F}
        fresh = [S for S in new if frozenset(S) not in known]
        assert fresh, "no fresh cut"
        F += fresh
        best = max(best, len(F))
    raise RuntimeError("round cap")


# --- instance families -------------------------------------------------------

def triangles_random(t, extra, rng):
    G = nx.disjoint_union_all([nx.cycle_graph(3) for _ in range(t)])
    for _ in range(int(extra * t)):
        G.add_edge(3 * rng.randrange(t) + rng.randrange(3), 3 * rng.randrange(t) + rng.randrange(3))
    G.remove_edges_from(nx.selfloop_edges(G))
    return G


def triangle_tree(depth):
    """Each vertex of a triangle hangs a child triangle: PM exists, LP sees only triangles."""
    G = nx.Graph()
    def build(d, next_id):
        a, b, c = next_id, next_id + 1, next_id + 2
        G.add_edges_from([(a, b), (b, c), (a, c)])
        nid = next_id + 3
        if d > 0:
            for v in (a, b, c):
                child = nid
                nid = build(d - 1, nid)
                G.add_edge(v, child)
        return nid
    build(depth, 0)
    return G


def nested_chain(k, base=0):
    """Nested blossoms of depth k: B_{i+1} is a 5-cycle through B_i."""
    G = nx.cycle_graph(3)
    G = nx.relabel_nodes(G, {i: base + i for i in range(3)})
    nid = base + 3
    tip = base
    for _ in range(k):
        u, v = nid, nid + 1
        nid += 2
        G.add_edges_from([(tip, u), (u, v), (v, tip + 1 if tip + 1 in G else tip)])
        tip = u
    return G, nid


def chains_hk(n, rng):
    """Chains of distinct depths 1,2,3..., the matching analogue of the Hopcroft-Karp bad case."""
    graphs, nid, k = [], 0, 1
    while nid < n:
        H, nid = nested_chain(k, nid)
        graphs.append(H)
        k += 1
    G = nx.compose_all(graphs)
    tips = [min(H.nodes) for H in graphs]
    for a, b in zip(tips, tips[1:]):
        G.add_edge(a, b)
    return G


def odd_cliques(t, s, extra, rng):
    G = nx.disjoint_union_all([nx.complete_graph(s) for _ in range(t)])
    for i in range(1, t):
        j = rng.randrange(i)
        G.add_edge(s * i + rng.randrange(s), s * j + rng.randrange(s))
    for _ in range(int(extra * t)):
        i, j = rng.randrange(t), rng.randrange(t)
        if i != j:
            G.add_edge(s * i + rng.randrange(s), s * j + rng.randrange(s))
    return G


def gallai_edmonds(a, s, rng):
    """A hub set of size a joined to a+s triangles: deficiency s, flat optimal dual."""
    G = nx.disjoint_union_all([nx.cycle_graph(3) for _ in range(a + s)])
    hub = list(range(3 * (a + s), 3 * (a + s) + a))
    for h in hub:
        for t in range(a + s):
            if rng.random() < 0.5:
                G.add_edge(h, 3 * t + rng.randrange(3))
    return G


def families(n, rng):
    t = max(2, n // 3)
    yield "G(n,2.5/n)", nx.gnp_random_graph(n, 2.5 / n, seed=rng.randrange(10**9))
    yield "G(n,5/n)", nx.gnp_random_graph(n, 5 / n, seed=rng.randrange(10**9))
    yield "cubic", nx.random_regular_graph(3, n + n % 2, seed=rng.randrange(10**9))
    yield "triangles+0.5", triangles_random(t, 0.5, rng)
    yield "triangles+1", triangles_random(t, 1.0, rng)
    yield "triangles+2", triangles_random(t, 2.0, rng)
    d = 0
    while 3 * (3 ** (d + 2) - 1) // 2 <= n:  # size of depth d is 3(3^{d+1}-1)/2
        d += 1
    yield "triangle_tree", triangle_tree(d)
    yield "chains_hk", chains_hk(n, rng)
    yield "odd_cliques5", odd_cliques(max(2, n // 5), 5, 0.5, rng)
    a = max(1, n // 8)
    yield "gallai_edmonds", gallai_edmonds(a, max(1, n // 16), rng)


def check():
    rng = random.Random(1)
    for name, G in families(40, rng):
        r, _, v = rounds(G, np.random.default_rng(1))
        assert v == len(nx.max_weight_matching(G, maxcardinality=True)), name
    print("self-check ok")


if __name__ == "__main__":
    check()
    if len(sys.argv) > 1 and sys.argv[1] == "check":
        sys.exit()
    sizes = [int(a) for a in sys.argv[1:]] or [30, 100, 300, 1000]
    print(f"{'family':16s}" + "".join(f"{'n=' + str(n):>18s}" for n in sizes) + "   (max r over 5 seeds, max |F|, plain/perturbed)")
    names = [name for name, _ in families(30, random.Random(0))]
    for name in names:
        print(f"{name:16s}", end="", flush=True)
        for n in sizes:
            rmax, fmax, nn = 0, 0, 0
            for seed in range(5):
                rng = random.Random(seed)
                G = dict(families(n, rng))[name]
                nn = G.number_of_nodes()
                for p in (None, np.random.default_rng(seed)):
                    r, f, v = rounds(G, p)
                    assert v == len(nx.max_weight_matching(G, maxcardinality=True)), (name, seed)
                    rmax, fmax = max(rmax, r), max(fmax, f)
            print(f"{rmax:>6d} |F|={fmax:<4d}n={nn:<5d}"[:18].rjust(18), end="", flush=True)
        print(flush=True)
