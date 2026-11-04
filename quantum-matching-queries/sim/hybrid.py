"""Hybrid cost: LP rounds, then blossom phases on what remains.

cost(G) = min_r [ (r+1) + d_r ], d_r = nu(G) - nu(union of LP supports so far).
Each LP round and each phase costs ~O(n) edge reveals, so a worst-case cost c gives
~O(n^{3/2} sqrt(c)) queries; c = o(sqrt n) would beat n^{7/4}. Revealed edges are free
to reuse, which is why the rounded matching may use every support seen so far.

ponytail: d_r upper-bounds phases, since a phase also augments several paths at once.
"""
import random
import sys

import networkx as nx
import numpy as np

import rounds as R


def nu(G):
    return len(nx.max_weight_matching(G, maxcardinality=True))


def hybrid_cost(G, perturb=None, cap=2000):
    """Returns (cost, best r, d_0, LP value gap at r=0)."""
    edges = list(G.edges)
    if not edges:
        return 0, 0, 0, 0.0
    n, opt = G.number_of_nodes(), nu(G)
    c = np.ones(len(edges))
    if perturb is not None:
        c += perturb.random(len(edges)) / (4 * n * len(edges))
    H = nx.Graph()
    H.add_nodes_from(G.nodes)
    F, last, best, best_r, d0, gap0 = [], None, 10**9, 0, None, 0.0
    for r in range(cap):
        if r + 1 >= best:  # one more LP round cannot beat the incumbent
            break
        x, duals = R.solve_lp(G, edges, F, c)
        H.add_edges_from(e for e, xe in zip(edges, x) if xe > R.EPS)
        d = opt - nu(H)
        if r == 0:
            d0, gap0 = d, float(x.sum()) - opt
        if r + 1 + d < best:
            best, best_r = r + 1 + d, r
        if d == 0:
            break
        if last is not None and c @ x < last - 1e-9 and F:
            F = [S for S, dd in zip(F, duals) if abs(dd) > R.EPS]
        last = c @ x
        new = [S for S in R.support_components(G, edges, x)
               if len(S) % 2 == 1 and R.set_value(S, edges, x) > (len(S) - 1) / 2 + 1e-6]
        if not new:
            new = R.padberg_rao(G, edges, x)
        known = {frozenset(S) for S in F}
        fresh = [S for S in new if frozenset(S) not in known]
        if not fresh:
            break
        F += fresh
    return best, best_r, d0, gap0


def lp_rounds_only(G):
    return R.rounds(G, None, cap=2000)[0]


def worst_gadget(s, tries, seed=0):
    """Sparse graph on about s vertices maximizing plain LP rounds (the stalling behaviour)."""
    rng = random.Random(seed)
    best, bestG = -1, None
    for _ in range(tries):
        G = nx.gnp_random_graph(s, 2.5 / s, seed=rng.randrange(10**9))
        r = lp_rounds_only(G)
        if r > best:
            best, bestG = r, G
    return bestG, best


def copies(gadget, c, bridge, rng):
    G = nx.disjoint_union_all([gadget.copy() for _ in range(c)])
    s = gadget.number_of_nodes()
    for _ in range(int(bridge * c)):
        i, j = rng.randrange(c), rng.randrange(c)
        if i != j:
            G.add_edge(s * i + rng.randrange(s), s * j + rng.randrange(s))
    return G


if __name__ == "__main__":
    G = nx.cycle_graph(5)
    assert hybrid_cost(G)[0] >= 1
    # two triangles joined by an edge: LP may give 3 at once, and cost is at most 2
    T = nx.disjoint_union(nx.cycle_graph(3), nx.cycle_graph(3))
    T.add_edge(0, 3)
    assert hybrid_cost(T)[0] <= 2
    print("self-check ok")
    sizes = [int(a) for a in sys.argv[1:]] or [100, 200, 400, 800]
    print(f"{'family':16s}" + "".join(f"{'n=' + str(n):>16s}" for n in sizes) + "   worst cost (r, d0), 5 seeds; sqrt n for scale")
    for name in [nm for nm, _ in R.families(30, random.Random(0))]:
        print(f"{name:16s}", end="", flush=True)
        for n in sizes:
            w = (0, 0, 0)
            for seed in range(5):
                rng = random.Random(seed)
                G = dict(R.families(n, rng))[name]
                for p in (None, np.random.default_rng(seed)):
                    co, r, d0, _ = hybrid_cost(G, p)
                    w = max(w, (co, r, d0))
            print(f"{w[0]:>7d} ({w[1]},{w[2]})".rjust(16), end="", flush=True)
        print(flush=True)
    print("copies of a stalling gadget (s vertices, c copies, n = s*c):")
    for s, tries in ((30, 150), (50, 150), (80, 80)):
        g, r0 = worst_gadget(s, tries)
        for c in (5, 10, 20):
            rng = random.Random(c)
            for bridge in (0, 1.0):
                G = copies(g, c, bridge, rng)
                co, r, d0, _ = hybrid_cost(G)
                print(f"  s={s:3d} gadget_r={r0:3d} c={c:3d} bridge={bridge:3.1f} n={G.number_of_nodes():5d} "
                      f"cost={co:4d} r={r:4d} d0={d0:4d} sqrt(n)={G.number_of_nodes()**.5:5.1f}", flush=True)
