"""Algorithm X on Max-Cut of random 3-regular graphs: the regularized warm start of arXiv:2603.10191 (Eq. (11), lam = 0.6,
best of M = 100 starts), spins with min(p_i, 1 - p_i) < tau fixed to the rounded warm start, and the residual graph on
the other spins solved exactly (variable elimination). No local search and no iterative refinement: one exact maximization
of the cut over the spins that warm-started QAOA can move. With tau = 0 and coordinate ascent this is the frozen-qubit
ceiling of frozen_ceiling.py.
Per graph: residual component sizes and diameters, elimination width, cut fractions of rounding, the radius-6 rule and X,
wall and CPU times of the warm start, of X and of the rule.
Warm starts: 'ca[:M]' (coordinate ascent to a fixed point, best of M, default 100) and 'adam:lr:steps:span[:M]' (rws_adam.adam, theta ~ U[0, span pi), best of M, default 100).
tau: one value or a comma-separated list, all applied to the same warm start.
seeds: S (seeds 0..S-1) or a:b (seeds a..b-1).
Usage: python -I c2_x.py N seeds warm tau[,tau..] out.jsonl"""
import os, sys, time, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, networkx as nx
from rws_local import graph, rws_ca, rounds, cut
from frozen_ceiling import ceiling, Eliminator
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from rws_adam import adam

def X(G, m, tau):
    """Fix spins with min(p, 1 - p) < tau (tau = 0: exactly polarized), solve the rest exactly, one connected component of
    the residual graph at a time (the components interact only through fixed spins, so the optimum splits).
    Returns cut, spins, largest elimination width, number of free spins, fixed mask, component vertex lists, rounding."""
    N = len(m); q = np.minimum((1 - m) / 2, (1 + m) / 2); fixed = q < tau if tau > 0 else np.abs(m) >= 1 - 1e-9
    s0 = np.where(m > 0, 1, -1).astype(np.int64); s = s0.copy()
    nb = np.array([sorted(G[v]) for v in range(N)], np.int64)
    E = np.array([(i, j) for i in range(N) for j in nb[i] if j > i]); ff = ~fixed[E[:, 0]] & ~fixed[E[:, 1]]
    A = csr_matrix((np.ones(ff.sum()), (E[ff, 0], E[ff, 1])), shape=(N, N))
    _, lab = connected_components(A, directed=False); F = np.where(~fixed)[0]
    order = F[np.argsort(lab[F], kind="stable")]; cuts = np.flatnonzero(np.diff(lab[order])) + 1
    comps = np.split(order, cuts) if len(F) else []; w = 0
    for C in comps:
        idx = {v: k for k, v in enumerate(C)}; h = np.zeros(len(C)); terms = []
        for v in C:
            for u in nb[v]:
                if not fixed[u]:
                    if u > v: terms.append(((idx[v], idx[u]) if idx[v] < idx[u] else (idx[u], idx[v]), 0.5))
                else: h[idx[v]] += 0.5 * s0[u]
        terms += [((k,), h[k]) for k in range(len(C)) if h[k] != 0]
        if not terms: continue
        El = Eliminator(len(C), terms); _, z = El.ground(); w = max(w, El.width); s[C] = z
    return cut(nb, s), s, w, len(F), fixed, comps, s0

def leak_bound(G, m, fixed, p=6, c=9.37):
    """Upper bound, in cut edges, on how far the expected cut of warm-started QAOA at depth p can exceed X when the fixed
    spins are polarized only up to delta_i = 2 arcsin sqrt(min(p_i, 1 - p_i)): c_p sum_{i fixed} D_i delta_i^2, D_i = number of
    edges whose radius-p light cone contains i (README; c_6 = 9.37 for the Table I schedule of [1]). 0 if all
    fixed spins are exactly polarized."""
    q = np.minimum((1 - m) / 2, (1 + m) / 2); tot = 0.0
    for i in np.where(fixed & (q > 0))[0]:
        B = nx.single_source_shortest_path_length(G, int(i), cutoff=p)
        D = sum(G.degree(v) for v in B) - G.subgraph(B).number_of_edges()     # edges with an endpoint in the ball
        tot += D * (2 * np.arcsin(np.sqrt(q[i]))) ** 2
    return c * tot

def diameter(G, C):
    """Exact diameter of the component for up to 3000 vertices, else the double-sweep lower bound."""
    H = G.subgraph(C)
    if len(C) <= 3000: return nx.diameter(H), True
    d = nx.single_source_shortest_path_length(H, C[0]); a = max(d, key=d.get)
    d = nx.single_source_shortest_path_length(H, a); return max(d.values()), False

def main(N, seeds, warm, taus, out):
    E = 1.5 * N
    with open(out, "a") as f:
        for sd in seeds:
            G, nb = graph(N, sd); t0 = time.perf_counter()
            if warm.startswith("ca"): m, _ = rws_ca(nb, 0.6, int(warm[3:]) if ":" in warm else 100, sd)
            else:
                a = warm.split(":"); M = int(a[4]) if len(a) > 4 else 100
                m = adam(nb, 0.6, M, float(a[1]), int(a[2]), float(a[3]) * np.pi, sd)
            tw = time.perf_counter() - t0
            for tau in taus:
              t0, p0 = time.perf_counter(), time.process_time()
              c, s, w, nf, fixed, comps, s0 = X(G, m, tau); tx, px = time.perf_counter() - t0, time.process_time() - p0
              assert cut(nb, s) == c and np.all(s[fixed] == s0[fixed]) and c >= cut(nb, s0)
              sizes = collections.Counter(len(k) for k in comps); big = max(comps, key=len) if comps else []
              diam, exact = diameter(G, list(big)) if len(big) else (0, True)
              lb = leak_bound(G, m, fixed)
              t0, p0 = time.perf_counter(), time.process_time(); _, h, _ = rounds(nb, s0, 3, sd)
              tr, pr = time.perf_counter() - t0, time.process_time() - p0
              rec = dict(N=N, seed=sd, warm=warm, tau=tau, fixed=float(fixed.mean()), free=nf, ncomp=len(comps),
                         max_comp=max(sizes, default=0), max_diam=diam, max_diam_exact=exact, sizes=dict(sorted(sizes.items())), width=w,
                         rounded=cut(nb, s0) / E, rule6=h[3] / E, X=c / E, X_minus_target=c / E - 0.9167, t_warm=tw, t_X=tx, cpu_X=px,
                         t_rule=tr, cpu_rule=pr, leak_bound=lb / E)
              f.write(json.dumps(rec) + "\n"); f.flush(); print(json.dumps({k: v for k, v in rec.items() if k != "sizes"}), flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "test":                          # X is the exact optimum over the free spins (brute force, n = 20)
        import itertools
        for sd in range(5):
            G, nb = graph(20, sd); m, _ = rws_ca(nb, 0.6, 10, sd)
            for tau in (0.0, 1e-2, 0.3):
                c, s, w, nf, fixed, comps, s0 = X(G, m, tau); F = np.where(~fixed)[0]; best = cut(nb, s0)
                for bits in itertools.product((1, -1), repeat=len(F)):
                    t = s0.copy(); t[F] = bits; best = max(best, cut(nb, t))
                assert c == best, (sd, tau, c, best)
        for sd in range(3):                            # componentwise X equals the global elimination at N = 2000
            G, nb = graph(2000, sd); m, _ = rws_ca(nb, 0.6, 10, sd); s0 = np.where(m > 0, 1, -1).astype(np.int64)
            assert X(G, m, 0.0)[0] == ceiling(G, m, s0)[0]
        print("c2_x self-checks passed"); sys.exit()
    main(int(sys.argv[1]), range(*map(int, sys.argv[2].split(":"))) if ":" in sys.argv[2] else range(int(sys.argv[2])), sys.argv[3], [float(t) for t in sys.argv[4].split(",")], sys.argv[5])
