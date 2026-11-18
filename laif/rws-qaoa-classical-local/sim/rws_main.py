"""Max-Cut on random 3-regular graphs (networkx random_regular_graph, seeds 0..S-1): classical rules on the regularized warm
start (RWS) of arXiv:2603.10191, against the expected cut fraction of depth-6 RWS-QAOA reported there (0.9167 at N = 10 000).
Warm start: Eq. (11) with lambda = 0.6, maximized to a fixed point by coordinate ascent, best F of 100 random starts.
Columns (cut fractions):
  product      expected cut of the warm-start product state itself (sampling each spin independently)
  rounded      sign of the warm start (radius 0)
  r2, r4, r6   1, 2, 3 rounds of the parallel improving-flip rule of rws_local.py (radius 2, 4, 6)
  ceiling      maximum cut with the polarised spins (p_i in {0, 1}) fixed, exact by elimination; it bounds the expected
               cut of warm-started QAOA at every depth, since those qubits are never changed
  SA           simulated annealing from a uniformly random state, 20 000 sweeps, T from 1.5 to 0.05 (unrestricted, no warm start)
Usage: python -I rws_main.py N seeds"""
import os, sys, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from numba import njit
from rws_local import graph, rws_ca, cut, rounds
from frozen_ceiling import ceiling

@njit(cache=True)
def sa(nb, s, sweeps, T0, T1, seed):
    np.random.seed(seed); s = s.copy(); N = nb.shape[0]; c = cut(nb, s); best = c; bs = s.copy()
    for t in range(sweeps):
        T = T0 * (T1 / T0) ** (t / max(1, sweeps - 1))
        for _ in range(N):
            i = np.random.randint(N); g = 0
            for k in range(3): g += 1 if s[nb[i, k]] == s[i] else -1
            if g >= 0 or np.random.random() < np.exp(g / T):
                s[i] = -s[i]; c += g
                if c > best: best = c; bs[:] = s
    return best, bs

if __name__ == "__main__":
    N, S = int(sys.argv[1]), int(sys.argv[2]); E = 1.5 * N
    for sd in range(S):
        G, nb = graph(N, sd); t = time.perf_counter(); m, f = rws_ca(nb, 0.6, 100, sd); tw = time.perf_counter() - t
        s0 = np.where(m > 0, 1, -1).astype(np.int64); _, h, _ = rounds(nb, s0, 3, sd)
        t = time.perf_counter(); c, s1, w, nf = ceiling(G, m, s0); tc = time.perf_counter() - t
        assert cut(nb, s1) == c and c >= h[0]
        t = time.perf_counter(); b, bs = sa(nb, np.where(np.random.default_rng(sd).random(N) < 0.5, 1, -1).astype(np.int64), 20000, 1.5, 0.05, sd); ts = time.perf_counter() - t; assert cut(nb, bs) == b
        prod = sum((1 - m[i] * m[j]) / 2 for i, j in G.edges()) / E
        r = dict(N=N, seed=sd, F=f / E, polarised=1 - nf / N, product=prod, rounded=h[0] / E, r2=h[1] / E, r4=h[2] / E, r6=h[3] / E,
                 ceiling=c / E, width=w, SA=b / E, t_warm=tw, t_ceiling=tc, t_SA=ts)
        print(json.dumps({k: (round(v, 5) if isinstance(v, float) else v) for k, v in r.items()}), flush=True)
