"""Single-core time to reach the cut fraction 0.9167 (the depth-6 RWS-QAOA value at N = 10 000 of arXiv:2603.10191, held
fixed for larger N there) on random 3-regular graphs, by two classical routes:
  warm   RWS warm start by coordinate ascent (best of M starts) + 3 rounds of the radius-2 flip rule
  SA     simulated annealing from a random state, T from 1.5 to 0.05, the smallest sweep count of a doubling ladder that
         reaches the target (time of that run only)
Usage: python -I ttt.py seeds N1 N2 ..."""
import os, sys, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from rws_local import graph, rws_ca, cut, rounds
from rws_main import sa
TARGET = 0.9167
S = int(sys.argv[1])
for N in map(int, sys.argv[2:]):
    E = 1.5 * N
    for sd in range(S):
        G, nb = graph(N, sd); r = dict(N=N, seed=sd)
        for M in (1, 10, 100):
            t = time.perf_counter(); m, _ = rws_ca(nb, 0.6, M, sd); s0 = np.where(m > 0, 1, -1).astype(np.int64)
            _, h, _ = rounds(nb, s0, 3, sd); r[f"warm_M{M}"] = round(h[3] / E, 5); r[f"t_warm_M{M}"] = round(time.perf_counter() - t, 3)
        s_init = np.where(np.random.default_rng(sd).random(N) < 0.5, 1, -1).astype(np.int64); sw = 125
        while sw <= 64000:
            t = time.perf_counter(); b, _ = sa(nb, s_init, sw, 1.5, 0.05, sd); dt = time.perf_counter() - t
            if b / E >= TARGET: r.update(SA_sweeps=sw, SA=round(b / E, 5), t_SA=round(dt, 3)); break
            sw *= 2
        print(json.dumps(r), flush=True)
