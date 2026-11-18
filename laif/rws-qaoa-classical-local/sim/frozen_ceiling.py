"""Ceiling for warm-started QAOA on Max-Cut: a qubit with p_i in {0, 1} is an eigenstate of its warm-start mixer and of the
cost, so it is never changed, and the expected cut at any depth is at most the maximum cut with those spins fixed.
Computes that maximum exactly by variable elimination (hubo.py of dcqs-exact) on the free spins.
Usage: python -I frozen_ceiling.py N seeds M (M warm-start starts)"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
for d in ("../../heavy-hex-hubo-exact-sampling/sim", "../../dcqs-exact/sim"):     # the eliminator hubo.py
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), d))
import numpy as np
from rws_local import graph, rws_ca, cut
from hubo import Eliminator, energy

def ceiling(G, m, s0):
    free = np.abs(m) < 1 - 1e-9; F = np.where(free)[0]; idx = {v: k for k, v in enumerate(F)}
    base = 0; h = np.zeros(len(F)); terms = []
    for i, j in G.edges():
        if free[i] and free[j]: terms.append(((min(idx[i], idx[j]), max(idx[i], idx[j])), 0.5))
        elif free[i] or free[j]:
            v, f = (i, j) if free[i] else (j, i); h[idx[v]] += 0.5 * s0[f]
        else: base += s0[i] != s0[j]
    terms += [((k,), h[k]) for k in range(len(F)) if h[k] != 0]
    n_terms_edges = sum(len(t) == 2 for t, _ in terms) + sum(1 for i, j in G.edges() if free[i] != free[j])
    El = Eliminator(len(F), terms); e0, z = El.ground()          # minimum of sum z_i z_j / 2 + sum h_i z_i
    s = s0.copy(); s[F] = z
    best = base + n_terms_edges / 2 - e0                          # cut = sum (1 - z z')/2 over edges touching free spins
    return int(round(best)), s, El.width, len(F)

if __name__ == "__main__":
    N, seeds, M = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for sd in range(seeds):
        G, nb = graph(N, sd); E = 1.5 * N; m, _ = rws_ca(nb, 0.6, M, sd); s0 = np.where(m > 0, 1, -1).astype(np.int64)
        t = time.perf_counter(); c, s, w, nf = ceiling(G, m, s0)
        assert cut(nb, s) == c and np.all(s[np.abs(m) >= 1 - 1e-9] == s0[np.abs(m) >= 1 - 1e-9])
        print(f"N={N} seed={sd}: free {nf}, width {w}, rounded {cut(nb, s0) / E:.4f}, frozen-spin ceiling {c / E:.4f} ({time.perf_counter() - t:.1f} s)", flush=True)
