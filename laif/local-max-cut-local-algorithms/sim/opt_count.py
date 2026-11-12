"""Depth-1 QAOA optimum for LocalMaxCut on the d-regular tree for many d (counting formula): warm start from the
best angles of the last d of the same parity, plus a coarse grid, then Nelder-Mead. Usage: opt_count.py d1 d2 step"""
import sys, json, numpy as np
from scipy.optimize import minimize
from qaoa_count import value
d1, d2, step = map(int, sys.argv[1:4]); prev = {0: (5.70, 1.29), 1: (0.60, 0.32)}
for d in range(d1, d2 + 1, step):
    f = lambda x: -value(d, x[0], x[1])
    grid = [(f((g, b)), g, b) for g in np.linspace(0, 2 * np.pi, 13)[:-1] for b in np.linspace(0, np.pi / 2, 7)[:-1]]
    starts = [prev[d % 2], prev[1 - d % 2]] + [(g, b) for _, g, b in sorted(grid)[:2]]
    best = (0, None)
    for s in starts:
        r = minimize(f, s, method="Nelder-Mead", options={"xatol": 1e-7, "fatol": 1e-11})
        if -r.fun > best[0]: best = (-r.fun, r.x)
    prev[d % 2] = tuple(best[1])
    print(json.dumps({"d": d, "value": best[0], "gamma": best[1][0] % (2 * np.pi), "beta": best[1][1] % (np.pi / 2)}), flush=True)
