"""Global optimum of depth-1 QAOA for LocalMaxCut on the d-regular tree: grid over gamma in [0, 2pi) and
beta in [0, pi/2) (the objective is invariant under the global flip, so beta has period pi/2), then Nelder-Mead
from the 6 best grid points."""
import sys, json, numpy as np
from scipy.optimize import minimize
from qaoa_tree import value
d = int(sys.argv[1]); G, B = 72, 36
grid = [(value(d, g, b), g, b) for g in np.arange(G) * 2 * np.pi / G for b in np.arange(B) * np.pi / 2 / B]
best = (0, 0, 0)
for v0, g0, b0 in sorted(grid)[-6:]:
    r = minimize(lambda p: -value(d, *p), [g0, b0], method="Nelder-Mead", options={"xatol": 1e-10, "fatol": 1e-13})
    if -r.fun > best[0]: best = (-r.fun, *r.x)
assert best[0] >= max(grid)[0] - 1e-12
print(json.dumps({"d": d, "value": best[0], "gamma": best[1] % (2 * np.pi), "beta": best[2] % (np.pi / 2), "grid_max": max(grid)[0]}), flush=True)
