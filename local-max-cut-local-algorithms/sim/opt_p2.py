"""Depth-p QAOA angle search for LocalMaxCut on the d-regular tree: coarse Nelder-Mead from random starts and from
the depth-1 optima, then a fine polish of the 3 best. Usage: opt_p2.py d p starts seed."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
from qaoa_p import value
d, p, S, seed = map(int, sys.argv[1:5]); rng = np.random.default_rng(seed)
f = lambda x: -value(d, x[:p], x[p:])
starts = [np.r_[rng.uniform(0, 2 * np.pi, p), rng.uniform(0, np.pi / 2, p)] for _ in range(S)]
for g1, b1 in [(5.6473, 1.2248), (0.6358, 0.3460)]:
    for eps in [0.0, 0.2, -0.2]:
        starts.append(np.r_[[g1] * p, [b1] * p] + eps * np.r_[np.linspace(-1, 1, p), np.linspace(1, -1, p)])
coarse = []; t = time.time()
for s in starts:
    r = minimize(f, s, method="Nelder-Mead", options={"xatol": 1e-3, "fatol": 1e-6, "maxiter": 300})
    coarse.append((-r.fun, r.x))
coarse.sort(key=lambda c: -c[0]); print("coarse top", [round(c[0], 6) for c in coarse[:5]], round(time.time() - t), flush=True)
best = (0, None)
for v0, x0 in coarse[:3]:
    r = minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-9, "fatol": 1e-12, "maxiter": 3000})
    if -r.fun > best[0]: best = (-r.fun, r.x)
print(json.dumps({"d": d, "p": p, "starts": len(starts), "value": best[0], "gamma": best[1][:p].tolist(), "beta": best[1][p:].tolist()}), flush=True)
