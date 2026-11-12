"""Depth-1 QAOA optimum for LocalMaxCut at large d (counting formula), Nelder-Mead from the best angles of the
nearest computed d of each parity. Usage: opt_warm.py d..."""
import sys, json, numpy as np
from scipy.optimize import minimize
from qaoa_count import value
prev = {r["d"]: (r["gamma"], r["beta"]) for r in map(json.loads, open("qaoa_d.jsonl"))}
for d in map(int, sys.argv[1:]):
    near = lambda par: prev[min((e for e in prev if e % 2 == par), key=lambda e: abs(e - d))]
    best = (0, None)
    for s in (near(d % 2), near(1 - d % 2)):
        r = minimize(lambda x: -value(d, x[0], x[1]), s, method="Nelder-Mead", options={"xatol": 1e-6, "fatol": 1e-10})
        if -r.fun > best[0]: best = (-r.fun, r.x)
    prev[d] = (best[1][0] % (2 * np.pi), best[1][1] % (np.pi / 2))
    print(json.dumps({"d": d, "value": best[0], "gamma": prev[d][0], "beta": prev[d][1]}), flush=True)
