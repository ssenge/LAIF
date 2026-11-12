"""Optimize lam of the linear rule for each d (common random numbers), then evaluate on fresh samples with a
Hoeffding bound (the averaged quantity is a conditional probability in [0, 1]). Usage: classical_scan.py d..."""
import sys, json, numpy as np
from scipy.optimize import minimize_scalar
from classical_d import val
for d in map(int, sys.argv[1:]):
    n_train = 20000 if d > 60 else 50000
    r = minimize_scalar(lambda l: -val(d, l, n_train, np.random.default_rng(5))[0], bounds=(0.4, 1.6), method="bounded", options={"xatol": 1e-3})
    N = 200000; parts = [val(d, r.x, N // 4, np.random.default_rng(1000 + d * 10 + i))[0] for i in range(4)]
    f = float(np.mean(parts)); t = np.sqrt(np.log(2 / 1e-9) / (2 * N))
    print(json.dumps({"d": d, "lam": float(r.x), "N": N, "value": f, "hoeffding_lower": f - t}), flush=True)
