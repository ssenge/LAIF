"""Best p = 2 cut fraction of K_{d,d} over all angles (multi-start), for Conjecture 1."""
import math, os, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import kdd_cut

rng = np.random.default_rng(5)
for d in [int(a) for a in sys.argv[1:]]:
    best = (-1, None)
    for _ in range(40):
        x0 = np.array([*rng.uniform(-math.pi / 4, math.pi / 4, 2), *rng.uniform(-math.pi, math.pi, 2)])
        r = minimize(lambda x: -kdd_cut(x[:2], x[2:], d), x0, method="L-BFGS-B")
        if -r.fun > best[0]:
            best = (-r.fun, r.x)
    print(d, f"{best[0]:.10f}", np.round(best[1], 6).tolist(), "d*gamma", np.round(best[1][2:] * d, 4).tolist(), flush=True)
