"""Multi-start search for the tree maximiser at given d, in the box beta in [-pi/4, pi/4), gamma in [-pi, pi)
(gamma_1 >= 0 by time reversal). Compares with the continuation value in scan.txt."""
import math, os, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import tree_cut

ref = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "scan.txt")):
    if not l.startswith("#"):
        p = l.split()
        ref[int(p[0])] = float(p[1])
rng = np.random.default_rng(11)
for d in [int(a) for a in sys.argv[1:]]:
    best = -1
    for _ in range(300):
        x0 = np.array([*rng.uniform(-math.pi / 4, math.pi / 4, 2), rng.uniform(0, math.pi), rng.uniform(-math.pi, math.pi)])
        r = minimize(lambda x: -tree_cut(x[:2], x[2:], d), x0, method="L-BFGS-B")
        best = max(best, -r.fun)
    print(f"{d} multistart {best:.12f} continuation {ref.get(d, float('nan')):.12f} diff {best - ref.get(d, float('nan')):+.2e}", flush=True)
