"""p = 2 at tree-optimal angles on small d-regular bipartite graphs rich in 4-cycles (plain statevector)."""
import math, os, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import statevector_cut, tree_cut

rng = np.random.default_rng(2)


def tree_opt(d):
    best = None
    for _ in range(30):
        x0 = np.array([*rng.uniform(-math.pi / 4, math.pi / 4, 2), *rng.uniform(-3, 3, 2)])
        r = minimize(lambda x: -tree_cut(x[:2], x[2:] / math.sqrt(d), d), x0, method="BFGS", options={"gtol": 1e-12})
        if best is None or r.fun < best.fun:
            best = r
    return best.x[:2], best.x[2:] / math.sqrt(d), -best.fun


def hypercube(n):
    return 2 ** n, [(v, v ^ (1 << i)) for v in range(2 ** n) for i in range(n) if v < v ^ (1 << i)]


def crown(m):  # K_{m,m} minus a perfect matching, (m - 1)-regular
    return 2 * m, [(i, m + j) for i in range(m) for j in range(m) if i != j]


cases = [("Q_3", 3, hypercube(3)), ("Q_4", 4, hypercube(4))] + [(f"K_{m},{m} minus matching", m - 1, crown(m)) for m in range(4, 9)]
for name, d, (n, E) in cases:
    assert all(sum(v in e for e in E) == d for v in range(n))
    b, g, t = tree_opt(d)
    c = statevector_cut(b, g, n, E)
    print(f"{name:24s} d={d} tree*={t:.10f} graph={c:.10f} diff={c - t:+.3e}", flush=True)
