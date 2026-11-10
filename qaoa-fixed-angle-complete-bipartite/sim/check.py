"""Checks for the note on the fixed-angle conjecture on K_{d,d} (README.md), p = 2.

1. The exact evaluators (regular tree by a sum over histories, K_{d,d} by two collective spins) agree
   with a plain statevector on small cases.
2. Tree-optimal angles from scratch (multi-start, then second-order steps) at selected d, the K_{d,d} value at them,
   and the sign of the difference: d = 2..8 and the window edges 351, 352, 384, 385, 585, 586, 643, 644.
3. The value at d = 9 matches the threshold b of [1, Theorem 8].
4. The angles of the 1/d family give K_{d,d} above the tree optimum at selected d (Conjecture 1).
The full scan over 9 <= d <= 1060 is produced by refine.py (output in scan.txt).
"""
import math
import os
import sys

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import kdd_cut, statevector_cut, tree_cut, tree_graph
from refine import newton, tree

rng = np.random.default_rng(1)


def check_evaluators():
    for _ in range(3):
        beta, gamma = rng.uniform(-1, 1, 2), rng.uniform(-1, 1, 2)
        n, E = tree_graph(3, 2)
        assert abs(tree_cut(beta, gamma, 3) - statevector_cut(beta, gamma, n, E, (0, 1))) < 1e-10
        for d in (2, 3, 4, 5):
            Ek = [(i, d + j) for i in range(d) for j in range(d)]
            assert abs(kdd_cut(beta, gamma, d) - statevector_cut(beta, gamma, 2 * d, Ek)) < 1e-10
    print("1. tree (d = 3) and K_{d,d} (d <= 5) agree with the statevector")


def tree_optimum(d, starts=40):
    best = None
    known = np.array([0.4963, 0.2691, 0.7639, 1.3323])  # near the large-d optimum, gamma = g / sqrt(d)
    for i in range(starts):
        x0 = known if i == 0 else np.array([*rng.uniform(-math.pi / 4, math.pi / 4, 2), *rng.uniform(-3, 3, 2)])
        r = minimize(lambda x: -tree(x, d), x0, method="BFGS")
        if best is None or r.fun < best.fun:
            best = r
    x, g = newton(best.x, d)
    return x, tree(x, d), g


def check_edges():
    print("2. d, tree optimum, K_{d,d} at the tree-optimal angles, difference:")
    expect = {d: +1 for d in range(2, 9)}
    expect.update({9: -1, 22: -1, 351: -1, 352: +1, 384: +1, 385: -1, 585: -1, 586: +1, 643: +1, 644: -1})
    for d, sign in expect.items():
        x, t, g = tree_optimum(d, 40 if d < 100 else 12)
        k = kdd_cut(x[:2], x[2:] / math.sqrt(d), d)
        assert np.sign(k - t) == sign and g < 1e-6, (d, k - t)
        if d == 9:
            assert t >= 0.6391275408952286 - 1e-12
        print(f"   d={d:4d}: {t:.10f}  {k:.10f}  {k - t:+.3e}")


def check_conjecture1():
    print("4. K_{d,d} at beta = (-0.360743, -0.564711), gamma = (-3.2955, -3.0938)/d against the tree optimum:")
    for d in (9, 30, 100, 300, 1000):
        x, t, _ = tree_optimum(d, 1 if d > 30 else 20)
        k = kdd_cut([-0.360743, -0.564711], [-3.2955 / d, -3.0938 / d], d)
        assert k > t
        print(f"   d={d:4d}: K {k:.6f} > tree optimum {t:.6f}")


if __name__ == "__main__":
    check_evaluators()
    check_edges()
    print("3. d = 9 tree optimum is at least b of [1, Theorem 8]: ok")
    check_conjecture1()
    print("all checks passed")
