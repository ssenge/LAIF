"""Tree-optimal p = 2 angles to high accuracy (second-order steps on central differences) and K_{d,d} at them.
Usage: python refine.py d0 d1 > out   (continuation from the d = 9 optimum; columns as in scan.txt)"""
import math, os, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qaoa import kdd_cut, tree_cut


def tree(x, d):
    return tree_cut(x[:2], x[2:] / math.sqrt(d), d)


def newton(x, d, h=1e-4, steps=8):
    n = len(x)
    I = np.eye(n) * h
    for _ in range(steps):
        f0 = tree(x, d)
        fp = np.array([tree(x + I[i], d) for i in range(n)])
        fm = np.array([tree(x - I[i], d) for i in range(n)])
        g = (fp - fm) / (2 * h)
        H = np.empty((n, n))
        for i in range(n):
            H[i, i] = (fp[i] - 2 * f0 + fm[i]) / h ** 2
            for j in range(i):
                H[i, j] = H[j, i] = (tree(x + I[i] + I[j], d) - tree(x + I[i] - I[j], d)
                                     - tree(x - I[i] + I[j], d) + tree(x - I[i] - I[j], d)) / (4 * h * h)
        step = np.linalg.solve(H, g)
        x = x - step
        if np.max(np.abs(step)) < 1e-11:
            break
    assert np.all(np.linalg.eigvalsh(H) < 0)
    return x, np.max(np.abs(g))


if __name__ == "__main__":
    d0, d1 = int(sys.argv[1]), int(sys.argv[2])
    x = np.array([0.509672697, 0.273443820, 0.782504858, 1.386818237])  # d = 9
    for d in range(9, d1 + 1):
        if d < d0 - 3:
            x = minimize(lambda y: -tree(y, d), x, method="BFGS").x
            continue
        x, gn = newton(x, d)
        if d < d0:
            continue
        t = tree(x, d)
        k = kdd_cut(x[:2], x[2:] / math.sqrt(d), d)
        k1 = kdd_cut(np.array([-0.360743, -0.564711]), np.array([-3.2955, -3.0938]) / d, d)  # 1/d family, result 4
        print(f"{d} {t:.13f} {k:.13f} {k - t:+.6e} {k1:.13f} " + " ".join(f"{v:.12f}" for v in x), flush=True)
        print(f"{d} gradient {gn:.1e}", file=sys.stderr)
