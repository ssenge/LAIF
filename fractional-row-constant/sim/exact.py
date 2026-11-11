"""Exact max over f: Q_n -> [-1,1] of degree <= d of the minimal row cost at x = 1.
Dual: max over vertices y of the packing polytope {y >= 0, sum_{S contains i} y_S <= 1} and signs of an LP in f."""
import itertools, sys
import numpy as np
from fractions import Fraction
from scipy.optimize import linprog

def vertices(n):
    blocks = [S for k in range(1, n + 1) for S in itertools.combinations(range(n), k)]
    A = np.array([[1.0 if i in S else 0.0 for S in blocks] for i in range(n)])
    V = set()
    for k in range(1, n + 1):
        for R in itertools.combinations(range(n), k):
            for B in itertools.combinations(range(len(blocks)), k):
                M = A[np.ix_(R, B)]
                if abs(np.linalg.det(M)) < 1e-9: continue
                yb = np.linalg.solve(M, np.ones(k))
                if yb.min() < -1e-9: continue
                y = np.zeros(len(blocks)); y[list(B)] = yb
                if (A @ y).max() > 1 + 1e-9: continue
                V.add(tuple(np.round(y, 9)))
    return blocks, [np.array(v) for v in V]

def run(n, d):
    blocks, V = vertices(n)
    pts = np.array(list(itertools.product([1, -1], repeat=n)))
    mons = [T for k in range(d + 1) for T in itertools.combinations(range(n), k)]
    chi = lambda z, T: np.prod(z[..., list(T)], axis=-1) if T else np.ones(z.shape[:-1])
    A = np.array([chi(pts, T) for T in mons]).T                       # f(z) = A c
    one = np.ones(n)
    # Delta_S f = f(1) - f(1^S) = sum_T c_T (1 - (-1)^{|S cap T|})
    D = np.array([[1 - (-1) ** len(set(S) & set(T)) for T in mons] for S in blocks], float)
    best = (0, None)
    for y in V:
        sup = np.nonzero(y > 1e-12)[0]
        for sg in itertools.product([1, -1], repeat=len(sup) - 1):
            sg = (1,) + sg
            obj = sum(s * y[j] * D[j] for s, j in zip(sg, sup))
            r = linprog(-obj, A_ub=np.vstack([A, -A]), b_ub=np.ones(2 * len(pts)), bounds=[(None, None)] * len(mons), method="highs")
            if -r.fun > best[0] + 1e-9: best = (-r.fun, (y[sup], [blocks[j] for j in sup], sg))
    return best, len(V)

if __name__ == "__main__":
    for n in range(int(sys.argv[2]) if len(sys.argv) > 2 else 2, int(sys.argv[1]) + 1):
        for d in range(1, n + 1):
            (val, arg), nv = run(n, d)
            print(f"n={n} d={d}: max min-row cost {val:.6f} = {val / d**2:.4f} d^2 ({nv} vertices); argmax y={np.round(arg[0],4)} blocks={arg[1]}", flush=True)
