"""Worst solution profile for d: a grid of the simplex, then a local search from the worst points. Each profile takes
the smaller of the label scheme and quantum search over the typed vectors. Usage: python worst.py d step full|wide"""
import math, os, sys
os.environ["OMP_NUM_THREADS"] = "1"
from multiprocessing import Pool
from itertools import product
import numpy as np
from scipy.optimize import minimize
from opt import Scheme, labels, wide_labels, profile, entropy

d, step, kind = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
S = Scheme(d, labels(d) if kind == "full" else wide_labels(d))

def grid():
    m = round(1/step)
    for t in product(range(m + 1), repeat=d):
        if sum(t) <= m:
            yield [(m - sum(t))*step] + [x*step for x in t]

def run(w, starts=3):
    pi = profile(d, w)
    grover = entropy(pi)/2
    v, q = S.solve(pi, starts=starts, seed=int(sum(x*1e4*(i + 1) for i, x in enumerate(w))))
    return min(v, grover, 2/7*entropy(pi)), w, v, q

def local(w0):
    def f(t):
        w = np.maximum(t, 0)
        w = w/w.sum()
        return -run(list(w), 2)[0]
    r = minimize(f, w0, method="Nelder-Mead", options=dict(maxiter=120, xatol=1e-3, fatol=1e-5))
    w = np.maximum(r.x, 0)
    return list(w/w.sum())

if __name__ == "__main__":
    pts = list(grid())
    with Pool(10) as p:
        res = p.map(run, pts, chunksize=4)
        res.sort(key=lambda r: -r[0])
        print(f"d={d} step={step} {kind} labels={len(S.labs)} points={len(pts)} baseline={2/7*math.log2(2*d+1):.5f}", flush=True)
        for r in res[:3]:
            print(f"  grid L={r[0]:.5f} w={[round(x, 4) for x in r[1]]}", flush=True)
        ws = p.map(local, [r[1] for r in res[:4]])
        fine = p.map(run, ws)
    fine.sort(key=lambda r: -r[0])
    L, w, v, q = fine[0]
    print(f"  worst L={L:.5f} w={[round(float(x), 4) for x in w]} gain={2/7*math.log2(2*d+1) - L:.5f}")
    print(f"  parts a,a0,ux,uy={[round(x, 4) for x in S.parts(q)[0]]} margin={S.support_margin(q, profile(d, w)):.3f} table exponent>={S.parts(q)[0][1]:.4f}")
    print("  used", [S.labs[i] for i in sorted(set(S.L[q > 1e-3]))], flush=True)
