"""The worst exponent over the profiles with a given weight w_0 of the value 0, against the empty scheme and typed search.
Writes curves_d.dat with columns w_0, best scheme, empty scheme. Usage: python curves.py d step"""
import math, os, sys
os.environ["OMP_NUM_THREADS"] = "1"
from itertools import product
from multiprocessing import Pool
from opt import Scheme, wide_labels, profile, entropy

d = int(sys.argv[1])
step = float(sys.argv[2])
S = Scheme(d, wide_labels(d))


def point(w):
    pi = profile(d, w)
    h = entropy(pi)
    empty = min(2/7, 1/2)*h
    v, q = S.solve(pi, starts=2, seed=int(sum(w)*1e6) % 2**31)
    return (w[0], min(v, h/2, empty) if q is not None else min(h/2, empty), min(h/2, empty))


if __name__ == "__main__":
    m = round(1/step)
    pts = [[i/m for i in t] + [(m - sum(t))/m] for t in product(range(m), repeat=d) if sum(t) < m and all(t[k] > 0 for k in range(1, d))]
    with Pool(11) as p:
        res = p.map(point, pts, chunksize=4)
    best = {}
    for w0, v, e in res:
        b = best.setdefault(w0, [0.0, 0.0])
        b[0], b[1] = max(b[0], v), max(b[1], e)
    with open(f"curves_{d}.dat", "w") as f:
        for w0 in sorted(best):
            f.write(f"{w0:.4f} {best[w0][0]:.5f} {best[w0][1]:.5f}\n")
