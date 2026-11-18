"""Exact 3-D hypervolume (maximization) by slicing; usage: hv3.py front.npy lower_bounds.json"""
import json, sys
import numpy as np

def area2(Q):                       # union area of boxes [0,a]x[0,b]
    Q = Q[np.argsort(-Q[:, 0])]; A = 0.0; ymax = 0.0
    for i in range(len(Q)):
        x_next = Q[i + 1, 0] if i + 1 < len(Q) else 0.0
        ymax = max(ymax, Q[i, 1]); A += (Q[i, 0] - x_next) * ymax
    return A

def hv3(P, r):
    Q = P - r; assert (Q >= -1e-12).all()
    Q = Q[np.argsort(-Q[:, 2])]; V = 0.0
    for i in range(len(Q)):
        z_next = Q[i + 1, 2] if i + 1 < len(Q) else 0.0
        V += area2(Q[: i + 1, :2]) * (Q[i, 2] - z_next)
    return V

if __name__ == "__main__":
    rng = np.random.default_rng(0); T = rng.random((40, 3))       # check against Monte Carlo
    S = rng.random((400000, 3)); mc = np.mean(np.any(np.all(S[:, None, :] <= T[None], axis=2), axis=1))
    assert abs(hv3(T, np.zeros(3)) - mc) < 5e-3, (hv3(T, np.zeros(3)), mc)
    P = np.load(sys.argv[1]); r = np.array(json.load(open(sys.argv[2])))
    print(f"points={len(P)} HV={hv3(P, r):.6f}")
