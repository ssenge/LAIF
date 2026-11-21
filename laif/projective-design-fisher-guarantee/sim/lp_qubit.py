"""LP for the design Fisher guarantee on qubits: minimise int n_x^2/(1+n_z) dmu over measures on S^2 whose moments
up to degree t match the uniform measure. Calibration: t=2 -> 1/(3+sqrt3), t=3 -> 1/3 (2611.17288, Thm 1)."""
import sys, numpy as np
from scipy.optimize import linprog
from itertools import product

def grid(N):
    # Fibonacci sphere plus poles
    i = np.arange(N) + 0.5
    z = 1 - 2 * i / N; r = np.sqrt(1 - z * z); ph = np.pi * (1 + 5 ** 0.5) * i
    P = np.c_[r * np.cos(ph), r * np.sin(ph), z]
    return np.vstack([P, [[0, 0, 1], [0, 0, -1]]])

def haar_moment(a, b, c):
    # E[x^a y^b z^c] on S^2
    if a % 2 or b % 2 or c % 2: return 0.0
    from math import gamma
    return 2 * gamma((a + 1) / 2) * gamma((b + 1) / 2) * gamma((c + 1) / 2) / gamma((a + b + c + 3) / 2) / (4 * np.pi)

def solve(t, N):
    P = grid(N); x, y, z = P.T
    f = np.where(z > -1 + 1e-12, x * x / np.maximum(1 + z, 1e-300), 0.0)   # at the south pole f -> 0 along the meridian limit; use 0
    rows, rhs = [], []
    for a, b, c in product(range(t + 1), repeat=3):
        if a + b + c <= t:
            rows.append(x ** a * y ** b * z ** c); rhs.append(haar_moment(a, b, c))
    res = linprog(f, A_eq=np.array(rows), b_eq=np.array(rhs), bounds=(0, None), method="highs")
    return res.fun, P[res.x > 1e-9], res.x[res.x > 1e-9]

if __name__ == "__main__":
    N = int(sys.argv[1])
    for t in map(int, sys.argv[2:]):
        v, pts, w = solve(t, N)
        print(f"t={t}: LP value {v:.6f}, support {len(w)} points")
        ref = {2: 1 / (3 + 3 ** 0.5), 3: 1 / 3, 5: 5 / 12}
        if t in ref: assert abs(v - ref[t]) < 2e-3, (t, v)
    print("ref t=2", 1 / (3 + 3 ** 0.5), " t=3", 1 / 3, " t=4 bounds", 0.5 * (1 - 2 / 8 + 3 / (8 * 4 * 16)), 0.5 * (1 - 2 / 9))
