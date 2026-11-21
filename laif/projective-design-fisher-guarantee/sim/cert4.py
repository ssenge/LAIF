"""Exact rational certificates for eta_des(2,4).
Reduced form: a symmetric measure on S^2 is a measure on R = {(z,u): -1<=z<=1, 0<=u<=1-z^2} (u = x^2); the design
conditions are E[u^a z^c] = Haar for 2a + c <= 4 (y^2 = 1 - z^2 - u is eliminated), the objective is E[u/(1+z)].
Dual: E_Haar[q] is a lower bound whenever h(z,s) = s(1-z) - q(z, s(1-z^2)) >= 0 on [-1,1]x[0,1].
Primal: rational points of R with exact rational weights give an upper bound."""
from fractions import Fraction as Fr
import itertools, sys
from math import comb
import numpy as np, mpmath as mp
from scipy.optimize import linprog

B = [(a, c) for a in range(3) for c in range(5) if 2 * a + c <= 4]
def dfact(n): return 1 if n <= 0 else n * dfact(n - 2)
def haar(a, c):   # E[x^(2a) z^c] on S^2, exact
    if c % 2: return Fr(0)
    return Fr(dfact(2 * a - 1) * dfact(c - 1), dfact(2 * a + c + 1))

# ---------- dual -------------------------------------------------------------------------------------------
def poly_h(qc):
    """h(z,s) as dict {(i,j): coef} for z^i s^j, exact."""
    h = {(0, 1): Fr(1), (1, 1): Fr(-1)}
    for (a, c), co in zip(B, qc):
        # -co * z^c * s^a * (1 - z^2)^a
        for k in range(a + 1):
            term = Fr((-1) ** k * comb(a, k)) * (-co)
            key = (c + 2 * k, a)
            h[key] = h.get(key, Fr(0)) + term
    return {k: v for k, v in h.items() if v != 0}

def to_box(h, z0, z1, s0, s1):
    """coefficients of h(z0 + (z1-z0) X, s0 + (s1-s0) Y) in powers of X, Y."""
    out = {}
    dz, ds = z1 - z0, s1 - s0
    for (i, j), c in h.items():
        for p in range(i + 1):
            cz = c * comb(i, p) * z0 ** (i - p) * dz ** p
            for r in range(j + 1):
                key = (p, r)
                out[key] = out.get(key, Fr(0)) + comb(j, r) * Fr(cz) * s0 ** (j - r) * ds ** r
    return out

def bernstein_min(cx, n, m):
    """min Bernstein coefficient of polynomial with monomial coeffs cx[(p,r)] on [0,1]^2, degrees n, m."""
    best = None
    for I in range(n + 1):
        for J in range(m + 1):
            b = Fr(0)
            for (p, r), c in cx.items():
                if p <= I and r <= J:
                    b += c * Fr(comb(I, p), comb(n, p)) * Fr(comb(J, r), comb(m, r))
            best = b if best is None or b < best else best
    return best

def certify_nonneg(h, depth_max=60):
    n = max(i for i, _ in h); m = max(j for _, j in h)
    stack = [(Fr(-1), Fr(1), Fr(0), Fr(1), 0)]; boxes = 0
    while stack:
        z0, z1, s0, s1, dep = stack.pop(); boxes += 1
        cx = to_box(h, z0, z1, s0, s1)
        if bernstein_min(cx, n, m) >= 0: continue
        # check a corner value: if negative, certificate fails
        v = sum(c * z0 ** i * s0 ** j for (i, j), c in h.items())
        if v < 0 or dep >= depth_max: return False, boxes
        zm, sm = (z0 + z1) / 2, (s0 + s1) / 2
        if z1 - z0 >= 2 * (s1 - s0):
            stack += [(z0, zm, s0, s1, dep + 1), (zm, z1, s0, s1, dep + 1)]
        else:
            stack += [(z0, z1, s0, sm, dep + 1), (z0, z1, sm, s1, dep + 1)]
    return True, boxes

# ---------- primal ------------------------------------------------------------------------------------------
def primal(points):
    """points: list of exact (z,u) in R; LP in floats picks the support, exact weights solve the moment equations."""
    Z = np.array([float(z) for z, u in points]); U = np.array([float(u) for z, u in points])
    A = np.array([U ** a * Z ** c for a, c in B]); b = np.array([float(haar(a, c)) for a, c in B])
    f = U / (1 + Z)
    res = linprog(f, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    order = list(np.argsort(-res.x))
    sup = [i for i in order if res.x[i] > 1e-13]
    rhs = [haar(a, c) for a, c in B]
    for extra in range(len(points)):
        M = [[points[i][1] ** a * points[i][0] ** c for i in sup] for a, c in B]
        w = solve_exact(M, rhs)
        if w is not None: break
        sup.append(order[len(sup)])
    assert w is not None and all(x >= 0 for x in w), "weights not nonnegative"
    for (a, c), r in zip(B, rhs):
        assert sum(wi * points[i][1] ** a * points[i][0] ** c for wi, i in zip(w, sup)) == r
    val = sum(wi * points[i][1] / (1 + points[i][0]) for wi, i in zip(w, sup))
    return val, [(points[i], wi) for wi, i in zip(w, sup) if wi != 0]

def solve_exact(M, rhs):
    """exact solution of an overdetermined consistent system M w = rhs with independent columns, else None."""
    rows, cols = len(M), len(M[0]); A = [row[:] + [r] for row, r in zip(M, rhs)]
    r = 0; piv = []
    for col in range(cols):
        p = next((i for i in range(r, rows) if A[i][col] != 0), None)
        if p is None: return None
        A[r], A[p] = A[p], A[r]
        for i in range(rows):
            if i != r and A[i][col] != 0:
                fct = A[i][col] / A[r][col]
                A[i] = [x - fct * y for x, y in zip(A[i], A[r])]
        piv.append(r); r += 1
    if any(A[i][cols] != 0 for i in range(r, rows)): return None
    return [A[i][cols] / A[i][i] for i in range(cols)]
