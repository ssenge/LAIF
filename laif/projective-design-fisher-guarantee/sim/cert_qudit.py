"""Rational certificates for eta_des(d,t), d >= 3, in the reduced variables (a, b, c).
Lower bound: q in span{a^i b^j (abc)^l : i+j+2l <= t} with
  h(a,s,c) = d s(1-a) c - q(a, s(1-a), c) >= 0 on [0,1]^3   (f >= q where a > 0, b = s(1-a))
  h0(s)    = -q(0, s, c) >= 0 on [0,1]                       (f = 0 where a = 0; q(0,b,c) does not depend on c)
gives eta >= E_Haar q. Upper bound: rational points with exact weights matching the invariant Haar moments."""
import sys, json, itertools
from fractions import Fraction as Fr
from math import comb, factorial
import numpy as np
from scipy.optimize import linprog
from cert4 import solve_exact

def basis(t): return [(i, j, l) for i in range(t + 1) for j in range(t + 1) for l in range(t // 2 + 1) if i + j + 2 * l <= t]
def haar(i, j, l, d):   # E[a^(i+l) b^(j+l)] E[c^l], Dirichlet(1,1,d-2), c = cos^2 of a uniform angle, exact
    p, q = i + l, j + l
    return Fr(factorial(d - 1) * factorial(p) * factorial(q), factorial(d - 1 + p + q)) * Fr(comb(2 * l, l), 4 ** l)

def mono(P, Bs):
    a, b, c = P.T
    return np.array([a ** i * b ** j * (a * b * c) ** l for i, j, l in Bs])

def dual_lp(d, t, M):
    Bs = basis(t)
    g = np.linspace(0, 1, M)
    A_, S_, C_ = np.meshgrid(g, g, g, indexing='ij'); A_ = A_.ravel(); S_ = S_.ravel(); C_ = C_.ravel()
    B_ = S_ * (1 - A_)
    P = np.c_[A_, B_, C_]
    f = np.where(A_ > 0, d * B_ * C_, 0.0)
    m = np.array([float(haar(i, j, l, d)) for i, j, l in Bs])
    res = linprog(-m, A_ub=mono(P, Bs).T, b_ub=f, bounds=(None, None), method="highs")
    return -res.fun, res.x

def h_poly(qc, Bs, d):
    """h(a,s,c) as dict {(p,r,k): coef} of a^p s^r c^k, exact."""
    h = {}
    def add(key, v): h[key] = h.get(key, Fr(0)) + v
    # d s (1 - a) c
    add((0, 1, 1), Fr(d)); add((1, 1, 1), Fr(-d))
    for (i, j, l), co in zip(Bs, qc):
        # - co a^i (s(1-a))^j (a s (1-a) c)^l = -co a^(i+l) s^(j+l) c^l (1-a)^(j+l)
        e = j + l
        for k in range(e + 1):
            add((i + l + k, j + l, l), -co * comb(e, k) * (-1) ** k)
    return {k: v for k, v in h.items() if v != 0}

def to_box(h, lo, hi):
    out = {}
    for key, c in h.items():
        parts = []
        for x, (l0, l1) in zip(key, zip(lo, hi)):
            parts.append([(p, comb(x, p) * l0 ** (x - p) * (l1 - l0) ** p) for p in range(x + 1)])
        for combo in itertools.product(*parts):
            k = tuple(p for p, _ in combo); v = c
            for _, w in combo: v *= w
            out[k] = out.get(k, Fr(0)) + v
    return out

def bern_min(cx, degs):
    best = None
    for I in itertools.product(*[range(n + 1) for n in degs]):
        b = Fr(0)
        for k, c in cx.items():
            if all(kk <= ii for kk, ii in zip(k, I)):
                w = c
                for kk, ii, n in zip(k, I, degs): w *= Fr(comb(ii, kk), comb(n, kk))
                b += w
        if best is None or b < best: best = b
    return best

def certify(h, dim, maxdepth=40):
    degs = [max(k[i] for k in h) for i in range(dim)]
    stack = [((Fr(0),) * dim, (Fr(1),) * dim, 0)]; boxes = 0
    while stack:
        lo, hi, dep = stack.pop(); boxes += 1
        if bern_min(to_box(h, lo, hi), degs) >= 0: continue
        v = sum(c * np.prod([float(x) ** e for x, e in zip(lo, k)]) for k, c in h.items())
        if v < 0 or dep >= maxdepth: return False, boxes, (lo, hi)
        ax = max(range(dim), key=lambda i: hi[i] - lo[i]); mid = (lo[ax] + hi[ax]) / 2
        hi1 = list(hi); hi1[ax] = mid; lo2 = list(lo); lo2[ax] = mid
        stack += [(lo, tuple(hi1), dep + 1), (tuple(lo2), hi, dep + 1)]
    return True, boxes, None
