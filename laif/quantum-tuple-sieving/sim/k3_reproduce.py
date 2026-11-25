"""Reproduce the 3-tuple exponent 0.284551 of 2510.08473 (Theorem 3.1, eq. (4)) and optimize alpha, alpha'.
All quantities are log2(.)/d. p(a) = cap, W(a, b | t) = wedge (Lemmas 2.7, 2.8)."""
from math import log2, sqrt, acos, cos
from scipy.optimize import minimize

def p(ca):  # cap with cos = ca
    return 0.5 * log2(1 - ca * ca)

def W(ca, cb, ct):  # wedge: angle a around v, b around w, <v,w> = ct
    g2 = (ca * ca + cb * cb - 2 * ca * cb * ct) / (1 - ct * ct)
    return 0.5 * log2(1 - g2) if g2 < 1 else float("-inf")

m = 0.25 * log2(27 / 16)
ct, ctp = 1 / 3, 1 / sqrt(3)

def T(c, verbose=False):
    ca, cap_ = c
    pa, pap = p(ca), p(cap_)
    ell = pa - W(ca, ca, ct) + pap - W(cap_, cap_, ctp)
    tsol = m
    inner = max(0.5 * (2 * m + pa), 0.5 * (3 * m + W(ct, ca, ca) + pap))
    tot = max(ell + m, 0.5 * (ell + tsol) + inner)
    cond = min(m + pa, m + pap, m + W(ct, ca, ca), 2 * m + W(ctp, cap_, cap_))  # must be >= 0 (omega(d))
    if verbose:
        print(f"pa {pa:.6f} pa' {pap:.6f} W(t,a|a) {W(ct, ca, ca):.6f} mW(t',a'|a') {m + W(ctp, cap_, cap_):.6f} ell {ell:.6f}")
    return tot if cond >= -1e-9 else 9

paper = T((0.347606, 0.427124), True)
print(f"m = {m:.6f}, paper parameters: T = {paper:.6f}")
assert abs(paper - 0.284551) < 2e-6
best = min((minimize(T, x0, method="Nelder-Mead", options={"xatol": 1e-9, "fatol": 1e-10}) for x0 in [(0.3, 0.4), (0.35, 0.43), (0.4, 0.5)]), key=lambda r: r.fun)
print(f"optimized: cos a = {best.x[0]:.6f}, cos a' = {best.x[1]:.6f}, T = {best.fun:.6f}")
