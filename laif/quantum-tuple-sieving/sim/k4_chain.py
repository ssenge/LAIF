"""Quantum 4-tuple sieve: the nested two-oracle search with random product codes of 2510.08473, carried to a chain
x1, x2 (angle t1), x3 near s2 = x1 + x2 (angle t2 to s2/|s2|), x4 near s3 (angle t3). All exponents are log2(.)/d.
Per random-product-code repetition, with buckets of angles a1, a2, a3:
  |T0| = m^2 p(a1), |T1| = m^2 W(t1, a1 | a1), x3-candidates per pair m p(a2), good ones m W(t2, a2 | a2),
  x4-candidates per triple m p(a3).  A pair is completed by an inner two-oracle search over x3 with an x4 check.
  Cost per solution: sqrt(|T0| / S) + sqrt(|T1| / S) * inner, S = solutions in this repetition,
  inner = sqrt(m p(a2) / n) + sqrt(m W2 / n) * sqrt(m p(a3)), n = max(1, completions per pair in T1).
  Repetitions ell = prod_i p(a_i) / W(a_i, a_i | t_i); preprocessing ell * m.
Run: python k4_chain.py"""
from math import log2, sqrt, acos, cos
from scipy.optimize import minimize
import itertools

def p(c):
    return 0.5 * log2(1 - c * c)

def W(ca, cb, ct):
    g2 = (ca * ca + cb * cb - 2 * ca * cb * ct) / (1 - ct * ct)
    return 0.5 * log2(1 - g2) if g2 < 1 - 1e-12 else -50.0

def time_k(m, ts, cs):
    """General chain with len(ts) = k - 1 levels. ts: cosines of chain angles, cs: cosines of bucket angles."""
    k1 = len(ts)
    if any(c <= 0 or c >= 1 for c in cs):
        return 9
    for t, c in zip(ts, cs):              # wedges need theta <= 2 alpha
        if acos(t) > 2 * acos(c) - 1e-6:
            return 9
    P = [p(c) for c in cs]
    Wl = [W(t, c, c) for t, c in zip(ts, cs)]          # W(t, a | a)
    ell = sum(P[i] - W(cs[i], cs[i], ts[i]) for i in range(k1))
    tsol = m                                              # minimal memory: m solutions in total
    if min(m + x for x in P) < 0 or m + Wl[0] < 0:
        return 9
    S = max(0.0, tsol - ell)                              # solutions per repetition (log), at least one
    # completions: number of level-i prefixes, from level 1 (pairs) on
    pref = [2 * m + Wl[0]]
    for i in range(1, k1):
        pref.append(pref[-1] + m + Wl[i])
    # expected completions (log, at least 0) of a prefix with j + 2 vectors in one repetition
    comp = {j: max(0.0, S - pref[j]) for j in range(k1)}
    def cost_complete(j):
        """cost to find one completion of a prefix with j + 2 vectors, j = 0 .. k1 - 2"""
        nxt = j + 1
        n = comp[j]
        if nxt == k1 - 1:                                   # last vector: plain search in the bucket
            return 0.5 * (m + P[nxt]) - 0.5 * n if n < m + P[nxt] else 0.0
        # two-oracle search over the next vector: candidates m P, good ones m W
        a = 0.5 * (m + P[nxt] - n)
        b = 0.5 * (max(m + Wl[nxt], n) - n) + cost_complete(nxt)   # the good set contains the target, so has >= 1 element
        return max(a, b)
    T0 = 2 * m + P[0]
    per_sol = max(0.5 * (T0 - S), 0.5 * (pref[0] - S) + cost_complete(0))
    tot = max(ell + m, ell + S + per_sol)
    return tot

if __name__ == "__main__":
    # check: k = 3 reproduces 0.284551
    m3 = 0.25 * log2(27 / 16)
    t3 = time_k(m3, [1 / 3, 1 / sqrt(3)], [0.347606, 0.427124])
    print(f"k=3 check: {t3:.6f}"); assert abs(t3 - 0.284551) < 2e-6
    m4 = log2(256 / 125) / 6
    ts4 = [1 / 4, 1 / sqrt(6), sqrt(3 / 8)]
    # consistency: the chain count m^4 p p p = m
    assert abs(4 * m4 + p(ts4[0]) + p(ts4[1]) + p(ts4[2]) - m4) < 1e-9
    f = lambda c: time_k(m4, ts4, list(c))
    best = None
    for x0 in itertools.product([0.2, 0.3, 0.4, 0.5], [0.3, 0.4, 0.5, 0.6], [0.4, 0.5, 0.6, 0.7]):
        r = minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-9, "fatol": 1e-11, "maxiter": 20000})
        if best is None or r.fun < best.fun:
            best = r
    print(f"k=4, m = {m4:.6f}: cos a = {[round(x, 6) for x in best.x]}, time = {best.fun:.6f} (previous 0.3178)")
