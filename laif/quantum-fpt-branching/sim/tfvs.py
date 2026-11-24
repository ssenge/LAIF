"""Exponents of Theorem 6 (Feedback Vertex Set in Tournaments), exact rational arithmetic where it decides.

Classical algorithm of [19] (arXiv:1510.07676): a family X of 2^{O(k/log k)} pairs (Lemma 5), a reduction to d-FVC with
d = 2 log^4 k (Lemma 6), a (1, 2) branching tree in k and a (1, 3) tree in n (Lemma 9), whose leaves call the
divide-and-conquer minimization of Lemma 7 on s disjoint undirected edges: min over C subset of E(X, Y),
|E(X, Y)| <= s/2 + d, of |E(X, Y)| plus the optima of two independent instances with at most s/4 + d^2 edges each.

Quantum form checked here:
1. Lemma 7 as nested minimum finding of depth D with classical leaves run reversibly (time T^{1+eps}):
   log2 Q(s) <= sum_{l<D} (s_l/2 + d)/2 + (1+eps)(2/3) s_D + O(D d^2 + log), s_{l+1} <= s_l/4 + d^2,
   so log2 Q(s) <= s (1/3 + eta) + O(D d^2) with eta = (1 + 2 eps) / (3 4^D).
2. Parameter k: for each leaf size s0, the walk over the tree cut at budget s0 (O(phi^{k-s0}) nodes)
   with leaf checks of cost Q(s0): exponent (k - s0) log2(phi)/2 + s0 (1/3 + eta) <= k log2(phi)/2 iff
   1/3 + eta <= log2(phi)/2.
3. Parameter n: tree x^3 = x^2 + 1 (root rho = 1.46557...), truncated at n0 vertices, leaf with s <= n0/2 edges:
   (n - n0) log2(rho)/2 + (n0/2)(1/3 + eta) <= n log2(rho)/2 iff (1/3 + eta)/2 <= log2(rho)/2.
4. The (1, 2) tree cut at budget s0 has O(phi^{k-s0}) nodes; Lemma 7's classical leaf count recursion gives 2^{2s/3}.
"""
from fractions import Fraction as F
from math import log2, sqrt

def root(f, lo, hi):
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) < 0 else (lo, mid)
    return lo, hi

phi_lo, phi_hi = root(lambda x: x * x - x - 1, F(3, 2), F(2))
rho_lo, rho_hi = root(lambda x: x ** 3 - x ** 2 - 1, F(7, 5), F(3, 2))
assert abs(float(phi_lo) - (1 + sqrt(5)) / 2) < 1e-12
print(f"phi = {float(phi_lo):.6f}, rho = {float(rho_lo):.6f} (x^3 = x^2 + 1)")

LOG2PHI_LO = F(6942, 10000)            # log2 phi = 0.694241...
LOG2RHO_LO = F(5514, 10000)            # log2 rho = 0.551463...
assert 2 ** float(LOG2PHI_LO) < float(phi_lo) and 2 ** float(LOG2RHO_LO) < float(rho_lo)

def eta(D, eps): return (1 + 2 * eps) / (3 * F(4) ** D)

D, EPS = 3, F(1, 10)
e = eta(D, EPS)
assert F(1, 3) + e < LOG2PHI_LO / 2, (float(F(1, 3) + e), float(LOG2PHI_LO / 2))
assert (F(1, 3) + e) / 2 < LOG2RHO_LO / 2
print(f"D = {D}, eps = {float(EPS)}: leaf base 2^(1/3 + eta) = {2 ** float(F(1, 3) + e):.5f} < sqrt(phi) = {sqrt(float(phi_lo)):.5f};"
      f" in n: 2^((1/3 + eta)/2) = {2 ** float((F(1, 3) + e) / 2):.5f} < sqrt(rho) = {sqrt(float(rho_lo)):.5f}")

# 1. integer recursion of the nested minimization: exponent sum <= s (1/3 + eta) + C D d^2
for d in (1, 4, 16, 64):
    for s in list(range(0, 400)) + list(range(400, 200000, 997)):
        sl, tot = F(s), F(0)
        for _ in range(D):
            tot += (sl / 2 + d) / 2           # square root of the 2^{s/2 + d} choices of C
            sl = sl / 4 + d * d               # each of the two subinstances
        tot += (1 + EPS) * F(2, 3) * sl        # classical leaf 1.5874^{s_D}, reversibly
        assert tot <= s * (F(1, 3) + e) + 3 * D * d * d, (s, d)

# 2./3. the maximum over s0 of the combined exponent is at s0 = 0 (k) and n0 = 0 (n)
for k in range(0, 300):
    assert max((k - s0) * LOG2PHI_LO / 2 + s0 * (F(1, 3) + e) for s0 in range(k + 1)) == k * LOG2PHI_LO / 2
    assert max((k - n0) * LOG2RHO_LO / 2 + F(n0, 2) * (F(1, 3) + e) for n0 in range(k + 1)) == k * LOG2RHO_LO / 2

# 4. nodes of the (1, 2) tree cut at budget s0, and the classical leaf recursion of Lemma 7
from functools import lru_cache
@lru_cache(maxsize=None)
def nodes(j):                                  # cut tree with j = budget - s0; budget below s0 is a leaf
    return 1 if j < 0 else 1 + nodes(j - 1) + nodes(j - 2)
for j in range(0, 200):
    assert nodes(j) <= 3 * float(phi_hi) ** (j + 1), j        # O(phi^{k - s0})
assert sqrt(2) < 1.4143 and sqrt(1.6740) < 1.2939            # implied baselines, rounded up
@lru_cache(maxsize=None)
def h(s): return 1 if s <= 4 else 2 ** (1 + s // 2) * h(s // 4)
for s in range(0, 2000):
    assert log2(h(s)) <= 2 * s / 3 + 3 * log2(s + 2) ** 2, s
print("all checks passed")
