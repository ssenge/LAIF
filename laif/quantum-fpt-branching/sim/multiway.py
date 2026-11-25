"""Bases of the Multiway Cut rows of Theorem 3, in exact rational arithmetic where it decides.

Edge Multiway Cut [26]: a search tree with measure m = 2k - h, h the sum of the minimum isolating cut sizes, branching
only when h > (1 - 1/p) k for p terminals, worst branching vector (1, 2, 3). Its leaves number at most tau^m with tau
the root of z^3 = z^2 + z + 1, and m <= k, or m <= (p - 2) k / (p - 1) with p terminals. The walk gives the square root.
Node Multiway Cut [27]: two branches, each lowering L = k - LP by at least 1/2, so 4^L leaves; Reduction 4 of [27]
answers yes when C <= 2L or C >= (s - 2) k / (s - 1), so a branching root has 4^L <= 2^{min(C, (s - 2) k / (s - 1))}
and the walk gives 2^L <= 2^{k/2}, and 2^{k/4} for three terminals.
1. tau, its square root and the p-terminal bases tau^{(p - 2)/(2 (p - 1))}, each rounded up at the fourth decimal.
2. The leaf recursion T(m) = T(m - 1) + T(m - 2) + T(m - 3) of the worst case stays below 2 tau^m.
3. The Node Multiway Cut bases 2^{1/2} and 2^{1/4}, and the implied bases of the earlier trees: 2^{1/2} for the (1, 1)
   tree of edge multiway cut with measure 2k - h, and 2 for the 4^k tree of node multiway cut.
Run: python multiway.py
"""
from fractions import Fraction as F
from functools import lru_cache


def root(f, lo, hi, it=200):
    for _ in range(it):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) < 0 else (lo, mid)
    return lo, hi


tau_lo, tau_hi = root(lambda z: z ** 3 - z ** 2 - z - 1, F(3, 2), F(2), 120)
assert tau_hi - tau_lo < F(1, 10 ** 30)
assert F(18392, 10000) < tau_lo and tau_hi < F(18393, 10000)       # tau = 1.83928...
print(f"tau = {float(tau_lo):.6f} (printed as 1.84 in [26])")


def up(base, exp_num, exp_den):
    """Smallest 4-decimal x >= 1 with x^exp_den >= base^exp_num; base "tau" uses the upper end of its interval."""
    target = (tau_hi if base == "tau" else F(base)) ** exp_num
    x = F(1)
    while x ** exp_den < target:
        x += F(1, 10000)
    return x


edge = up("tau", 1, 2)
assert edge == F(13563, 10000), edge                                  # sqrt(tau) <= 1.3563
assert (edge - F(1, 10000)) ** 2 < tau_lo                             # and 1.3562 is too small
print(f"Edge Multiway Cut: sqrt(tau) <= {float(edge):.4f}")

bases = {}
for p in range(3, 9):
    num, den = p - 2, 2 * (p - 1)                                     # tau^{(p-2)/(2(p-1))}
    b = up("tau", num, den)
    assert (b - F(1, 10000)) ** den < tau_lo ** num
    bases[p] = b
assert bases[3] == F(11646, 10000)
print("p-terminal bases tau^((p-2)/(2(p-1))):", {p: float(b) for p, b in bases.items()})


@lru_cache(maxsize=None)
def leaves(m):
    return 1 if m <= 0 else leaves(m - 1) + leaves(m - 2) + leaves(m - 3)


for m in range(0, 400):
    assert leaves(m) <= 2 * tau_hi ** m, m
print("worst-case leaf recursion (1, 2, 3) stays below 2 tau^m for m < 400")

node = up(2, 1, 2); node3 = up(2, 1, 4)
assert node == F(14143, 10000) and node3 == F(11893, 10000)
assert (node - F(1, 10000)) ** 2 < 2 and (node3 - F(1, 10000)) ** 4 < 2
print(f"Node Multiway Cut: 2^(1/2) <= {float(node):.4f}, three terminals 2^(1/4) <= {float(node3):.4f}")
assert edge < node and bases[3] < node3                               # the new trees beat the implied (1, 1) / 4^k ones
print("all checks passed")
