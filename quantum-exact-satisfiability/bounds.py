"""Quantum bases for Exact Satisfiability: square roots of the classical branching bases."""
import math


def tau(*d):
    """Branching number: the root x > 1 of sum x^(-d_i) = 1, by bisection."""
    lo, hi = 1.0, 2.0
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if sum(mid ** -x for x in d) > 1 else (lo, mid)
    return hi


# X3SAT: the branching vectors of the X3SAT algorithm (Table 1(b)) and its sparse enumeration 2^(2n/15)
x3 = tau(12, 4)
assert all(tau(*v) <= x3 for v in ((11, 5), (9, 6), (8, 7))) and 2 ** (2 / 15) <= x3
print(f"tau(12,4) = {x3:.6f} = 2^{math.log2(x3):.6f}; sparse enumeration 2^(2/15) = {2 ** (2 / 15):.6f}")

for name, b in (("XSAT, DPLL with a nonstandard measure", 1.1674),
                ("X3SAT, branch and reduce with sparse enumeration", x3)):
    q = math.ceil(math.sqrt(b) * 1e4) / 1e4
    assert math.sqrt(b) <= q
    # crossover with the bound 2^((n - M')/2) of the subspace search: equal when M' = (1 - 2 log2 q) n
    print(f"{name}: sqrt({b:.6f}) = {math.sqrt(b):.6f} <= {q}; crossover M'/n = {1 - 2 * math.log2(q):.4f}")
