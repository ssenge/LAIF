"""Quantum SAT in terms of the number of clauses m: the search tree of the 1.2226^m algorithm and its square root."""
import math
from fractions import Fraction as Fr


def tau(*d):
    """Branching number: the root x > 1 of sum x^(-d_i) = 1, by bisection."""
    lo, hi = 1.0, 2.0
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if sum(mid ** -x for x in d) > 1 else (lo, mid)
    return hi


for v in ((3, 3), (3, 4), (3, 5), (4, 4)):
    print(f"tau{v} = {tau(*v):.4f}")

# the substitution proof of Theorem 1: T(F) <= c1 g^m - 1 for good F, c2 g^m - 1 for bad F, in exact arithmetic
g, c1 = Fr(12226, 10000), Fr(2)
c2 = c1 / Fr(9136, 10000)
checks = {
    "bad, (3,4), children of either kind": c2 * (g ** -3 + g ** -4) <= c2,
    "bad, (3,3), both children good": 2 * c1 * g ** -3 <= c2,
    "good, (3,5), children of either kind": c2 * (g ** -3 + g ** -5) <= c1,
    "good, (4,4), children of either kind": 2 * c2 * g ** -4 <= c1,
    "good, (3,4), both children good": c1 * (g ** -3 + g ** -4) <= c1,
    "reduction from good to bad removes a clause": c2 <= g * c1 and c1 <= c2,
}
for k, ok in checks.items():
    print(f"{k}: {ok}")
    assert ok

q = math.ceil(math.sqrt(1.2226) * 1e4) / 1e4
assert math.sqrt(1.2226) <= q
print(f"quantum base sqrt(1.2226) = {math.sqrt(1.2226):.6f} <= {q}")
for name, b in (("1.239^m", 1.239), ("1.260^m", 1.26)):
    print(f"walk on the {name} algorithm: {math.sqrt(b):.4f}")
# against quantum search over all assignments, 2^(n/2): 1.1058^m is smaller iff m < n ln(2) / (2 ln 1.1058)
print(f"below 2^(n/2) whenever m < {math.log(2) / (2 * math.log(q)):.4f} n")

# MaxSAT: the largest branching factor (6, 6, 5, 5) of the 1.2886^m algorithm and its square root
assert tau(6, 6, 5, 5) <= 1.2886 and 1.2576 <= 1.2886
qm = math.ceil(math.sqrt(1.2886) * 1e4) / 1e4
assert math.sqrt(1.2886) <= qm
print(f"MaxSAT: tau(6,6,5,5) = {tau(6, 6, 5, 5):.5f}; sqrt(1.2886) = {math.sqrt(1.2886):.6f} <= {qm}; "
      f"below 2^(n/2) whenever m < {math.log(2) / (2 * math.log(qm)):.4f} n")
