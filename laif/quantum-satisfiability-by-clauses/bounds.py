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

# SAT in terms of the length L: the bound 2^(0.0926 L) of SparseSAT and its square root
ql = math.ceil(math.sqrt(2 ** 0.0926) * 1e4) / 1e4
assert 2 ** 0.0926 <= 1.0663 and math.sqrt(2 ** 0.0926) <= ql
print(f"SAT in L: 2^0.0926 = {2 ** 0.0926:.6f}; square root {math.sqrt(2 ** 0.0926):.6f} <= {ql}")

# SAT in terms of L, second tree: the branching vectors of the 1.0638^L algorithm [9, Table 3] with its weights
w3, s = 1.94719, 0.86108
w4, w5, w6 = 2 * w3, 5.0, 6.0
d4, d5, d6 = w4 - w3, w5 - w4, 1.0
vectors = {
    "3": (w6 + d6, w6 + 11 * d6), "4": (w5 + 2 * w3, w5 + w3 + 7 * d5), "5": (w5 + 2 * d5, w5 + 4 * w3 + 4 * d5),
    "6": (w5 + 3 * d5 - s, 2 * w5 + 2 * w3 + 3 * d5 - s), "7": (w5 + w3 + 2 * d5, w5 + w3 + 6 * d5),
    "8": (w5 + 4 * d5, w5 + 2 * w3 + 4 * d5), "9": (w5 + 4 * d5, w5 + d4 + 6 * d5),
    "10a": (w5 + 4 * d5, w5 + w4 + 6 * d5), "10b": (w5 + 4 * d5, w5 + w3 + 6 * d5),
    "11": (w5 + 4 * d5, w5 + 7 * d5 + s), "12a": (w5 + 4 * d5, w5 + 4 * d5 + 2 * w3),
    "12b": (w5 + 4 * d5, w5 + w3 + 5 * d5 + s), "14": (w4 + 2 * w3, w4 + 6 * d4), "15": (w4 + 2 * d4, w4 + 6 * d4),
}
a = 1.0638
for k, v in vectors.items():
    assert tau(*v) <= a, k
print("steps " + ", ".join(f"{k}: {tau(*v):.5f}" for k, v in vectors.items()))
# Step 16: SparseSAT on formulas of maximum degree 3, 1.1279^n with mu = w3 n
assert 1.1279 ** (1 / w3) <= a
# Step 13: the 3-CNF part with n* variables of weight 5, by the (4/3 + eps)^n* tree of [12] with 4/3 + eps <= 1.34
assert 1.34 ** (1 / 5) < a and 1.34 <= a ** 5
qa = math.ceil(math.sqrt(a) * 1e4) / 1e4
assert math.sqrt(a) <= qa == 1.0315 and a <= qa ** 2
print(f"SAT in L, second tree: Step 16 1.1279^(1/w3) = {1.1279 ** (1 / w3):.6f}, Step 13 1.34^(1/5) = {1.34 ** 0.2:.6f}; "
      f"all <= {a}; square root {math.sqrt(a):.6f} <= {qa}")
