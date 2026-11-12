"""Quantum d-Hitting Set by solution size k: constants and the split step, with asserts."""
import itertools
import random
from fractions import Fraction as F
from math import sqrt

b = F(20409, 10000)                     # branching base of the 3-Hitting Set algorithm [T]

# Bases: square roots, rounded up.
base = {3: F(14287, 10000), 4: F(17439, 10000), 5: F(20102, 10000), 6: F(22452, 10000)}
for d, q in base.items():
    c = b + (d - 3)                     # (c + 1)^k for (d + 1)-Hitting Set by iterative compression [D], [F]
    assert q * q >= c, (d, q)
    assert (q - F(1, 10000)) ** 2 < c, (d, q)   # tight to the last digit
    print(f"d = {d}: classical {float(c):.4f}^k, quantum {float(q)}^k")

# Implied plain-tree walks, for comparison: sqrt(2.168) on [SZ], and sqrt(2.0755) on [W] if its tree is plain.
assert sqrt(2.168) > 1.4724 > 1.4287 and sqrt(2.0755) > 1.4406 > 1.4287
# d = 4, 5, 6: compression on the plain 2.168 tree, or the bases of [Fe] 3.115, 4.08, 5.049 if plain.
for d, fe in ((4, 3.115), (5, 4.08), (6, 5.049)):
    assert float(base[d]) < min(sqrt(2.168 + d - 3), sqrt(fe), sqrt(2.0755 + d - 3)), d

# The implied entries of the table, rounded up: sqrt(2.168) and sqrt(2.168 + d - 3).
for d, imp in ((3, 1.4725), (4, 1.7799), (5, 2.0416), (6, 2.2734)):
    v = sqrt(2.168 + d - 3)
    assert v <= imp < v + 1e-4 and float(base[d]) < imp, d

# The split step of Section 2 for k >= 10: two sums of calls up to K = floor(k/2) and a tail of budget
# at most k - 4 have at most b^(k-2) leaves, so the measure of Lemma 30 of [T] still bounds the tree.
for k in range(10, 400):
    K = k // 2
    calls = 2 * sum(b ** i for i in range(4, K + 1))
    assert calls + b ** (k - 4) <= b ** (k - 2), k
    # (M2): the log measure of a call is at most about half that of its caller.
    assert K <= F(k, 2)


# The decision of the split step equals opt(H) + opt(R) <= k (each part has optimum at least 4).
def opt(edges, verts):
    for s in range(len(verts) + 1):
        for S in itertools.combinations(verts, s):
            if all(set(e) & set(S) for e in edges):
                return s


def split_decision(oH, oR, k):
    K = k // 2
    for i in range(4, min(K, k - 4) + 1):        # value calls on H
        if oH <= i:
            return oR <= k - i                     # tail on R
    for i in range(4, min(K, k - 4) + 1):        # value calls on R
        if oR <= i:
            return oH <= k - i                     # tail on H
    return False


rng = random.Random(5)
n_checks = 0
for _ in range(1500):
    parts = []
    for p in range(2):
        nv = rng.randint(4, 9)
        vs = list(range(p * 20, p * 20 + nv))
        es = [tuple(rng.sample(vs, 3)) for _ in range(rng.randint(3, 3 * nv))]
        parts.append((es, vs))
    oH, oR = (opt(es, vs) for es, vs in parts)
    for k in range(0, 20):
        want = oH + oR <= k
        if oH >= 4 and oR >= 4:
            assert split_decision(oH, oR, k) == want, (oH, oR, k)
            n_checks += 1
assert n_checks > 0
print(n_checks, "split decisions equal opt(H) + opt(R) <= k")
print("all asserts passed")
