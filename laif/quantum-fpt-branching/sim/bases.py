"""Bases of the classical trees and of the quantum walks over them (square roots), recomputed from the recurrences.
Vertex Cover above LP [1, Theorem 2] (arXiv:1203.0833): worst branching vector (1, 3/2, 3/2) in mu = k - vc*(G), so the tree has
size x^mu with 1 = x^-1 + 2 x^-3/2. A walk over it costs sqrt(x)^mu up to poly factors. The reductions give mu <= k
(OCT, AGVC, Almost 2-SAT) or mu <= k/2 (KVD with a perfect matching, KVD, VC by KVD, VC by OCT)."""
from fractions import Fraction as F
def root(f, lo, hi):                       # f increasing in x on [lo, hi], f(lo) < 0 < f(hi)
    for _ in range(200):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if f(m) < 0 else (lo, m)
    return hi
x = root(lambda x: 1 - 1 / x - 2 / x ** 1.5, 1.5, 4)          # 1 = x^-1 + 2 x^-3/2
y, z = x ** 0.5, x ** 0.25
print(f"classical above LP {x:.6f}, quantum mu {y:.6f}, quantum k/2 {z:.6f}")
assert x <= 2.3146 and abs(x - 2.3146) < 1e-4                   # the paper's 2.3146 is the root rounded up
# printed bases are upper bounds: check them exactly on the recurrence of the walk, b^-2 + 2 b^-3 <= 1 (b = sqrt x)
for b, scale in ((F(15214, 10000), 1), (F(12335, 10000), 2)):    # mu <= k, mu <= k/2 (b^2 = 1.5214^.. per k)
    c = b ** scale                                                # quantum base per unit of mu
    assert 1 / c ** 2 + 2 / c ** 3 <= 1, (b, scale)
assert y < 1.5214 and z < 1.2335
print("bases ok: 1.5214^k (mu <= k), 1.2335^k (mu <= k/2)")
# simple quantum baselines: search over the 3^k compression steps and over the 2^k subsets of a transversal
assert F(17321, 10000) ** 2 >= 3 and F(17320, 10000) ** 2 < 3
assert F(14143, 10000) ** 2 >= 2 and F(14142, 10000) ** 2 < 2
assert F(15214, 10000) < F(17321, 10000) and F(12335, 10000) < F(14143, 10000)   # the new bases are below them
print("implied baselines ok: 1.7321^k, 1.4143^k")
# rule B6 of [1]: vector (3/2, 3/2, 5/2, 5/2, 2), the same root as B5
x6 = root(lambda x: 1 - 2 / x ** 1.5 - 2 / x ** 2.5 - 1 / x ** 2, 1.5, 4)
assert abs(x6 - x) < 1e-6, (x6, x)
# best implied quantum baselines: the walk of [3] on the plain tree of [1, Theorem 1], vector (1/2, 1) in mu, root phi^2
x1 = root(lambda x: 1 - 1 / x ** 0.5 - 1 / x, 1.5, 4)
phi = (1 + 5 ** 0.5) / 2
assert abs(x1 - phi ** 2) < 1e-9 and x1 <= 2.6181
assert phi <= 1.6181 and phi ** 0.5 <= 1.2721 and phi ** 0.5 > 1.2720
assert 1.5214 < 1.6181 and 1.2335 < 1.2721
print(f"B6 root {x6:.6f}; implied baselines {phi:.6f}^k and {phi ** 0.5:.6f}^k")
