"""Support of the index superposition of the unrolled split recursion for Minimum Steiner Tree, against the stated
amplitude-amplification count. Every node of the recursion tree carries its own split of its terminal set and its own
vertex set A (Figure 2 of the source). Lower bound used here: A empty at every node and exact halving (alpha = 1/2,
eta = 0), k a power of two, recursion down to singletons (l0 = lm = log2 k). Every extra choice only enlarges the support.
    python support.py"""
from itertools import combinations
from math import comb, factorial, isqrt, log2

def trees(K):
    """All index states (with A empty): a node chooses the left half K1 of its terminal set, the children recurse."""
    K = tuple(K)
    if len(K) == 1: return 1
    tot = 0
    for K1 in combinations(K, len(K) // 2):
        K2 = tuple(x for x in K if x not in K1)
        tot += trees(K1) * trees(K2)
    return tot

def N(k):                      # closed form of trees(range(k)): N(k) = C(k, k/2) N(k/2)^2 = k!
    return 1 if k == 1 else comb(k, k // 2) * N(k // 2) ** 2

def stated(k):                 # the stated product: one binomial per level, prod_{l=1}^{log k} C(k/2^(l-1), k/2^l)
    p, m = 1, k
    while m > 1: p *= comb(m, m // 2); m //= 2
    return p

for k in (2, 4, 8):            # brute force against the closed form
    assert trees(range(k)) == N(k) == factorial(k), k
for m in range(1, 9):
    k = 2 ** m
    assert N(k) == factorial(k)
    assert stated(k) <= 4 ** k                       # the stated count is at most 2^(2k), so its square root at most 2^k
    if k >= 4: assert N(k) > stated(k)               # the support of the state is larger from k = 4 on
    if k >= 16: assert N(k) > 4 ** k                 # and larger than 2^(2k) from k = 16 on
    print(f"k={k:4d}  support >= k! = 2^{log2(N(k)):8.1f}   stated = 2^{log2(stated(k)):7.1f}   2^(2k) = 2^{2 * k}"
          f"   sqrt ratio support/stated >= 2^{(log2(N(k)) - log2(stated(k))) / 2:7.1f}")
# with the vertex sets A: each of the k - 1 internal nodes chooses A subset of V with |A| <= a; for a >= 1 that is a factor
# of at least (n + 1)^(k - 1), so the square root carries n^((k - 1)/2), which is not a polynomial factor for growing k
n, a, k = 20, 1, 8
per_node = sum(comb(n, i) for i in range(a + 1))
assert per_node ** (k - 1) == (n + 1) ** (k - 1)
print(f"with A (n={n}, |A|<=1): extra factor (n+1)^(k-1) = {per_node ** (k - 1)} for k = {k}")
print("all checks passed")
