"""Checks for the quantum approximate counter of independent sets (Theorem 1).

Preprocessing tree P (Algorithm 9 of [1]): branch on a vertex v of maximum degree >= 6 (exclude v: budget -1,
include v: budget -(deg v + 1) <= -7), stop when the budget b <= 0 (hard leaf) or when the maximum degree is at
most 5 (easy leaf).
Compiled tree C: P with every hard leaf H replaced by the include/exclude tree of H (branch on the first vertex;
exclude deletes it, include deletes its closed neighbourhood; a leaf is the empty graph).

1. Exact identity: C is a full binary tree, and  #IS(G) = (N + 1)/2 + sum over easy leaves e of (#IS(e) - 1),
   with N the number of nodes of C.  Checked on random graphs against brute-force counting.
2. Ticket bounds: P has at most T(b) leaves, T(b) = T(b-1) + T(b-7) for b > 0 and T(b) = 1 for b <= 0, and the
   node-ticket map of C sends its marked tickets bijectively onto the root paths of the nodes of C, inside a
   universe of size at most U_C = 2 T(budget) 2^{(1 - beta) n}.
3. Bucketed sum: for values f_e and (1 +- eps)-accurate estimates, sum over buckets (1+eps)^k M_k is within a factor
   (1 +- 3 eps) of sum f_e.
4. Exponents: a = log2 of the root of x^7 = x^6 + 1, 2^{-a} + 2^{-7a} <= 1, beta = 1/(1 + a), quantum exponent
   a / (2 (1 + a)) and the comparison bases.
Run: python isapprox.py
"""
import itertools, random
from fractions import Fraction
from math import log2, ceil, floor

random.seed(3)


def count_is(adj, verts):
    """Exact number of independent sets of the induced graph on verts (branching, exponential)."""
    verts = frozenset(verts)
    if not verts:
        return 1
    v = max(verts, key=lambda u: len(adj[u] & verts))
    if not adj[v] & verts:                       # isolated vertex doubles the count
        return 2 * count_is(adj, verts - {v})
    return count_is(adj, verts - {v}) + count_is(adj, verts - (adj[v] | {v}))


def easy(adj, verts):
    """Easy test: maximum degree at most 5."""
    return all(len(adj[u] & verts) <= 5 for u in verts)


def branch_vertex(adj, verts):
    """A vertex of maximum degree, smallest label first."""
    return max(verts, key=lambda u: (len(adj[u] & verts), -u))


def preprocess(adj, verts, b, hard, easy_l, stats):
    """Algorithm 9 of [1] with budget ceil(beta n); records the hard and easy leaves and the number of P nodes."""
    stats["P"] += 1
    if b <= 0:
        hard.append(verts); return
    if easy(adj, verts):
        easy_l.append(verts); return
    v = branch_vertex(adj, verts)
    d = len(adj[v] & verts)
    assert d >= 6
    preprocess(adj, verts - {v}, b - 1, hard, easy_l, stats)
    preprocess(adj, verts - (adj[v] | {v}), b - (d + 1), hard, easy_l, stats)


def naive_nodes(adj, verts):
    """Nodes of the include/exclude tree on the first vertex (sorted order)."""
    if not verts:
        return 1
    v = min(verts)
    return 1 + naive_nodes(adj, verts - {v}) + naive_nodes(adj, verts - (adj[v] | {v}))


def T(b, memo={}):
    if b <= 0:
        return 1
    if b not in memo:
        memo[b] = T(b - 1) + T(b - 7)
    return memo[b]


A_EXP = 0.328174
beta = 1 / (1 + A_EXP)

checked = 0
for n in range(8, 19):
    for p in (0.4, 0.55, 0.7, 0.85):
        for _ in range(2):
            adj = {u: set() for u in range(n)}
            for u, w in itertools.combinations(range(n), 2):
                if random.random() < p:
                    adj[u].add(w); adj[w].add(u)
            adj = {u: frozenset(s) for u, s in adj.items()}
            V = frozenset(range(n))
            budget = ceil(beta * n)
            hard, easy_l, stats = [], [], {"P": 0}
            preprocess(adj, V, budget, hard, easy_l, stats)
            leaves = len(hard) + len(easy_l)
            assert stats["P"] == 2 * leaves - 1                          # P is a full binary tree
            assert leaves <= T(budget)                                    # leaf bound
            for H in hard:
                assert len(H) <= n - budget                               # hard residuals are small
            # node count of the compiled tree: P nodes minus hard leaves plus their include/exclude trees
            N = stats["P"] - len(hard) + sum(naive_nodes(adj, H) for H in hard)
            assert N % 2 == 1                                             # full binary tree
            total = count_is(adj, V)
            assert sum(count_is(adj, H) for H in hard) + sum(count_is(adj, E) for E in easy_l) == total
            assert (N + 1) // 2 + sum(count_is(adj, E) - 1 for E in easy_l) == total, (n, p)
            assert N <= 2 * T(budget) * 2 ** (n - budget)                 # node-ticket universe U_C
            checked += 1
print(f"identity #IS = (N + 1)/2 + sum_easy (f - 1) holds on {checked} random graphs (n <= 18)")

# 2b. node tickets: ticket m at a node of the compiled tree; 0 is the node itself, then the children's blocks
def node_ticket(adj, verts, b, m, n, budget, phase, path=()):
    """Returns the node reached by ticket m, or None.  Bounds: P node with budget b: 2 T(b) 2^{n - budget} - 1;
    include/exclude node on k vertices: 2^{k + 1} - 1 (full binary tree with at most 2^k leaves)."""
    if phase == "P" and (b <= 0):
        phase = "core"
    if phase == "P" and easy(adj, verts):
        return path if m == 0 else None
    if m == 0:
        return path
    m -= 1
    if phase == "P":
        v = branch_vertex(adj, verts); d = len(adj[v] & verts)
        kids = [(verts - {v}, b - 1), (verts - (adj[v] | {v}), b - (d + 1))]
        for i, (kv, kb) in enumerate(kids):
            bound = (2 * T(kb) * 2 ** (n - budget) - 1) if kb > 0 else (2 ** (len(kv) + 1) - 1)
            if m < bound:
                return node_ticket(adj, kv, kb, m, n, budget, "P", path + (i,))
            m -= bound
        return None
    if not verts:
        return None
    v = min(verts)
    for i, kv in enumerate((verts - {v}, verts - (adj[v] | {v}))):
        bound = 2 ** (len(kv) + 1) - 1
        if m < bound:
            return node_ticket(adj, kv, 0, m, n, budget, "core", path + (i,))
        m -= bound
    return None

for n, p in ((10, 0.7), (12, 0.7), (11, 1.0), (12, 0.5), (13, 0.85)):
    adj = {u: set() for u in range(n)}
    for u, w in itertools.combinations(range(n), 2):
        if random.random() < p:
            adj[u].add(w); adj[w].add(u)
    adj = {u: frozenset(s) for u, s in adj.items()}
    V = frozenset(range(n)); budget = ceil(beta * n)
    U = 2 * T(budget) * 2 ** (n - budget) - 1
    hits = [node_ticket(adj, V, budget, m, n, budget, "P") for m in range(U)]
    hard, easy_l, stats = [], [], {"P": 0}
    preprocess(adj, V, budget, hard, easy_l, stats)
    N = stats["P"] - len(hard) + sum(naive_nodes(adj, H) for H in hard)
    paths = [h for h in hits if h is not None]
    assert len(paths) == len(set(paths)) == N, (n, N)                  # distinct root paths, one per node
    assert U <= 2 * T(budget) * 2 ** (n - budget)                      # inside U_C
print("node-ticket map hits every node of the compiled tree exactly once (exhaustive over the universe)")

# 3. bucketed sum with (1 +- eps)-accurate estimates
for eps in (Fraction(1, 4), Fraction(1, 10), Fraction(1, 50)):
    for _ in range(200):
        f = [random.choice([1, 2, 3, random.randint(1, 10 ** 6)]) for _ in range(30)]
        est = [x * (1 + eps * Fraction(random.randint(-1000, 1000), 1000)) for x in f]
        w = 0
        for x in est:                                   # bucket k with (1+eps)^k <= x < (1+eps)^{k+1}, weight (1+eps)^k
            k = floor(log2(float(x)) / log2(float(1 + eps)))
            while (1 + eps) ** k > x: k -= 1
            while (1 + eps) ** (k + 1) <= x: k += 1
            w += (1 + eps) ** k
        assert (1 - 3 * eps) * sum(f) <= w <= (1 + 3 * eps) * sum(f)
print("bucketed sums lie within (1 +- 3 eps) of the true sums")

# 4. exponents
lo, hi = 1.0, 2.0
for _ in range(200):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if mid ** 7 - mid ** 6 - 1 < 0 else (lo, mid)
assert log2(hi) <= A_EXP and 2 ** -A_EXP + 2 ** (-7 * A_EXP) <= 1
q = A_EXP / (2 * (1 + A_EXP)); c = A_EXP / (1 + A_EXP)
assert abs(beta * A_EXP - (1 - beta)) < 1e-12                      # balance: preprocessing size = residual size
assert 2 ** q < 1.0895 and 2 ** c < 1.1869
mixed = A_EXP / (1 + 3 * A_EXP)                                     # classical preprocessing, quantum cores
easy_only = log2(hi) / 2                                            # bucketed count over the leaves of P with no budget
assert 2 ** mixed > 1.1214 and 2 ** 0.25 > 1.1892 and 2 ** easy_only > 1.1204
print(f"quantum exponent a/(2(1 + a)) = {q:.6f}: base {2 ** q:.5f}; classical [1] {2 ** c:.5f};"
      f" classical preprocessing with quantum cores {2 ** mixed:.5f}; bucketed count without budget {2 ** easy_only:.5f};"
      f" include/exclude tree alone {2 ** 0.25:.5f}")
print("all checks passed")
