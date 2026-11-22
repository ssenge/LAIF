"""Checks for Theorem 5 (Mixed Dominating Set).

1. The branching vectors of the exact algorithm [18, Section 4] and the FPT algorithm [18, Section 5], as characteristic
   equations x^a = sum c_e x^e: every printed root bound r satisfies sum c_e r^(e - a) < 1, exactly, so the root is below
   r, or the script reports the rule. The largest roots are below 1.3252 (exact, rule B5) and 1.8734 (FPT, rule B3.2).
2. The tree of the first step: branching on a vertex v of minimum degree, with one child for each u in N[v] put into the
   independent set and N[u] removed. On random graphs its leaves include every maximal independent set (so the
   complements include every minimal vertex cover) and its number of nodes is at most (n + 1) * 3^(n/3).
3. Bases: the walk on the FPT tree has size 1.8734^l with l <= 2k, so its square root is 1.8734^k; for the exact
   algorithm sqrt(3^(n/3) * 1.3252^n) <= 1.3825^n, i.e. 1.3825^6 >= 3 * 1.3252^3, and 1.3824^6 < 3 * 1.3252^3.
"""
import itertools, random
from fractions import Fraction as F
from math import comb

def poly(spec):                     # "x6 = x5 + 3x2 + 3x + 4" -> (6, {5: 1, 2: 3, 1: 3, 0: 4})
    lhs, rhs = spec.replace(" ", "").split("=")
    a = int(lhs[1:]); terms = {}
    for t in rhs.split("+"):
        if "x" in t:
            c, e = t.split("x"); c = int(c or 1); e = int(e or 1)
        else:
            c, e = int(t), 0
        terms[e] = terms.get(e, 0) + c
    return a, terms

EXACT = [("x5 = x4 + 1", "1.3248"), ("x3 = 2", "1.2600"), ("x4 = x2 + 1", "1.2721"), ("x4 = 3", "1.3161"),
         ("x5 = x2 + x + 1", "1.3248"), ("x14 = x10 + 3x8 + 3x2 + 1", "1.3252"), ("x10 = x9 + x3 + 1", "1.3001")]
FPT = [("x2 = x + 1", "1.6181"), ("x4 = x3 + 2x + 1", "1.7944"), ("x3 = x2 + 3", "1.8638"),
       ("x6 = x5 + 2x3 + x2 + 1", "1.8199"), ("x6 = x5 + 3x2 + 3x + 1", "1.8205"), ("x6 = x5 + 3x2 + 3x + 2", "1.8393"),
       ("x5 = x4 + 4x + 2", "1.8305"), ("x6 = x5 + 3x2 + 3x + 4", "1.8734"), ("x6 = x5 + 4x2 + 2x + 2", "1.8672"),
       ("x5 = x4 + 5x + 1", "1.8603"), ("x8 = x7 + 4x3 + 6x2 + 10x + 1", "1.8595"), ("x8 = x7 + 6x3 + 6x2 + 4x + 1", "1.8665"),
       ("x7 = x6 + 6x2 + 6x + 5", "1.8700"), ("x5 = x4 + 7", "1.7487")]
# rule B5 for i = d_U(u) = 5..8: T(l) <= T(l-1) + (i-1) T(l-i-1) + sum_j C(i,j) T(l-i-j); rule B6 with 9 neighbours
for i, r in ((5, "1.8473"), (6, "1.8104"), (7, "1.7816"), (8, "1.7593")):
    t = {2 * i - 1: 1, i - 1: i - 1}
    for j in range(1, i + 1):
        t[i - j] = t.get(i - j, 0) + comb(i, j)
    FPT.append(((2 * i, t), r))
t = {17: 1, 16: 1}
for j in range(10):
    t[9 - j] = t.get(9 - j, 0) + comb(9, j)
FPT.append(((18, t), "1.8640"))

def g(a, terms, r):
    return sum(c * r ** (e - a) for e, c in terms.items())

def root(a, terms):                 # bracket of the unique root > 1 of sum c_e x^(e - a) = 1, width 1e-6
    lo, hi = F(1), F(4)
    while hi - lo > F(1, 10 ** 6):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if g(a, terms, mid) > 1 else (lo, mid)
    return lo, hi

def check(rows):
    worst, low = F(0), []
    for spec, r in rows:
        a, terms = poly(spec) if isinstance(spec, str) else spec
        lo, hi = root(a, terms)
        if g(a, terms, F(r)) >= 1:            # the printed bound is below the root
            low.append((spec, r, float(hi)))
        worst = max(worst, hi)
    return worst, low
we, low_e = check(EXACT); wf, low_f = check(FPT)
assert we <= F("1.3252") and wf <= F("1.8734"), (we, wf)
assert g(14, poly("x14 = x10 + 3x8 + 3x2 + 1")[1], F("1.3252")) < 1 and g(6, poly("x6 = x5 + 3x2 + 3x + 4")[1], F("1.8734")) < 1
for spec, r, hi in low_e + low_f:
    print(f"printed bound {r} lies below the root {hi:.5f} of {spec}; the largest root is unchanged")
print(f"branching roots: {len(EXACT)} exact rules below 1.3252, {len(FPT)} FPT rules below 1.8734")

def tree(vs, adj):
    """Nodes and leaves (as independent sets) of the first-step tree."""
    vs = frozenset(vs)
    if not vs:
        return 1, [frozenset()]
    v = min(vs, key=lambda x: (len(adj[x] & vs), x))
    nodes, leaves = 1, []
    for u in sorted((adj[v] & vs) | {v}):
        nn, ll = tree(vs - adj[u] - {u}, adj)
        nodes += nn; leaves += [l | {u} for l in ll]
    return nodes, leaves

random.seed(3)
for _ in range(300):
    n = random.randint(1, 11); p = random.random()
    adj = {x: set() for x in range(n)}
    for a, b in itertools.combinations(range(n), 2):
        if random.random() < p:
            adj[a].add(b); adj[b].add(a)
    nodes, leaves = tree(range(n), adj)
    assert nodes <= (n + 1) * 3 ** (n / 3) + 1e-9, (n, nodes)
    mis = [frozenset(S) for r in range(n + 1) for S in itertools.combinations(range(n), r)
           if all(b not in adj[a] for a, b in itertools.combinations(S, 2))
           and all(x in S or adj[x] & set(S) for x in range(n))]
    assert set(mis) <= set(leaves), (n, adj)
print("first-step tree: all maximal independent sets reached, nodes <= (n + 1) 3^(n/3), 300 random graphs")

assert F("1.3825") ** 6 >= 3 * F("1.3252") ** 3 > F("1.3824") ** 6
print("bases: 1.8734^k and 1.3825^n")
print("all checks passed")
