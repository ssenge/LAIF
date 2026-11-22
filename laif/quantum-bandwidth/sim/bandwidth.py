"""Checks for the polynomial-space quantum algorithm for Bandwidth.

1. The bucket-assignment reduction, as used: bandwidth <= b iff some bucket assignment sigma (offsets in {-1, 0, +1}
   along a spanning tree, correct bucket sizes, no edge across two or more buckets) admits a path from the empty set to
   V through balanced sets, each step inserting a vertex v at the next position of its bucket such that v has no
   neighbour in the previous bucket inside S and all its neighbours in the next bucket are already in S. The path is
   decided by the halving recursion over middle sets that the algorithm runs. Compared with brute force over all
   orderings on random connected graphs.
2. The number of locally valid pairs (sigma, S) is exactly k * 2 * 5^(n-1): 5 choices per non-root vertex.
3. The exponent: sqrt(5^n) * prod_{l=1}^{D-1} 2^(n / 2^(l+1)) * 4^((1+eps) n / 2^D) <= 3.1623^n up to subexponential
   factors, i.e. sqrt(10) * 2^((1 + 2 eps) / 2^D) < 3.1623 strictly, checked in exact rationals with ln 2 < 0.6932.
"""
import itertools, random
from fractions import Fraction as F

def bw_brute(n, E):
    best = n
    for p in itertools.permutations(range(n)):
        best = min(best, max((abs(p[u] - p[v]) for u, v in E), default=0))
    return best

def spanning_tree(n, adj):
    par, order, seen = {0: None}, [0], {0}
    for x in order:
        for y in sorted(adj[x]):
            if y not in seen:
                seen.add(y); par[y] = x; order.append(y)
    return par, order

def positions_order(sizes):
    """Fill order of positions: offset j, then bucket i; full buckets are skipped."""
    return [(i, j) for j in range(max(sizes)) for i in range(len(sizes)) if j < sizes[i]]

def path_exists(n, adj, sig, sizes, par=None):
    def locally_valid(S):
        for v in range(n):
            p = par[v] if par else None
            if p is None:
                continue
            if p in S and sig[v] == sig[p] + 1 and v not in S:
                return False
            if p not in S and sig[v] == sig[p] - 1 and v in S:
                return False
        return True
    order = positions_order(sizes)
    bucket = lambda i: [v for v in range(n) if sig[v] == i]
    def step_ok(S, v):            # insert v at the next position of the fill order
        t = len(S)
        i, _ = order[t]
        if sig[v] != i:
            return False
        if any(sig[u] == i - 1 and u in S for u in adj[v]):
            return False
        if any(sig[u] == i + 1 and u not in S for u in adj[v]):
            return False
        return True
    def balanced(S):
        cnt = [0] * len(sizes)
        for v in S:
            cnt[sig[v]] += 1
        want = [0] * len(sizes)
        for (i, _) in order[:len(S)]:
            want[i] += 1
        return cnt == want
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def path(A, B):               # halving recursion over middle sets
        A, B = set(A), set(B)
        m = len(B) - len(A)
        if m == 0:
            return True
        if m == 1:
            (v,) = tuple(B - A)
            return step_ok(A, v)
        h = m // 2
        for C in itertools.combinations(sorted(B - A), h):
            M = A | set(C)
            if balanced(M) and path(frozenset(A), frozenset(M)) and path(frozenset(M), frozenset(B)):
                if not A:                         # a top-level middle set on a sequence is locally valid for sigma
                    assert locally_valid(M), (sig, M)
                return True
        return False
    return path(frozenset(), frozenset(range(n)))

def bw_buckets(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v); adj[v].add(u)
    par, order = spanning_tree(n, adj)
    for b in range(1, n):
        k = -(-n // (b + 1)); sizes = [b + 1] * (k - 1) + [n - (k - 1) * (b + 1)]
        found = False
        for root_bucket in range(k):
            for offs in itertools.product((-1, 0, 1), repeat=n - 1):
                sig = {order[0]: root_bucket}
                for v, s in zip(order[1:], offs):
                    sig[v] = sig[par[v]] + s
                if any(not 0 <= sig[v] < k for v in range(n)):
                    continue
                if [sum(1 for v in range(n) if sig[v] == i) for i in range(k)] != sizes:
                    continue
                if any(abs(sig[u] - sig[v]) >= 2 for u, v in E):
                    continue
                if path_exists(n, adj, sig, sizes, par):
                    found = True; break
            if found:
                break
        if found:
            return b
    return 0

random.seed(7)
tested = 0
for n in range(2, 8):
    for _ in range(25 if n < 7 else 12):
        while True:                                  # random connected graph
            E = {(u, v) for u in range(n) for v in range(u + 1, n) if random.random() < random.choice((0.3, 0.5, 0.7))}
            adj = [set() for _ in range(n)]
            for u, v in E:
                adj[u].add(v); adj[v].add(u)
            seen, st = {0}, [0]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y); st.append(y)
            if len(seen) == n and E:
                break
        E = sorted(E)
        a, c = bw_brute(n, E), bw_buckets(n, E)
        assert a == c, (n, E, a, c)
        tested += 1
print(f"reduction and halving recursion agree with brute force on {tested} random connected graphs, n = 2..7")

# 2. locally valid pairs: per non-root vertex, given whether its parent is in S, exactly 5 of the 6 (offset, membership)
for b_par in (0, 1):
    ok = [(s, a) for s in (-1, 0, 1) for a in (0, 1) if not (b_par == 1 and s == 1 and a == 0) and not (b_par == 0 and s == -1 and a == 1)]
    assert len(ok) == 5
print("locally valid pairs per vertex: 5, so k * 2 * 5^(n-1) pairs in total")

# 3. exponent, exact: sqrt(10) * 2^x < 3.1623 with x = (1 + 2 eps) / 2^D, via 2^x <= 1 / (1 - x ln 2) and ln 2 < 0.6932
D, eps = 17, F(1, 10)
x = (1 + 2 * eps) / 2 ** D
LN2_UP = F(6932, 10000)
two_x_up = 1 / (1 - x * LN2_UP)
assert 10 * two_x_up ** 2 < F(31623, 10000) ** 2
print(f"exponent: sqrt(10) * 2^((1+2 eps)/2^D) < 3.1623 for D = {D}, eps = {eps}")
print("all checks passed")
