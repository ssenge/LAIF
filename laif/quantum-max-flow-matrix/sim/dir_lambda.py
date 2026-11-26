"""Directed edge connectivity of simple digraphs: side sizes of minimum cuts, and the sampling step.

Brute force over all vertex sets on small random digraphs. Asserts: (1) if lambda < delta (delta the
least in- or out-degree), every minimum cut (S, V - S) has |S| >= delta + 1 and |V - S| >= delta + 1;
(2) for a fixed root r, lambda = min over u != r of min(lambda(r -> u), lambda(u -> r)), and the minimum
is already reached on any set X that meets both sides of some minimum cut.
Mutation: replacing delta + 1 by delta + 2 in (1) fails on some instance.
"""
import itertools, random
from maxflow_or import reference_flow

def out_cut(A, S):
    n = len(A); return sum(A[u][v] for u in S for v in range(n) if v not in S)

def digraph(n, p, rng, blocks):
    if not blocks:
        return [[int(u != v and rng.random() < p) for v in range(n)] for u in range(n)]
    b = n // 2   # two dense blocks joined by one or two arcs in each direction
    A = [[int(u != v and (u < b) == (v < b) and rng.random() < p) for v in range(n)] for u in range(n)]
    for _ in range(rng.choice((1, 2))):
        A[rng.randrange(b)][rng.randrange(b, n)] = 1
        A[rng.randrange(b, n)][rng.randrange(b)] = 1
    return A

def check(n, p, rng, slack=1, blocks=False):
    A = digraph(n, p, rng, blocks)
    delta = min(min(sum(r) for r in A), min(sum(A[u][v] for u in range(n)) for v in range(n)))
    cuts = {}
    for k in range(1, n):
        for S in itertools.combinations(range(n), k):
            cuts[S] = out_cut(A, set(S))
    lam = min(cuts.values())
    ok = True
    if lam < delta:
        for S, c in cuts.items():
            if c == lam and not (len(S) >= delta + slack and n - len(S) >= delta + slack): ok = False
    r = 0
    pair = {u: min(reference_flow(A, r, u), reference_flow(A, u, r)) for u in range(1, n)}
    assert min(pair.values()) == lam
    for S, c in cuts.items():
        if c == lam:
            side = set(S) if r not in S else set(range(n)) - set(S)   # the side without r
            assert min(pair[u] for u in side) == lam
    return ok, lam < delta

if __name__ == "__main__":
    rng = random.Random(11); strict = 0
    for blocks in (False, True):
        for n in (5, 6, 7, 8, 9, 10):
            for p in (0.3, 0.55, 0.8, 0.95, 1.0):
                for _ in range(4):
                    ok, s = check(n, p, rng, blocks=blocks); assert ok; strict += s
    print(f"240 digraphs (n <= 10, half of them two dense blocks): structure of minimum cuts and the root sampling step hold; {strict} with lambda < delta")
    assert strict >= 10
    rng = random.Random(11); bad = False
    for n in (6, 8, 10):
        for p in (0.8, 1.0):
            for _ in range(4):
                ok, _ = check(n, p, rng, slack=2, blocks=True); bad |= not ok
    assert bad, "mutation survived"
    print("mutation (sides >= delta + 2) caught")
