"""Decision version of Algorithm 4 of van Rooij and Bodlaender (Discrete Appl. Math. 2011; tech. report
UU-CS-2009-025) for Dominating Set, as a backtracking tree: each node either answers, or makes one tail call with a
new budget, or branches into the OR of two children (take S with budget k - 1, discard S with budget k).

A graph G becomes the set cover instance with the closed neighbourhoods N[v] as sets over the universe V.
The script compares the smallest budget accepted with brute force, and records the number of tree nodes."""
import itertools
import random
import networkx as nx

random.seed(11)


def freq(S, U):
    return {e: [i for i, s in S.items() if e in s] for e in U}


def take(S, U, i):
    T = S[i]
    return {j: s - T for j, s in S.items() if j != i}, U - T


def decide(S, U, k, cnt):
    """True iff the instance (S, U) has a set cover of at most k sets. S: dict id -> frozenset."""
    cnt[0] += 1
    if not U:
        return k >= 0
    if k <= 0:
        return False
    f = freq(S, U)
    if any(not f[e] for e in U):
        return False
    for e in U:                                        # Rule 1: an element of frequency one
        if len(f[e]) == 1:
            return decide(*take(S, U, f[e][0]), k - 1, cnt)
    ids = list(S)
    for i in ids:                                      # Rule 3: a set contained in another one (or empty)
        for j in ids:
            if i != j and S[i] <= S[j]:
                return decide({x: s for x, s in S.items() if x != i}, U, k, cnt)
    for a in U:                                        # Rule 5: subsumption, S(a) inside S(b): remove b
        for b in U:
            if a != b and set(f[a]) <= set(f[b]):
                return decide({x: s - {b} for x, s in S.items()}, U - {b}, k, cnt)
    for i in ids:                                      # Rule 6: counting rule, take R
        two = [e for e in S[i] if len(f[e]) == 2]
        other = set().union(*[S[j] for e in two for j in f[e]]) - S[i] if two else set()
        if len(other) < len(two):
            return decide(*take(S, U, i), k - 1, cnt)
    for i in ids:                                      # Rule 7: R = {e1, e2}, both of frequency two
        if len(S[i]) == 2 and all(len(f[e]) == 2 for e in S[i]):
            e1, e2 = sorted(S[i])
            r1 = next(j for j in f[e1] if j != i)
            r2 = next(j for j in f[e2] if j != i)
            if r1 == r2:                               # both other occurrences in one set: R is a subset of it
                continue
            q = (S[r1] | S[r2]) - S[i]
            T = {x: s for x, s in S.items() if x not in (i, r1, r2)}
            T[max(S) + 1] = frozenset(q)
            return decide(T, U - S[i], k - 1, cnt)
    m = max(len(s) for s in S.values())
    if m <= 2:                                         # Rule 4: maximum matching, polynomial time
        g = nx.Graph()
        g.add_nodes_from(U)
        g.add_edges_from(tuple(s) for s in S.values() if len(s) == 2)
        return len(U) - len(nx.max_weight_matching(g, maxcardinality=True)) <= k
    i = next(x for x in ids if len(S[x]) == m)        # branch on a set of maximum cardinality
    return decide(*take(S, U, i), k - 1, cnt) or decide({x: s for x, s in S.items() if x != i}, U, k, cnt)


def gamma(n, adj):
    for r in range(n + 1):
        for D in itertools.combinations(range(n), r):
            if set(D).union(*[adj[v] for v in D]) == set(range(n)):
                return r


if __name__ == "__main__":
    worst = {}
    for trial in range(400):
        n = random.randint(4, 15)
        p = random.choice([0.15, 0.25, 0.4])
        adj = {v: set() for v in range(n)}
        for a, b in itertools.combinations(range(n), 2):
            if random.random() < p:
                adj[a].add(b); adj[b].add(a)
        S = {v: frozenset(adj[v] | {v}) for v in range(n)}
        g, k, cnt = gamma(n, adj), 0, [0]
        while not decide(dict(S), frozenset(range(n)), k, cnt):
            k += 1
        assert k == g, (n, adj, k, g)
        worst[n] = max(worst.get(n, 0), cnt[0] / (k + 1))
    print("400 random graphs, n = 4..15: smallest accepted budget = domination number in every case")
    print("largest number of tree nodes per budget, by n:", {n: round(w) for n, w in sorted(worst.items())})
