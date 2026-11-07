"""Classical check of the recursion behind the bounds (the reductions of Theorem 9 of arXiv:1907.00529, with OR in
place of quantum search): COL(G, k, u) is true if G splits into k independent sets of size at most u, false if G is
not k-colourable. For every k >= 4 either reduction is chosen at random, or Reduction 2 always, so that its
sub-calls get binding size limits. Each call may enlarge the limits it passes on, as bounds.py assumes;
here they are kept tight or enlarged at random. Compared with brute force on random graphs. The base case respects the
limit strictly, so a control run with the limit for G - S lowered by one must fail, which shows that the limits
are tested."""
import itertools
import random


def colourable(V, E, k, u=None):
    """Brute force by backtracking: a split into k independent sets of size at most u (any size if u is None)."""
    V = sorted(V)
    adj = {v: {b for a, b in E if a == v} | {a for a, b in E if b == v} for v in V}
    c = {}

    def go(i):
        if i == len(V):
            return True
        for x in range(k):
            if all(c.get(w) != x for w in adj[V[i]]) and (u is None or sum(y == x for y in c.values()) < u):
                c[V[i]] = x
                if go(i + 1):
                    return True
                del c[V[i]]
        return False
    return go(0)


def independent(S, E):
    return not any(a in S and b in S for a, b in E)


def maximal_independent_sets(V, E):
    V = sorted(V)
    for r in range(len(V) + 1):
        for I in itertools.combinations(V, r):
            I = set(I)
            if independent(I, E) and all(not independent(I | {v}, E) for v in V if v not in I):
                yield I


def col(V, E, k, u, broken=False, p1=0.5):
    V = frozenset(V)
    n = len(V)
    if n == 0:
        return True
    if k <= 3:
        return colourable(V, E, k, u)                   # base case, strict: the limit u is respected
    if random.random() < p1:                           # Reduction 1: a maximal independent set of size >= n/k
        return any(col(V - I, E, k - 1, n, broken, p1) for I in maximal_independent_sets(V, E) if len(I) * k >= n)
    kp = random.randint(2, k // 2)                      # Reduction 2: k' largest classes, the rest smaller
    for t in range(-(-n * kp // k), min(n, u * kp) + 1):
        for S in itertools.combinations(sorted(V), t):
            S = frozenset(S)
            u1 = min(t, u) + (0 if broken else random.randint(0, 1))   # enlarged limits weaken the promise
            u2 = min(n - t, t // kp) + (-1 if broken else random.randint(0, 1))
            if col(S, E, kp, u1, broken, p1) and col(V - S, E, k - kp, u2, broken, p1):
                return True
    return False


def run(trials, broken, p1, seed):
    random.seed(seed)
    wrong = 0
    for _ in range(trials):
        n, k = random.randint(5, 9), random.randint(3, 8)
        E = [e for e in itertools.combinations(range(n), 2) if random.random() < random.choice([0.5, 0.7, 0.85, 0.95])]
        wrong += col(range(n), E, k, n, broken, p1) != colourable(range(n), E, k)
    return wrong


if __name__ == "__main__":
    for p1, name in [(0.5, "either reduction at random"), (0.0, "Reduction 2 only")]:
        assert run(300, False, p1, 3) == 0
        print(f"300 random graphs, n = 5..9, k = 3..8, {name}: COL agrees with brute force")
    w = run(300, True, 0.0, 3)
    assert w > 0
    print(f"control, Reduction 2 only, limit for G - S lowered by one: {w} of 300 answers wrong, as expected")
