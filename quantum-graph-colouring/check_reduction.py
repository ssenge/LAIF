"""Classical check of the recursion behind the bounds (Algorithm 4 of Shimizu and Mori, with OR in place of Grover):
COL(G, k, u) is true if G splits into k independent sets of size at most u, false if G is not k-colourable.
Each call may enlarge the size limits it passes on, as bounds.py assumes; here they are enlarged at random.
Compared with brute force on random graphs."""
import itertools
import random

random.seed(3)


def colourable(V, E, k):
    V = list(V)
    return any(all(c[V.index(a)] != c[V.index(b)] for a, b in E if a in V and b in V)
               for c in itertools.product(range(k), repeat=len(V))) if V else True


def independent(S, E):
    return not any(a in S and b in S for a, b in E)


def maximal_independent_sets(V, E):
    V = sorted(V)
    for r in range(len(V) + 1):
        for I in itertools.combinations(V, r):
            I = set(I)
            if independent(I, E) and all(not independent(I | {v}, E) for v in V if v not in I):
                yield I


def col(V, E, k, u):
    V = frozenset(V)
    n = len(V)
    if n == 0:
        return True
    if k <= 3:
        return colourable(V, E, k)                      # base case: 3-colouring, 2-colouring
    if k <= 5:                                          # Reduction 1: a maximal independent set of size >= n/k
        return any(col(V - I, E, k - 1, n) for I in maximal_independent_sets(V, E) if len(I) * k >= n)
    kp = random.randint(2, k // 2)                      # Reduction 2: k' largest classes, the rest smaller
    for t in range(-(-n * kp // k), min(n, u * kp) + 1):
        for S in itertools.combinations(sorted(V), t):
            S = frozenset(S)
            u1 = min(t, u) + random.randint(0, 2)       # enlarged limits only weaken the promise
            u2 = min(n - t, t // kp) + random.randint(0, 2)
            if col(S, E, kp, u1) and col(V - S, E, k - kp, u2):
                return True
    return False


if __name__ == "__main__":
    trials = 0
    for _ in range(300):
        n, k = random.randint(4, 8), random.randint(3, 6)
        E = [e for e in itertools.combinations(range(n), 2) if random.random() < random.choice([0.4, 0.6, 0.8, 0.9])]
        truth = colourable(range(n), E, k)
        assert col(range(n), E, k, n) == truth, (n, k, E)
        trials += 1
    print(f"{trials} random graphs, n = 4..8, k = 3..6: COL agrees with brute force")
