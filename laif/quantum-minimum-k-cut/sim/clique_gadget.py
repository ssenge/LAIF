"""Check of the hub gadget (README, Theorem 3) by brute force on small graphs, k = 3, 4, 5.
H has N vertices and nonnegative integer weights; Delta is its largest weighted degree and D = k*Delta + 1.
G adds one hub b with w(v, b) = D - deg_H(v). Asserted: the minimum k-cut of G equals (k-1) D - max over
(k-1)-sets S of w_H(S), the weight of the edges inside S; also with the clique shift w + M on edges,
the maximum is attained by a (k-1)-clique whenever H has one.
"""
import itertools, random

def min_kcut(n, w, k):
    best = None
    for lab in itertools.product(range(k), repeat=n):
        if len(set(lab)) < k:
            continue
        c = sum(w[u][v] for u in range(n) for v in range(u + 1, n) if lab[u] != lab[v])
        best = c if best is None else min(best, c)
    return best

def gadget(N, wH, k):
    deg = [sum(wH[v]) for v in range(N)]
    D = k * max(deg) + 1
    n = N + 1
    w = [[0] * n for _ in range(n)]
    for u in range(N):
        for v in range(N):
            w[u][v] = wH[u][v]
        w[u][N] = w[N][u] = D - deg[u]
    return n, w, D

random.seed(1)
cases = 0
for trial in range(300):
    N = random.randint(3, 6)
    k = random.choice([3, 4, 5])
    if k - 1 > N or (k == 5 and N > 5):
        N = min(N, 5)
    if k - 1 > N:
        continue
    p = random.random()
    wH = [[0] * N for _ in range(N)]
    for u in range(N):
        for v in range(u + 1, N):
            if random.random() < p:
                wH[u][v] = wH[v][u] = random.randint(1, 5)
    n, w, D = gadget(N, wH, k)
    sets = list(itertools.combinations(range(N), k - 1))
    inside = lambda S, ww: sum(ww[u][v] for u, v in itertools.combinations(S, 2))
    assert min_kcut(n, w, k) == (k - 1) * D - max(inside(S, wH) for S in sets), (N, k, wH)
    # clique shift: M larger than any (k-1)-set weight
    M = 1 + sum(map(sum, wH))
    wS = [[wH[u][v] + M if wH[u][v] > 0 else 0 for v in range(N)] for u in range(N)]
    cliques = [S for S in sets if all(wH[u][v] > 0 for u, v in itertools.combinations(S, 2))]
    if cliques:
        top = max(inside(S, wS) for S in sets)
        assert top == max(inside(S, wS) for S in cliques)
        assert top - (k - 1) * (k - 2) // 2 * M == max(inside(S, wH) for S in cliques)
    cases += 1
print(f"{cases} cases passed")
