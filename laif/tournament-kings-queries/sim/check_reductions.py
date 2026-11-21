"""Checks of the two reductions between 'every vertex of a tournament is a king' (KINGS) and
Orthogonal Vectors (OV: do two distinct rows of an n x n 0/1 matrix have disjoint supports?).

Upper reduction: a tournament T on N vertices fails KINGS iff the OV instance on 2N + 2 vectors
  U_x = (out(x), e_x, 1, 0), W_y = (not out(y), e_y, 0, 1), plus two all-ones vectors
has an orthogonal pair. Lower reduction: for X in {0,1}^{m x m}, m odd, the tournament T_X on 3m + 4
vertices (classes R, R', W with rotational tournaments inside, helpers a, b, c, d) satisfies KINGS
iff X has no orthogonal pair. Both are checked by asserts: exhaustively for m = 3 and small N,
and on random and structured inputs beyond that.
"""
import itertools
import random


def kings_all(A):
    """A[u][v] = 1 iff u -> v. True iff every vertex reaches every other within two steps."""
    n = len(A)
    out = [{v for v in range(n) if A[u][v]} for u in range(n)]
    for x in range(n):
        reach = set(out[x])
        for z in out[x]:
            reach |= out[z]
        reach.add(x)
        if len(reach) < n:
            return False
    return True


def has_cover(A):
    """True iff some x != y has out(x) subset of out(y) (x is covered by y)."""
    n = len(A)
    out = [frozenset(v for v in range(n) if A[u][v]) for u in range(n)]
    return any(x != y and out[x] <= out[y] for x in range(n) for y in range(n))


def ov(vecs):
    return any(not any(a & b for a, b in zip(vecs[i], vecs[j]))
               for i in range(len(vecs)) for j in range(i + 1, len(vecs)))


def ov_of_tournament(A):
    n = len(A)
    e = lambda i: [int(i == j) for j in range(n)]
    U = [list(A[x]) + e(x) + [1, 0] for x in range(n)]
    W = [[1 - A[y][z] for z in range(n)] + e(y) + [0, 1] for y in range(n)]
    ones = [1] * (2 * n + 2)
    vecs = U + W + [ones, ones]
    assert len(vecs) == 2 * n + 2 and all(len(v) == 2 * n + 2 for v in vecs)
    return vecs


def tournament_of_ov(X):
    m = len(X)
    assert m % 2 == 1 and m >= 3
    R = list(range(m)); Rp = list(range(m, 2 * m)); W = list(range(2 * m, 3 * m))
    a, b, c, d = 3 * m, 3 * m + 1, 3 * m + 2, 3 * m + 3
    N = 3 * m + 4
    A = [[0] * N for _ in range(N)]

    def arc(u, v):
        assert u != v and not A[u][v] and not A[v][u]
        A[u][v] = 1

    for cls in (R, Rp, W):                      # rotational tournament, diameter 2 for odd m >= 3
        for i in range(m):
            for s in range(1, (m - 1) // 2 + 1):
                arc(cls[i], cls[(i + s) % m])
    for i in range(m):
        for j in range(m):
            arc(Rp[j], R[i])
            if X[i][j]:
                arc(R[i], W[j])                  # r_i -> w_t iff X[i][t] = 1
            else:
                arc(W[j], R[i])
            if X[i][j]:
                arc(W[j], Rp[i])                 # w_t -> r'_i iff X[i][t] = 1
            else:
                arc(Rp[i], W[j])
    for v in R + Rp:
        arc(v, a); arc(b, v); arc(v, c); arc(d, v)
    for w in W:
        arc(a, w); arc(w, b); arc(w, c); arc(d, w)
    for u, v in ((a, b), (c, a), (c, b), (a, d), (b, d), (c, d)):
        arc(u, v)
    assert all(A[u][v] + A[v][u] == 1 for u in range(N) for v in range(N) if u != v)
    return A


def random_tournament(n, rng, p=0.5):
    A = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < p:
                A[u][v] = 1
            else:
                A[v][u] = 1
    return A


def main():
    rng = random.Random(1)
    # upper reduction and the covering characterization, all tournaments on up to 5 vertices
    cnt = 0
    for n in range(2, 6):
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        for bits in itertools.product((0, 1), repeat=len(pairs)):
            A = [[0] * n for _ in range(n)]
            for (u, v), bt in zip(pairs, bits):
                A[u][v], A[v][u] = bt, 1 - bt
            k = kings_all(A)
            assert k == (not has_cover(A))
            assert k == (not ov(ov_of_tournament(A)))
            cnt += 1
    for _ in range(300):
        n = rng.randint(6, 14)
        A = random_tournament(n, rng, rng.choice([0.5, 0.8, 0.95]))
        k = kings_all(A)
        assert k == (not has_cover(A)) == (not ov(ov_of_tournament(A)))
        cnt += 1
    print(f"upper reduction: {cnt} tournaments checked")
    # lower reduction: all 3 x 3 matrices, then random 5 x 5 and 7 x 7
    cnt = 0
    for bits in itertools.product((0, 1), repeat=9):
        X = [list(bits[3 * i:3 * i + 3]) for i in range(3)]
        assert kings_all(tournament_of_ov(X)) == (not ov(X))
        cnt += 1
    for m in (5, 7):
        for _ in range(400):
            p = rng.choice([0.2, 0.35, 0.5, 0.7])
            X = [[int(rng.random() < p) for _ in range(m)] for _ in range(m)]
            assert kings_all(tournament_of_ov(X)) == (not ov(X))
            cnt += 1
    print(f"lower reduction: {cnt} matrices checked")


if __name__ == "__main__":
    main()
