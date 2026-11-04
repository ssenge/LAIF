"""Checks for README.md: the coset gadget and the degree claim of the lower bound over F2.

Run: python check_gadget.py

Tests, by assertion:
1. For a found gadget (U, W, a, b), every A and B built from f satisfy (AB)_ij = [f(i) = f(j)], so AB = C iff f is injective.
2. Every d - 1 coordinates of a coset are uniform and the same for all symbols. Some d coordinates reveal the coset.
3. For random T-query phase-oracle algorithms, the acceptance probability averaged over u, w, as a function of f, has
   degree at most 2T/d in the indicators y_ih. With N = 2, d = 3: no dependence on f for T = 1, no interaction between
   the two symbols for T = 2. For T = 3 the interaction is allowed, and the test checks it is nonzero.

Limits: small n, N = 2, d = 3, random algorithms. This tests the statement on small cases. It does not prove it.
"""
import itertools

import numpy as np

rng = np.random.default_rng(5)


def rref(M):
    M = M.copy() % 2
    piv, r = [], 0
    for c in range(M.shape[1]):
        p = [i for i in range(r, M.shape[0]) if M[i, c]]
        if not p:
            continue
        M[[r, p[0]]] = M[[p[0], r]]
        for i in range(M.shape[0]):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        piv.append(c)
        r += 1
        if r == M.shape[0]:
            break
    return M[:r], piv


def perp(M, n):
    R, piv = rref(M)
    out = []
    for f in [c for c in range(n) if c not in piv]:
        v = np.zeros(n, dtype=np.uint8)
        v[f] = 1
        for row, p in zip(R, piv):
            if row[f]:
                v[p] = 1
        out.append(v)
    return np.array(out, dtype=np.uint8)


def span(B):
    return (np.array(list(itertools.product([0, 1], repeat=B.shape[0])), dtype=np.uint8) @ B) % 2


def distance(B):
    w = span(B).sum(1)
    return int(w[w > 0].min())


def extend(base, S):
    cur, ext = base.copy(), []
    for v in S:
        t = np.vstack([cur, v])
        if len(rref(t)[0]) > len(cur):
            cur, ext = t, ext + [v]
    return np.array(ext, dtype=np.uint8)


def gadget(n, q, want):
    u = (n - q) // 2
    for _ in range(200000):
        U = rref(rng.integers(0, 2, (u, n), dtype=np.uint8))[0]
        if len(U) < u:
            continue
        D = perp(U, n)
        W = rref((rng.integers(0, 2, (u, D.shape[0]), dtype=np.uint8) @ D) % 2)[0]
        if len(W) < u:
            continue
        E = perp(W, n)
        if min(distance(D), distance(E)) < want:
            continue
        a, b = extend(U, E), extend(W, D)
        G = (a @ b.T) % 2
        R, p = rref(np.concatenate([G, np.eye(q, dtype=np.uint8)], 1))
        assert p[:q] == list(range(q))
        b = (R[:, q:].T @ b) % 2
        assert ((a @ b.T) % 2 == np.eye(q, dtype=np.uint8)).all()
        assert not ((U @ D.T) % 2).any() and not ((U @ W.T) % 2).any() and not ((a @ W.T) % 2).any()
        return U, W, D, E, a, b, min(distance(D), distance(E))
    raise RuntimeError("no gadget found")


def test_product(n, q, U, W, a, b):
    N = q
    C = np.zeros((n, n), dtype=np.uint8)
    C[:N, :N] = np.eye(N, dtype=np.uint8)
    SU, SW = span(U), span(W)
    for f in itertools.product(range(q), repeat=N):
        for _ in range(200):
            A = np.zeros((n, n), dtype=np.uint8)
            B = np.zeros((n, n), dtype=np.uint8)
            for i in range(N):
                A[i] = a[f[i]] ^ SU[rng.integers(len(SU))]
                B[:, i] = b[f[i]] ^ SW[rng.integers(len(SW))]
            P = (A @ B) % 2
            for i in range(N):
                for j in range(N):
                    assert P[i, j] == int(f[i] == f[j])
            assert (P == C).all() == (len(set(f)) == N)


def test_marginals(n, d, cosets):
    for P in itertools.combinations(range(n), d - 1):
        for S in cosets:
            v, c = np.unique(S[:, list(P)], axis=0, return_counts=True)
            assert len(v) == 2 ** (d - 1) and (c == c[0]).all()


def haar(k):
    z = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
    return np.linalg.qr(z)[0]


def averaged(f, T, us, n, q, SU, SW, a, b, Vs):
    """Exact average acceptance over all u_1, u_2, w_1, w_2, for N = 2."""
    rows = [SU ^ a[f[0]], SU ^ a[f[1]]]
    cols = [SW ^ b[f[0]], SW ^ b[f[1]]]
    k = len(SU)
    total, count = 0.0, 0
    for i0 in range(k):
        for i1 in range(k):
            r = np.concatenate([rows[0][i0], rows[1][i1]])
            grid = np.array(list(itertools.product(range(k), repeat=2)))
            bits = np.concatenate(
                [np.broadcast_to(r, (len(grid), 2 * n)), cols[0][grid[:, 0]], cols[1][grid[:, 1]]], 1
            )
            sign = (-1.0) ** bits
            sign = np.concatenate([sign, np.ones((len(grid), 1))], 1)
            s = np.broadcast_to(Vs[0][:, 0], sign.shape).astype(complex)
            for t in range(T):
                s = (s * sign) @ Vs[t + 1].T
            total += (np.abs(s[:, : s.shape[1] // 2]) ** 2).sum()
            count += len(grid)
    return total / count


def test_degree(n, q, U, W, a, b, d):
    SU, SW = span(U), span(W)
    dim = 4 * n + 1
    fs = [(0, 0), (0, 1), (1, 0), (1, 1)]
    for T, runs in [(1, 3), (2, 3), (3, 3)]:
        worst_dep, worst_int = 0.0, 0.0
        for _ in range(runs):
            Vs = [haar(dim) for _ in range(T + 1)]
            v = {f: averaged(f, T, None, n, q, SU, SW, a, b, Vs) for f in fs}
            worst_dep = max(worst_dep, max(v.values()) - min(v.values()))
            worst_int = max(worst_int, abs(v[(0, 0)] - v[(0, 1)] - v[(1, 0)] + v[(1, 1)]))
        print(f"T={T}: spread over f {worst_dep:.2e}, interaction {worst_int:.2e}", flush=True)
        if 2 * T < d:
            assert worst_dep < 1e-9
        if 2 * T < 2 * d:
            assert worst_int < 1e-9
        else:
            assert worst_int > 1e-9


if __name__ == "__main__":
    n, q = 10, 2
    U, W, D, E, a, b, d = gadget(n, q, 3)
    print(f"n={n}, q={q}, dim U={len(U)}, d={d}")
    assert d == 3
    test_product(n, q, U, W, a, b)
    print("product identity: ok")
    test_marginals(n, d, [span(U) ^ a[x] for x in range(q)] + [span(W) ^ b[y] for y in range(q)])
    print("marginals: ok")
    test_degree(n, q, U, W, a, b, d)
    print("degree claim: ok")
