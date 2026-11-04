"""Checks for Section 11 of RESULTS.md: simple graphs with cut answers mod 4.

Run: python check_mod4.py

Tests, by assertion:
1. A(U) is a simple graph, with the stated degrees and minimum degree, for all U at L = 2, 3 and random U at L = 4, 5.
2. cut_A(U)(x) = cut_A0(x) + 2 Y^T U Q over the integers, at random x.
3. For a random 1-query algorithm at L = 3, 4, the average of acc over the off-diagonal bits has Walsh weight 0 above
   2T in h. At phase 1/8 weight 3 is nonzero, so the argument does not extend to that phase.
4. The 4-query routine of Proposition 9 reads the degree exactly, on random graphs with n = 7.

Limits: small L, one query, and sampled query sets in test 3 (random unitaries on a sample of x and all z). Test 3 checks
the degree claim only, not the approximate degree of AND. Test 4 simulates the routine for one fixed vertex at a time,
not the minimum finding around it.
"""
import itertools

import numpy as np

rng = np.random.default_rng(7)


def graph(L, n, U):
    """Edge set of A(U) on n vertices, with v_l = l, a_l = L + l, c_l = 2L + l."""
    v, a, c = (lambda l: l), (lambda l: L + l), (lambda l: 2 * L + l)
    E = set()
    for p, q in itertools.combinations(range(n), 2):
        if (p < L) == (q < L):
            E.add((p, q))
    for l in range(L):
        for m in range(l, L):
            if not U[l, m]:
                continue
            plus = [(v(l), c(m)), (a(l), v(m))]
            minus = [(v(l), v(m)), (a(l), c(m))]
            for s, t in plus:
                pair = (min(s, t), max(s, t))
                assert pair not in E, "positive gadget entry on an existing edge"
                E.add(pair)
            for s, t in minus:
                if s == t:
                    continue
                pair = (min(s, t), max(s, t))
                assert pair in E, "negative gadget entry on a missing edge"
                E.remove(pair)
    return E


def cut(E, x):
    return sum(x[p] ^ x[q] for p, q in E)


def random_upper(L):
    return np.triu(rng.integers(0, 2, (L, L)))


def check_graph(L, n, U):
    E = graph(L, n, U)
    deg = np.zeros(n, dtype=int)
    for p, q in E:
        deg[p] += 1
        deg[q] += 1
    for l in range(L):
        assert deg[l] == L - 1 + 2 * U[l, l]
    assert all(deg[w] == n - L - 1 for w in range(L, n))
    want = L + 1 if all(U[l, l] for l in range(L)) else L - 1
    assert deg.min() == want
    E0 = graph(L, n, np.zeros((L, L), dtype=int))
    for _ in range(40):
        x = rng.integers(0, 2, n)
        Y = np.array([int(x[l]) - int(x[L + l]) for l in range(L)])
        Q = np.array([int(x[l]) - int(x[2 * L + l]) for l in range(L)])
        assert cut(E, x) == cut(E0, x) + 2 * Y @ U @ Q


def test_graph():
    for L, n in [(2, 6), (2, 8), (3, 9), (3, 11)]:
        cells = [(l, m) for l in range(L) for m in range(l, L)]
        for bits in itertools.product([0, 1], repeat=len(cells)):
            U = np.zeros((L, L), dtype=int)
            for (l, m), b in zip(cells, bits):
                U[l, m] = b
            check_graph(L, n, U)
    for L, n in [(4, 12), (5, 16)]:
        for _ in range(200):
            check_graph(L, n, random_upper(L))


def haar(d):
    z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    return np.linalg.qr(z)[0]


def walsh_by_weight(L, unit, zs, nx):
    """Largest Walsh coefficient of h -> E_a acc, by weight, for a random one-query algorithm."""
    n = 3 * L
    xs = rng.integers(0, 2, (nx, n))
    d = nx * len(zs)
    U0, U1 = haar(d), haar(d)
    s0 = U0[:, 0]
    off = [(l, m) for l in range(L) for m in range(l + 1, L)]
    H = list(itertools.product([0, 1], repeat=L))
    P = np.zeros(len(H))
    for i, h in enumerate(H):
        total = 0.0
        bit_vectors = list(itertools.product([0, 1], repeat=len(off)))
        for bits in bit_vectors:
            M = np.diag(h)
            for (l, m), b in zip(off, bits):
                M[l, m] = b
            E = graph(L, n, M)
            c = np.array([cut(E, x) for x in xs])
            phase = np.concatenate([np.exp(2j * np.pi * unit * z * c) for z in zs])
            s = U1 @ (phase * s0)
            total += (np.abs(s[: d // 2]) ** 2).sum()
        P[i] = total / len(bit_vectors)
    out = {}
    for S in H:
        co = sum(P[i] * (-1) ** np.dot(S, h) for i, h in enumerate(H)) / len(H)
        out[sum(S)] = max(out.get(sum(S), 0.0), abs(co))
    return out


def test_degree():
    for L, nx in [(3, 40), (4, 25)]:
        w = walsh_by_weight(L, 1 / 4, [0, 1, 2, 3], nx)
        assert max(v for k, v in w.items() if k > 2) < 1e-10, w
        print(f"L={L}, mod 4: largest Walsh coefficient above weight 2 is {max(v for k, v in w.items() if k > 2):.1e}")
    w = walsh_by_weight(4, 1 / 8, list(range(8)), 12)
    print(f"L=4, phase 1/8: largest Walsh coefficient above weight 2 is {max(v for k, v in w.items() if k > 2):.1e}")
    assert max(v for k, v in w.items() if k > 2) > 1e-6


def test_degree_routine():
    """Prepare i^{cut(S+u) - cut(S)} on S, apply Hadamards, and read N(u)."""
    n = 7
    for _ in range(30):
        E = {p for p in itertools.combinations(range(n), 2) if rng.integers(0, 2)}
        for u in range(n):
            others = [w for w in range(n) if w != u]
            amp = np.zeros(2 ** (n - 1), dtype=complex)
            for idx, bits in enumerate(itertools.product([0, 1], repeat=n - 1)):
                x = np.zeros(n, dtype=int)
                x[others] = bits
                xu = x.copy()
                xu[u] = 1
                amp[idx] = 1j ** (cut(E, xu) - cut(E, x))
            amp /= np.sqrt(len(amp))
            H1 = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
            H = np.array([[1.0]])
            for _q in range(n - 1):
                H = np.kron(H, H1)
            out = H @ amp
            k = int(np.argmax(np.abs(out)))
            assert abs(abs(out[k]) - 1) < 1e-9
            read = [int(b) for b in format(k, f"0{n - 1}b")]
            nbrs = [1 if (min(u, w), max(u, w)) in E else 0 for w in others]
            assert read == nbrs
            assert sum(read) == sum(nbrs)


if __name__ == "__main__":
    test_graph()
    print("graph, degrees, minimum degree and cut identity: ok")
    test_degree()
    test_degree_routine()
    print("degree routine: ok")
