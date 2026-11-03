"""Numerical checks for the integer-weight lower bound in ../RESULTS.md. Exact integer arithmetic mod N.

check_basis:    b_uv is a Z-basis of ker(deg), and F = C beta + eps with eps_uv = <b_uv, F>.
check_expansion: P(h) = sum_u phi(u) K_u(h) with |K_u| <= 1, for a random algorithm, by brute force over a.
check_support:  every pair (p, p') in a class u has |Y(F_p - F_p' - F_u)| within the sparsity bound.
check_sparsity: exact solutions over Z_N, N composite or a power of 2. Also searches for r > rank.
check_kernel:   the exact instance in kernel_instance.json with nonzero kernel K, so r > rank.
check_near:     dyadic approximations of Z_q solutions: near-zero labels, non-tiny D_v, count within the bound.

Limits: the sizes are small, the degree bounds of Section 4 are not tight here, random search rarely leaves K = 0,
and near-solutions are rounded exact solutions, so tau is never stressed.
"""
import itertools
import json
import math
import os
from fractions import Fraction

import numpy as np


def pairs(n):
    return list(itertools.combinations(range(n), 2))


def setup(n):
    E = pairs(n)
    idx = {e: i for i, e in enumerate(E)}
    e = lambda u, v: idx[(min(u, v), max(u, v))]
    basis, keys = [], []
    for u, v in E:
        if u == 0 or (u, v) == (1, 2):
            continue
        b = np.zeros(len(E), dtype=np.int64)
        for f, c in ((e(u, v), 1), (e(0, u), -1), (e(0, v), -1), (e(0, 1), 1), (e(0, 2), 1), (e(1, 2), -1)):
            b[f] += c
        basis.append(b)
        keys.append(e(u, v))
    Bv = []
    for v in range(n):
        a, c = [w for w in range(n) if w != v][:2]
        b = np.zeros(len(E), dtype=np.int64)
        b[e(v, a)] += 1
        b[e(v, c)] += 1
        b[e(a, c)] -= 1
        Bv.append(b)
    return E, np.array(basis), np.array(keys), np.array(Bv)


def deg(n, E, A):
    d = np.zeros(n, dtype=np.int64)
    for (u, v), a in zip(E, A):
        d[u] += a
        d[v] += a
    return d


def delta(x, E):
    return np.array([x[u] ^ x[v] for u, v in E], dtype=np.int64)


def check_basis(n, rng):
    E, b, keys, Bv = setup(n)
    assert all((deg(n, E, row) == 0).all() for row in b)
    assert len(b) == len(E) - n
    for v in range(n):
        d = deg(n, E, Bv[v])
        assert d[v] == 2 and (np.delete(d, v) == 0).all()
    assert (b[:, keys] == np.eye(len(b), dtype=np.int64)).all()  # unit triangular, hence a Z-basis
    # F = C beta + eps over Z_{2N}: eps_uv = <b_uv, F>, on all other edges 0, and <B_v, C beta> = 2 beta_v
    N = 2 ** 10
    idx = {e: i for i, e in enumerate(E)}
    e = lambda u, v: idx[(min(u, v), max(u, v))]
    for _ in range(50):
        F = rng.integers(0, N, len(E))
        F2 = 2 * F  # work in units of 1/(2N) so that beta_0 exists
        beta = np.zeros(n, dtype=np.int64)
        beta[0] = (F[e(0, 1)] + F[e(0, 2)] - F[e(1, 2)])
        for v in range(1, n):
            beta[v] = F2[e(0, v)] - beta[0]
        eps = (F2 - np.array([beta[u] + beta[v] for u, v in E])) % (2 * N)
        expect = np.zeros(len(E), dtype=np.int64)
        expect[keys] = 2 * (b @ F)
        assert ((eps - expect) % (2 * N) == 0).all()
        for v in range(n):
            lhs = 2 * (Bv[v] @ F)
            rhs = 2 * beta[v] + Bv[v] @ eps
            assert (lhs - rhs) % (2 * N) == 0


def phi_table(N, b):
    """Triangle phi(z/N) with half-width b+1 grid points: phi(z) = max(0, 1 - |z|/(b+1))."""
    t = np.zeros(N)
    for z in range(N):
        dist = min(z, N - z)
        t[z] = max(0.0, 1 - dist / (b + 1))
    return t


def haar(dim, rng):
    q, _ = np.linalg.qr(rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim)))
    return q


def check_expansion(n, N, b, T, G, rng):
    """Brute force E_a over the periodized Fejer pmf on Z_N^J against the sum over u."""
    E, basis, keys, Bv = setup(n)
    J = len(basis)
    phi = phi_table(N, b)
    pmf = np.real(np.fft.fft(phi)) / N  # pmf(a) = (1/N) sum_z phi(z/N) e^{-2 pi i a z / N}
    assert pmf.min() > -1e-12 and abs(pmf.sum() - 1) < 1e-12
    xs = rng.choice(2 ** n, 4, replace=False)
    sets = [np.array([(int(i) >> k) & 1 for k in range(n)]) for i in xs]
    B = [(s, z) for s in range(4) for z in range(N)]
    dim = len(B)
    Us = [haar(dim, rng) for _ in range(T + 1)]
    cuts = np.array([delta(sets[s], E) for s, _ in B])
    zs = np.array([z for _, z in B])
    A0 = rng.integers(0, N, len(E))
    psi0 = np.zeros(dim, dtype=complex)
    psi0[0] = 1
    worst = 0.0
    for h in rng.integers(0, 2, (4, n)):
        Ah = A0 + G * (h @ Bv)
        direct = 0.0
        for a in itertools.product(range(N), repeat=J):
            w = np.prod(pmf[list(a)])
            if w < 1e-15:
                continue
            A = Ah + np.array(a) @ basis
            ph = np.exp(2j * np.pi * ((zs * (cuts @ A)) % N) / N)
            psi = Us[0] @ psi0
            for s in range(T):
                psi = Us[s + 1] @ (ph * psi)
            direct += w * abs(psi[0]) ** 2
        # label model: state on (basis index, theta in Z_N^J), start theta = 0
        ph = np.exp(2j * np.pi * ((zs * (cuts @ Ah)) % N) / N)
        shift = (zs[:, None] * (cuts @ basis.T)) % N
        state = {(0,) * J: Us[0] @ psi0}
        for s in range(T):
            new = {}
            for th, vec in state.items():
                for i in range(dim):
                    if abs(vec[i]) < 1e-15:
                        continue
                    k = tuple((np.array(th) + shift[i]) % N)
                    new.setdefault(k, np.zeros(dim, dtype=complex))[i] += ph[i] * vec[i]
            state = {k: Us[s + 1] @ v for k, v in new.items()}
        assert abs(sum(np.linalg.norm(v) ** 2 for v in state.values()) - 1) < 1e-9
        Ku = {}
        keys_th = list(state)
        for t1 in keys_th:
            for t2 in keys_th:
                u = tuple((np.array(t1) - np.array(t2)) % N)
                if all(phi[z] > 0 for z in u):
                    Ku[u] = Ku.get(u, 0) + state[t1][0] * np.conj(state[t2][0])
        assert max(abs(v) for v in Ku.values()) <= 1 + 1e-9
        via_u = sum(np.prod(phi[list(u)]) * v for u, v in Ku.items())
        worst = max(worst, abs(via_u - direct))
    assert worst < 1e-9, worst
    return worst


def check_support(n, N, T, sets, zvals, rng, bound):
    """All pairs of T-query paths: within a class u, the difference from the reference has |Y| <= bound."""
    E, basis, keys, Bv = setup(n)
    d = [delta(np.array(s), E) for s in sets]
    steps = [(i, z) for i in range(len(sets)) for z in zvals]
    paths = np.array([sum(z * d[i] for i, z in c) for c in itertools.product(steps, repeat=T)]) % N
    paths = np.unique(paths, axis=0)
    th = (paths @ basis.T) % N
    D = (paths @ Bv.T) % N
    classes = {}
    worst, count = 0, 0
    for i in range(len(paths)):
        diff = (th[i] - th) % N
        codes = [tuple(row) for row in diff]
        for j, code in enumerate(codes):
            if code in classes:
                ref = classes[code]
                y = int(np.count_nonzero((D[i] - D[j] - ref) % N))
                worst = max(worst, y)
                count += 1
                assert y <= bound, (y, bound)
            else:
                classes[code] = (D[i] - D[j]) % N
    return worst, count, len(classes)


def solve_all(n, N, X):
    """All t in Z_N^R with exactly zero labels, returned with the diag D_v = <B_v, F>."""
    E, basis, keys, Bv = setup(n)
    d = np.array([delta(x, E) for x in X])
    R = len(X)
    grid = np.array(list(itertools.product(range(N), repeat=R)), dtype=np.int64)
    F = grid @ d
    ok = ((F @ basis.T) % N == 0).all(axis=1)
    return grid[ok], (F[ok] @ Bv.T) % N


def rank_q(M):
    return np.linalg.matrix_rank(M.astype(float))


def yhat(X, v0, ys):
    return np.array([list(X[:, v] - X[:, v0]) + [1] for v in ys]).T


def check_sparsity(n, N, R, trials, rng):
    """Bound r' <= rho (1 + log r' / (2 log 2)) for exact solutions, and record the excess r' - rho."""
    best = (0, None)
    for _ in range(trials):
        X = rng.integers(0, 2, (R, n))
        ts, Ds = solve_all(n, N, X)
        for t, D in zip(ts, Ds):
            Y = np.nonzero(D)[0]
            if len(Y) == 0:
                continue
            v0 = 0
            ys = [v for v in Y if v != v0]
            if not ys:
                continue
            rho = rank_q(yhat(X, v0, ys))
            r = len(ys)
            assert r <= rho * (1 + math.log(max(r, 2)) / (2 * math.log(2))) + 1e-9, (r, rho)
            if N & (N - 1) == 0:
                assert r <= rho, (r, rho, N)
            if r - rho > best[0]:
                best = (r - rho, (X.copy(), t.copy(), r, rho))
    return best


def check_kernel(path):
    """Exact instance with K != 0: labels vanish, r = 12 > rank 11, and lambda_u D_u = 0 for the kernel vector."""
    data = json.load(open(path))
    X, t = data["X"], [Fraction(a, b) for a, b in data["t"]]
    n = len(X[0])
    sep = lambda u, v: sum(s for s, x in zip(t, X) if x[u] != x[v]) % 1
    for u, v in pairs(n):
        if u != 0 and (u, v) != (1, 2):
            assert (sep(u, v) - sep(0, u) - sep(0, v) + sep(0, 1) + sep(0, 2) - sep(1, 2)) % 1 == 0
    D = []
    for v in range(n):
        a, c = [w for w in range(n) if w != v][:2]
        D.append((sep(v, a) + sep(v, c) - sep(a, c)) % 1)
    Y = [v for v in range(1, n) if D[v] != 0]
    Yh = np.array([[x[v] - x[0] for x in X] + [1] for v in Y]).T
    lam = np.array([3, 3, 3, -3, -3, -3, 2, 2, 2, -2, -2, -2])
    assert len(Y) == 12 and rank_q(Yh) == 11 and (Yh @ lam == 0).all()
    assert all((int(l) * D[v]) % 1 == 0 for l, v in zip(lam, Y))
    G = math.lcm(*range(1, n + 1))
    assert all((G * x) % 1 == 0 for x in D)  # G removes every denominator here
    return len(Y), rank_q(Yh)


def check_near(n, q, k, R, trials, rng):
    """t = a/q rounded to Z_{2^k}: u is tiny, D_v is near a multiple of 1/q; the count obeys the bound."""
    E, basis, keys, Bv = setup(n)
    N = 2 ** k
    G = math.lcm(*range(1, n + 1))
    seen, worst = 0, 0
    for _ in range(trials):
        X = rng.integers(0, 2, (R, n))
        ts, Ds = solve_all(n, q, X)
        d = np.array([delta(x, E) for x in X])
        for t in ts[:200]:
            z = [int(round(int(a) * N / q)) for a in t]
            F = np.array([sum(zz * int(c) for zz, c in zip(z, col)) % N for col in d.T], dtype=object)
            th = [int(sum(int(c) * int(f) for c, f in zip(row, F))) % N for row in basis]
            D = [int(sum(int(c) * int(f) for c, f in zip(row, F))) % N for row in Bv]
            small = max(min(u, N - u) for u in th)
            assert small <= 12 * R  # rounding error only
            big = [v for v in range(n) if min(D[v], N - D[v]) > 100 * R]
            Gbig = [v for v in range(n) if min(G * D[v] % N, N - G * D[v] % N) > G * 100 * R]
            worst = max(worst, len(big))
            seen += bool(big)
            assert len(big) <= 1.5 * (R + 1) * (1 + math.log(max(n, 2)) / (2 * math.log(2))) + 1
            assert len(Gbig) == 0 or q > n  # G kills every denominator q <= n
    return seen, worst


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for n in (5, 6, 9, 13):
        check_basis(n, rng)
    print("basis and F = C beta + eps: ok", flush=True)
    for n, N, b, T, G in ((4, 16, 2, 2, 1), (4, 16, 3, 3, 2), (5, 8, 1, 1, 2), (5, 6, 1, 1, 6), (5, 8, 2, 2, 1)):
        err = check_expansion(n, N, b, T, G, rng)
        print(f"expansion n={n} N={N} b={b} T={T} G={G}: max |direct - sum_u| = {err:.1e}", flush=True)
    block = lambda n, I: [1 if i in I else 0 for i in range(n)]
    sing = lambda n: [block(n, {i}) for i in range(n)]
    tri = lambda n: [block(n, {0, 1, 2}), block(n, {0, 1, 3}), block(n, {0, 2, 3}), block(n, {1, 2, 3})]
    w, c, cl = check_support(10, 4, 1, sing(10) + tri(10), (1, 2, 3), rng, 6)
    print(f"support n=10 N=4 T=1: {c} pairs in {cl} classes, max |Y| = {w}, bound (4 terms + 2) = 6", flush=True)
    shift = lambda n, sets, k: [list(np.roll(s, k)) for s in sets]
    spread = sing(14)[:2] + tri(14) + shift(14, tri(14), 4) + shift(14, tri(14), 8)
    w, c, cl = check_support(14, 4, 2, spread, (1, 2), rng, 10)
    print(f"support n=14 N=4 T=2: {c} pairs in {cl} classes, max |Y| = {w}, bound (8 terms + 2) = 10", flush=True)
    r, rho = check_kernel(os.path.join(os.path.dirname(os.path.abspath(__file__)), "kernel_instance.json"))
    print(f"kernel instance: r = {r}, rank = {rho}, kernel vector checked", flush=True)
    for n, N, R, trials in ((7, 4, 4, 1500), (7, 8, 3, 1500), (7, 6, 4, 1500), (8, 6, 5, 200), (7, 12, 3, 1500), (7, 30, 3, 400)):
        ex = check_sparsity(n, N, R, trials, rng)
        print(f"sparsity n={n} N={N} R={R}: max excess r' - rho = {ex[0]}", flush=True)
    for n, q, k, R, trials in ((8, 3, 40, 3, 300), (8, 5, 40, 3, 200), (9, 6, 40, 4, 40)):
        seen, worst = check_near(n, q, k, R, trials, rng)
        print(f"near n={n} q={q} R={R}: {seen} near solutions with non-tiny D, max count = {worst}", flush=True)
    print("all checks passed")
