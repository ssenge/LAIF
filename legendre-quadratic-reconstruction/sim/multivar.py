"""Exact state-vector simulation of the algorithm for f(x) = (x + s)^T A (x + s) - D over F_p^n (Theorem 3).

Even n. One run: query chi(f(x)) on the uniform superposition, keep the outcome "nonzero" and apply the phase,
apply the Fourier transform over F_p^n, write the outcome k != 0 as lambda k0 with k0 normalized (first nonzero
coordinate 1), measure k0, apply the Fourier transform over F_p to the lambda register and measure w. The
outcome satisfies (w + k0.s)^2 = k0^T B k0 with B = D A^{-1}, i.e. the equation
    w^2 + 2 w (k0 . s) + k0^T M k0 = 0,   M = s s^T - B,
which is linear in (s, M). Enough runs determine s and B; one classical query at x = -s gives chi(D), and
f is recovered up to a square factor as c ((x + s)^T B^{-1} (x + s) - 1) with chi(c) = chi(D).

Odd n >= 3. Restrictions of f to affine hyperplanes are quadratics in n - 1 (even) variables. Two pairs of
parallel hyperplanes give two lines through the centre -s; hyperplanes through -s give the Gram matrices of
B^{-1} on their directions.

The simulation computes each measurement distribution exactly from the state vector, which is built from the
oracle table alone; the recovery uses only the measured (k0, w) and oracle values."""
import sys
import numpy as np

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 7)


def chi_tab(p):
    c = np.full(p, -1, dtype=np.int64)
    c[(np.arange(1, p) ** 2) % p] = 1
    c[0] = 0
    return c


def solve_mod(rows, rhs, p):
    """Solution of rows x = rhs over F_p if unique, else None."""
    A = np.concatenate([np.array(rows, dtype=np.int64) % p, np.array(rhs, dtype=np.int64)[:, None] % p], 1)
    m, n = len(rows), A.shape[1] - 1
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i, c]), None)
        if piv is None:
            return None
        A[[r, piv]] = A[[piv, r]]
        A[r] = A[r] * pow(int(A[r, c]), -1, p) % p
        for i in range(m):
            if i != r and A[i, c]:
                A[i] = (A[i] - A[i, c] * A[r]) % p
        r += 1
    assert not A[r:, n].any(), "inconsistent equations"
    return A[:n, n]


def inv_mod(M, p):
    n = len(M)
    return np.array([solve_mod(M, np.eye(n, dtype=np.int64)[:, j], p) for j in range(n)]).T


def one_run(table, n, p):
    """One run on the oracle table chi(f(x)), x in F_p^n (shape (p,)*n). Returns (k0, w) or None."""
    amp = table.astype(complex)
    amp /= np.linalg.norm(amp)                         # outcome "nonzero" kept
    phi = np.fft.ifftn(amp) * np.sqrt(p ** n)          # unitary Fourier transform, kernel e(k.x/p)
    prob = np.abs(phi.reshape(-1)) ** 2
    k = np.array(np.unravel_index(rng.choice(p ** n, p=prob / prob.sum()), (p,) * n))
    if not k.any():
        return None
    lam = int(k[np.flatnonzero(k)[0]])
    k0 = k * pow(lam, -1, p) % p
    v = np.array([phi[tuple(l * k0 % p)] if l else 0 for l in range(p)])   # lambda register given k0
    pw = np.abs(np.fft.fft(v)) ** 2                    # Fourier transform over F_p, kernel e(-lambda w/p)
    return k0, int(rng.choice(p, p=pw / pw.sum()))


def recover_even(oracle, n, p, max_runs=None):
    """oracle: integer grid (N, n) -> chi values. Returns (s, B, chi(D), runs) for f = (x+s)^T A (x+s) - D,
    or None after max_runs runs (a restriction with singular quadratic part or D = 0 never verifies)."""
    grid = np.indices((p,) * n).reshape(n, -1).T
    table = oracle(grid).reshape((p,) * n)
    iu = np.triu_indices(n)
    rows, rhs, runs = [], [], 0
    while max_runs is None or runs < max_runs:
        runs += 1
        out = one_run(table, n, p)
        if out is None:
            continue
        k0, w = out
        quad = np.outer(k0, k0) * (2 - np.eye(n, dtype=np.int64))
        rows.append(list(2 * w * k0 % p) + list(quad[iu] % p))
        rhs.append(-w * w % p)
        if len(rows) < len(iu[0]) + n:
            continue
        try:
            sol = solve_mod(rows, rhs, p)
        except AssertionError:                         # a sample with a wrong w (probability <= 2/p)
            rows, rhs = [], []
            continue
        if sol is None:
            continue
        s = sol[:n]
        M = np.zeros((n, n), dtype=np.int64)
        M[iu] = sol[n:]
        M = (M + M.T - np.diag(np.diag(M))) % p
        B = (np.outer(s, s) - M) % p
        chiD = int(oracle(-s[None, :] % p)[0]) * int(chi_tab(p)[p - 1])  # chi(f(-s)) = chi(-D)
        if chiD and verify(oracle, s, B, chiD, n, p):
            return s, B, chiD, runs
        rows, rhs = [], []                             # wrong candidate: start again with fresh runs


def verify(oracle, s, B, chiD, n, p, m=40):
    """Classical check of a candidate at m random points."""
    if solve_mod(B, np.zeros(n, dtype=np.int64), p) is None:
        return False
    chi = chi_tab(p)
    x = rng.integers(0, p, (m, n))
    y = (x + s) % p
    return np.array_equal(chiD * chi[(np.einsum('ki,ij,kj->k', y, inv_mod(B, p), y) - 1) % p], oracle(x))


def recover(oracle, n, p):
    """Returns (s, B^{-1} = A/D, chi(D), runs)."""
    if n % 2 == 0:
        s, B, chiD, runs = recover_even(oracle, n, p)
        return s, inv_mod(B, p), chiD, runs

    def restricted(x0, P):
        return lambda y: oracle((x0 + y @ P.T) % p)

    cap = 40 * (n - 1) * (n + 2)                       # far above the typical number of runs
    runs, lines = 0, []
    while len(lines) < 2:                              # two lines through -s from parallel hyperplanes
        P = rng.integers(0, p, (n, n - 1))
        x0, x1 = rng.integers(0, p, n), rng.integers(0, p, n)
        r0 = recover_even(restricted(x0, P), n - 1, p, cap)
        r1 = recover_even(restricted(x1, P), n - 1, p, cap)
        runs += 2 * cap if r0 is None or r1 is None else r0[3] + r1[3]
        if r0 is None or r1 is None:
            continue
        c0, c1 = (x0 - P @ r0[0]) % p, (x1 - P @ r1[0]) % p   # centres: the restrictions are centred at y = -s1
        if (c0 - c1).any():
            lines.append((c0, (c1 - c0) % p))
    (a, u), (b, v) = lines
    ab = solve_mod(np.stack([u, -v % p], 1), (b - a) % p, p)
    s = (-(a + ab[0] * u)) % p
    iu = np.triu_indices(n)
    rows, rhs = [], []
    while True:                                        # Gram matrices of C = B^{-1} on hyperplanes through -s
        P = rng.integers(0, p, (n, n - 1))
        res = recover_even(restricted(-s % p, P), n - 1, p, cap)
        runs += cap if res is None else res[3]
        if res is None:
            continue
        C1 = inv_mod(res[1], p)                            # = P^T C P
        for i in range(n - 1):
            for j in range(i, n - 1):
                # (P^T C P)_ij = sum_{a <= b} C_ab (P_ai P_bj + P_bi P_aj), halved on the diagonal a = b
                sym = (np.outer(P[:, i], P[:, j]) + np.outer(P[:, j], P[:, i])) % p
                sym[np.diag_indices(n)] = sym[np.diag_indices(n)] * pow(2, -1, p) % p
                rows.append(list(sym[iu]))
                rhs.append(int(C1[i, j]))
        if len(rows) >= len(iu[0]):
            sol = solve_mod(rows, rhs, p)
            if sol is not None:
                break
    C = np.zeros((n, n), dtype=np.int64)
    C[iu] = sol
    C = (C + C.T - np.diag(np.diag(C))) % p
    chiD = int(oracle(-s[None, :] % p)[0]) * int(chi_tab(p)[p - 1])
    return s, C, chiD, runs


def trial(p, n):
    chi = chi_tab(p)
    while True:
        A = rng.integers(0, p, (n, n))
        A = (A + A.T) % p
        if solve_mod(A, np.zeros(n, dtype=np.int64), p) is not None:
            break
    s, D = rng.integers(0, p, n), int(rng.integers(1, p))

    def oracle(x):
        y = (x + s) % p
        return chi[(np.einsum('ki,ij,kj->k', y, A, y) - D) % p]
    s_hat, C, chiD, runs = recover(oracle, n, p)
    c = next(c for c in range(1, p) if chi[c] == chiD)
    grid = np.indices((p,) * n).reshape(n, -1).T
    y = (grid + s_hat) % p
    ok = np.array_equal(chi[c * (np.einsum('ki,ij,kj->k', y, C, y) - 1) % p], oracle(grid))
    return ok, runs


if __name__ == "__main__":
    print("n, p, trials, all recovered (chi(f_hat) = chi(f) at every point), runs of the quantum routine per trial")
    for n, p, t in [(2, 101, 20), (2, 211, 10), (4, 17, 5), (4, 31, 3), (3, 31, 5), (3, 61, 3), (5, 13, 2)]:
        res = [trial(p, n) for _ in range(t)]
        assert all(ok for ok, _ in res)
        print(f"n = {n}, p = {p:3d}, {t:2d} trials, all recovered, runs {sorted(r for _, r in res)}")
