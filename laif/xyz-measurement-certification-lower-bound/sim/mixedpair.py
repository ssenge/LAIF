"""Checks for the mixed pair s0 = (1 - lam) I/d + lam |cat><cat|, s1 = (1 - lam) I/d + lam |anticat><anticat|,
cat = (a^n + abar^n)/sqrt2, anticat = (a^n - abar^n)/sqrt2, a with Bloch vector (1,1,1)/sqrt3.

Asserts, for every X/Y/Z product setting (up to permutation, by outcome types) and n = 1..14:
  (1) |<e|a><abar|e>| = 6^(-1/2) for every axis and outcome;
  (2) H^2(P_b(s0), P_b(s1)) <= lam^2 (2/3)^n / (1 - lam);
and at n = 4, by brute force on state vectors:
  (3) the same bound for random qubit-by-qubit adaptive measurement trees (axis of each qubit, and the order of
      the qubits, chosen from earlier outcomes of the same copy);
  (4) fidelity gap <cat|s0|cat> - <cat|s1|cat> = lam.
Prints max_b H^2 / (lam^2 (2/3)^n) and the implied copy bound.
  (5) the exact optimum over all adaptive one-copy trees (dynamic programming), n <= 14, below the bound of (2);
  (6) stored copies: for random fully adaptive trees on all nT qubits, |c|/b <= rho per copy and leaf, and
      affinity >= (1 - rho^2)^(T/2), rho = lam (2/3)^(n/2)/(1 - lam).
"""
import itertools, numpy as np
from math import comb

s3 = 1 / np.sqrt(3); th = np.arccos(s3)
a = np.array([np.cos(th / 2), np.exp(1j * np.pi / 4) * np.sin(th / 2)])
ab = np.array([-a[1].conj(), a[0].conj()])
AX = {'X': np.array([[1, 1], [1, -1]]) / np.sqrt(2), 'Y': np.array([[1, 1], [1j, -1j]]) / np.sqrt(2), 'Z': np.eye(2)}
amp = {(c, x): (AX[c][:, x].conj() @ a, AX[c][:, x].conj() @ ab) for c in 'XYZ' for x in (0, 1)}
for (c, x), (u, v) in amp.items():
    assert abs(abs(u * v.conj()) - 1 / np.sqrt(6)) < 1e-12                         # (1)
    assert abs(abs(u) ** 2 - (1 + (1 if x == 0 else -1) * s3) / 2) < 1e-12


def h2_setting(n, counts, lam):
    """Exact H^2 for the setting with counts (nX, nY, nZ), summing over outcome types with multiplicity."""
    d = 2 ** n; aff = 0.0
    nX, nY, nZ = counts
    for ks in itertools.product(range(nX + 1), range(nY + 1), range(nZ + 1)):
        A = B = 1.0 + 0j; mlt = 1
        for c, nc, k in zip('XYZ', counts, ks):
            u1, v1 = amp[(c, 1)]; u0, v0 = amp[(c, 0)]
            A *= u1 ** k * u0 ** (nc - k); B *= v1 ** k * v0 ** (nc - k); mlt *= comb(nc, k)
        diag = (abs(A) ** 2 + abs(B) ** 2) / 2; cross = np.real(A * B.conj())
        p0 = (1 - lam) / d + lam * (diag + cross); p1 = (1 - lam) / d + lam * (diag - cross)
        aff += mlt * np.sqrt(p0 * p1)
    return 1 - aff


worst = 0.0
for n in range(1, 15):
    for lam in (0.05, 0.2, 0.5):
        bound = lam ** 2 * (2 / 3) ** n / (1 - lam)
        hs = [h2_setting(n, (nX, nY, n - nX - nY), lam) for nX in range(n + 1) for nY in range(n + 1 - nX)]
        assert max(hs) <= bound * (1 + 1e-9), (n, lam, max(hs), bound)               # (2)
        worst = max(worst, max(hs) / bound)
        if lam == 0.2:
            T = np.log(1 / np.sqrt(8 / 9)) / -np.log(1 - max(hs))
            print(f"n={n:2d} lam={lam}: max_b H^2 = {max(hs):.4e}, bound = {bound:.4e}, ratio = {max(hs)/bound:.3f}, "
                  f"copies to separate the pair >= {T:.1f}")
print(f"largest ratio max_b H^2 / bound: {worst:.4f}")

# (3), (4): brute force at n = 4 with random adaptive trees
n = 4; d = 2 ** n; rng = np.random.default_rng(1)
A = a; B = ab
for _ in range(n - 1): A = np.kron(A, a); B = np.kron(B, ab)
cat = (A + B) / np.sqrt(2); anti = (A - B) / np.sqrt(2)
for lam in (0.1, 0.5):
    s0 = (1 - lam) * np.eye(d) / d + lam * np.outer(cat, cat.conj())
    s1 = (1 - lam) * np.eye(d) / d + lam * np.outer(anti, anti.conj())
    assert abs(np.real(cat.conj() @ (s0 - s1) @ cat) - lam) < 1e-12                  # (4)
    bound = lam ** 2 * (2 / 3) ** n / (1 - lam)
    for trial in range(200):
        tree = {}
        def leaves(hist, done):
            # hist: tuple of (qubit, axis, outcome); choose next qubit and axis from the history
            if len(done) == n:
                yield hist; return
            key = hist
            if key not in tree:
                free = [q for q in range(n) if q not in done]
                tree[key] = (free[rng.integers(len(free))], 'XYZ'[rng.integers(3)])
            q, c = tree[key]
            for x in (0, 1):
                yield from leaves(hist + ((q, c, x),), done | {q})
        aff = 0.0; tot = 0.0
        for leaf in leaves((), frozenset()):
            vecs = [None] * n
            for q, c, x in leaf: vecs[q] = AX[c][:, x]
            e = vecs[0]
            for v in vecs[1:]: e = np.kron(e, v)
            p0 = np.real(e.conj() @ s0 @ e); p1 = np.real(e.conj() @ s1 @ e); tot += p0
            aff += np.sqrt(max(p0, 0) * max(p1, 0))
        assert abs(tot - 1) < 1e-10
        assert 1 - aff <= bound * (1 + 1e-9), (lam, 1 - aff, bound)                   # (3)
print("adaptive trees at n = 4: bound holds for 400 random trees")

# (5) exact optimum over all adaptive one-copy trees, by dynamic programming over the counts of the six
# (axis, outcome) types: tau_pm are permutation invariant, so the leaf law depends only on these counts,
# and the qubit chosen next does not matter.
from functools import lru_cache
amps = [amp[(c, x)] for c in 'XYZ' for x in (0, 1)]
def adaptive_h2(n, lam):
    d = 2 ** n
    @lru_cache(None)
    def f(cnt):   # least affinity sum over the subtree below a node
        if sum(cnt) == n:
            A = np.prod([amps[k][0] ** cnt[k] for k in range(6)]); B = np.prod([amps[k][1] ** cnt[k] for k in range(6)])
            return np.sqrt(((1 - lam) / d + lam * abs(A + B) ** 2 / 2) * ((1 - lam) / d + lam * abs(A - B) ** 2 / 2))
        return min(sum(f(tuple(c + (1 if k == 2 * ax + x else 0) for k, c in enumerate(cnt))) for x in (0, 1)) for ax in range(3))
    return 1 - f((0,) * 6)
worst = 0.0
for n in range(1, 15):
    for lam in (0.2, 0.5):
        h, b = adaptive_h2(n, lam), lam ** 2 * (2 / 3) ** n / (1 - lam)
        assert h <= b * (1 + 1e-9); worst = max(worst, h / b)
print(f"exact optimum over adaptive one-copy trees, n <= 14: largest ratio to the bound {worst:.4f}")

# (6) stored copies: random fully adaptive trees on all nT qubits of T copies (next qubit from any copy, axis
# from the outcomes so far); assert the pointwise ratio |c|/b <= rho per copy and the affinity bound
# sum_leaves sqrt(P+ P-) >= (1 - rho^2)^(T/2), rho = lam (2/3)^(n/2)/(1 - lam), with both laws from tau^(x)T.
def stored_check(n, T, lam, trials, rng):
    d = 2 ** n
    A1 = a; B1 = ab
    for _ in range(n - 1): A1 = np.kron(A1, a); B1 = np.kron(B1, ab)
    c1, c2 = (A1 + B1) / np.sqrt(2), (A1 - B1) / np.sqrt(2)
    tp = (1 - lam) * np.eye(d) / d + lam * np.outer(c1, c1.conj()); tm = (1 - lam) * np.eye(d) / d + lam * np.outer(c2, c2.conj())
    rho = lam * (2 / 3) ** (n / 2) / (1 - lam); worst = 0.0; N = n * T
    for _ in range(trials):
        tree = {}
        def leaves(hist, done):
            if len(done) == N:
                yield hist; return
            if hist not in tree:
                free = [q for q in range(N) if q not in done]
                tree[hist] = (free[rng.integers(len(free))], 'XYZ'[rng.integers(3)])
            q, c = tree[hist]
            for x in (0, 1): yield from leaves(hist + ((q, c, x),), done | {q})
        aff = 0.0; tot = 0.0
        for leaf in leaves((), frozenset()):
            vec = [None] * N
            for q, c, x in leaf: vec[q] = AX[c][:, x]
            pp = pm = 1.0
            for t in range(T):
                e = vec[t * n]
                for v in vec[t * n + 1:(t + 1) * n]: e = np.kron(e, v)
                gp, gm = np.real(e.conj() @ tp @ e), np.real(e.conj() @ tm @ e)
                assert abs(gp - gm) / (gp + gm) <= rho * (1 + 1e-9)   # |c|/b with g = b +- c
                pp *= gp; pm *= gm
            aff += np.sqrt(pp * pm); tot += pp
        assert abs(tot - 1) < 1e-10
        assert aff >= (1 - rho ** 2) ** (T / 2) - 1e-12, (n, T, lam, aff)
        worst = max(worst, (1 - aff) / (1 - (1 - rho ** 2) ** (T / 2)))
    return worst
rng = np.random.default_rng(2); w = 0.0
for n, T in ((1, 2), (1, 4), (2, 2), (2, 3), (3, 2)):
    for lam in (0.2, 0.5):
        w = max(w, stored_check(n, T, lam, 30, rng))
print(f"stored copies, random fully adaptive trees: bound holds; largest (1 - affinity)/(1 - bound) = {w:.4f}")
