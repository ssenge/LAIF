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
