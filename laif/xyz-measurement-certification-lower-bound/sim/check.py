"""Checks for the magic cat lower bound (paulicert/NOTES.md).
a: single-qubit state with direction (1,1,1)/sqrt3, b = a_perp; psi_n = (a^n + b^n)/sqrt2, rho_n = (a a^n + b b^n)/2.
Asserts, for n <= 6 and every Pauli basis in {X,Y,Z}^n, and for random adaptive single-qubit Pauli trees (n <= 5):
  (1) <psi|rho|psi> = 1/2;  (2) sum_leaves |u||v| = (2/3)^{n/2};  (3) chi^2(P_psi || P_rho) <= (2/3)^{n/2};
  (4) mixtures rho_s = (1-s) rho + s psi: chi^2(P_{s+2e} || P_s) <= 8 e^2 (2/3)^{n/2}  (s in [0, 1/2]) and,
      for s = 1 - 2e against s = 1: chi^2(P_1 || P_{1-2e}) <= 2 e (2/3)^{n/2}.
Prints the ratio of the largest chi^2 to (2/3)^{n/2}."""
import itertools, numpy as np
rng = np.random.default_rng(1)
r = np.ones(3) / np.sqrt(3)
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1])
w, V = np.linalg.eigh((np.eye(2) + r[0] * X + r[1] * Y + r[2] * Z) / 2); a, b = V[:, 1], V[:, 0]
assert abs(abs(a.conj() @ b)) < 1e-14
BAS = {}
for nm, P in (('X', X), ('Y', Y), ('Z', Z)):
    e, U = np.linalg.eigh(P); BAS[nm] = U.T.conj()          # rows: <x_B|
def kron(vs):
    out = np.array([1.0 + 0j])
    for v in vs: out = np.kron(out, v)
    return out
def stats(u, v):                       # leaf amplitudes u = <e|a^n>, v = <e|b^n>
    m = (abs(u) ** 2 + abs(v) ** 2) / 2; c = (u * v.conj()).real; return m, c
worst = {}
for n in range(1, 7):
    psi = (kron([a] * n) + kron([b] * n)) / np.sqrt(2)
    rho = (np.outer(kron([a] * n), kron([a] * n).conj()) + np.outer(kron([b] * n), kron([b] * n).conj())) / 2
    assert abs((psi.conj() @ rho @ psi).real - 0.5) < 1e-12
    bound = (2 / 3) ** (n / 2); mx = 0
    for B in itertools.product('XYZ', repeat=n):
        M = BAS[B[0]]
        for s in B[1:]: M = np.kron(M, BAS[s])
        u = M @ kron([a] * n); v = M @ kron([b] * n); m, c = stats(u, v)
        assert abs(np.sum(np.abs(u) * np.abs(v)) - bound) < 1e-12
        Ppsi = np.abs(M @ psi) ** 2; Prho = np.real(np.einsum('ij,jk,ik->i', M, rho, M.conj()))
        assert np.allclose(Ppsi, m + c) and np.allclose(Prho, m)
        chi = np.sum(c ** 2 / m); assert chi <= bound + 1e-12; mx = max(mx, chi)
        for eps in (0.01, 0.1, 0.2):
            P1, P1e = m + c, m + (1 - 2 * eps) * c
            assert np.sum((P1 - P1e) ** 2 / P1e) <= 2 * eps * bound + 1e-12
            for s in np.linspace(0, 0.5, 5):
                Pa, Pb = m + s * c, m + (s + 2 * eps) * c
                assert np.sum((Pb - Pa) ** 2 / Pa) <= 8 * eps ** 2 * bound + 1e-12
    worst[n] = mx / bound
# adaptive trees: qubit order and basis chosen at random as a function of the outcomes so far
def tree_sums(n, amp_a, amp_b, left, depth=0):
    """returns (sum |u||v|, chi^2) over the leaves below; amp_* are the partial products so far."""
    if not left:
        m, c = stats(amp_a, amp_b); return abs(amp_a) * abs(amp_b), c ** 2 / m
    q = left[rng.integers(len(left))]; Bn = 'XYZ'[rng.integers(3)]; s1 = s2 = 0
    for x in range(2):
        e = BAS[Bn][x]; t1, t2 = tree_sums(n, amp_a * (e @ a), amp_b * (e @ b), [l for l in left if l != q], depth + 1)
        s1 += t1; s2 += t2
    return s1, s2
for n in range(1, 6):
    for _ in range(200):
        s1, s2 = tree_sums(n, 1 + 0j, 1 + 0j, list(range(n)))
        assert abs(s1 - (2 / 3) ** (n / 2)) < 1e-12 and s2 <= (2 / 3) ** (n / 2) + 1e-12
print("all asserts passed; max chi^2 / (2/3)^{n/2} over Pauli bases:", {n: round(x, 4) for n, x in worst.items()})
