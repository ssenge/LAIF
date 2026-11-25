"""Upper bound for the target psi_n: the classical-shadow estimator with uniformly random X, Y, Z axes,
o(b, s) = <psi_n| (x)_i (3 E_{b_i, s_i} - I) |psi_n>, is unbiased and has second moment at most 4.5 (3/2)^n for every
state. Asserts, for n <= 6: unbiasedness (E_b sum_s o E_{b,s} = |psi_n><psi_n|), the per-qubit identities
|3 <abar|e><e|a>|^2 = 3/2 and E_b sum_s (3|<e|a>|^2 - 1)^2 E_{b,s} = I + (r.sigma)/2, and
max_sigma E[o^2] <= 4.5 (3/2)^n; prints the exact maximum divided by (3/2)^n."""
import itertools, numpy as np
s3 = 1 / np.sqrt(3); th = np.arccos(s3)
a = np.array([np.cos(th / 2), np.exp(1j * np.pi / 4) * np.sin(th / 2)]); ab = np.array([-a[1].conj(), a[0].conj()])
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1.])
AX = {'X': np.array([[1, 1], [1, -1]]) / np.sqrt(2), 'Y': np.array([[1, 1], [1j, -1j]]) / np.sqrt(2), 'Z': np.eye(2)}
M1 = sum(np.outer(AX[c][:, x], AX[c][:, x].conj()) * (3 * abs(AX[c][:, x].conj() @ a) ** 2 - 1) ** 2 for c in 'XYZ' for x in (0, 1)) / 3
assert np.allclose(M1, np.eye(2) + (X + Y + Z) / (2 * np.sqrt(3)))
for c in 'XYZ':
    for x in (0, 1):
        e = AX[c][:, x]; assert abs(abs(3 * (ab.conj() @ e) * (e.conj() @ a)) ** 2 - 1.5) < 1e-12
for n in range(1, 7):
    A = a; B = ab
    for _ in range(n - 1): A = np.kron(A, a); B = np.kron(B, ab)
    psi = (A + B) / np.sqrt(2); d = 2 ** n; Mv = np.zeros((d, d), complex); Mean = np.zeros((d, d), complex)
    for b in itertools.product('XYZ', repeat=n):
        for s in itertools.product((0, 1), repeat=n):
            e = np.array([1.0 + 0j]); Op = np.array([[1.0 + 0j]])
            for c, x in zip(b, s):
                v = AX[c][:, x]; e = np.kron(e, v); Op = np.kron(Op, 3 * np.outer(v, v.conj()) - np.eye(2))
            o = np.real(psi.conj() @ Op @ psi); E = np.outer(e, e.conj())
            Mv += o ** 2 * E; Mean += o * E
    Mv /= 3 ** n; Mean /= 3 ** n
    assert np.allclose(Mean, np.outer(psi, psi.conj()))
    top = np.linalg.eigvalsh(Mv).max(); assert top <= 4.5 * 1.5 ** n * (1 + 1e-9)
    print(f"n={n}: max over states of E[o^2] = {top:.4f} = {top / 1.5 ** n:.4f} (3/2)^n")
