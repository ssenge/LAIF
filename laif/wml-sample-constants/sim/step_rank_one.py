"""Exact bound for rank-one L = |a><b| (|a| = |b| = 1), d >= 3: with B = |b><b|, Bp = I - B and
P = (Tr(rB) I - L r L+)/4 + ((d-1)/4) Bp r Bp,  N = ((d-1)/4) L r L+ + Lind^2/2 + ((d-1)/4) Bp r Bp,
P and N are CP, P - N = E_L - Lind^2/2 and P*(I) = ((d-1)/4) I, so (1/2)||E_L - Lind^2/2||_dia <= (d-1)/4."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np
def choi(f, d):
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; J += np.kron(E, f(E))
    return J
rng = np.random.default_rng(6)
for d in (3, 4, 5, 6, 8):
    for k in range(300):
        a = rng.normal(size=d) + 1j * rng.normal(size=d); b = rng.normal(size=d) + 1j * rng.normal(size=d)
        if k % 5 == 1: b = a + 0.05 * b                      # nearly equal
        if k % 5 == 2: b = b - (a.conj() @ b) / (a.conj() @ a) * a   # orthogonal
        a /= np.linalg.norm(a); b /= np.linalg.norm(b)
        L = np.outer(a, b.conj()); Ld = L.conj().T; B = np.outer(b, b.conj()); Bp = np.eye(d) - B
        lind = lambda r: L @ r @ Ld - (B @ r + r @ B) / 2
        P = lambda r: (np.trace(r @ B) * np.eye(d) - L @ r @ Ld) / 4 + (d - 1) / 4 * Bp @ r @ Bp
        N = lambda r: (d - 1) / 4 * L @ r @ Ld + lind(lind(r)) / 2 + (d - 1) / 4 * Bp @ r @ Bp
        Phi = lambda r: np.trace(r @ B) * np.eye(d) / 4 - d / 4 * L @ r @ Ld - lind(lind(r)) / 2
        JP, JN = choi(P, d), choi(N, d)
        assert np.abs(JP - JN - choi(Phi, d)).max() < 1e-12
        assert np.linalg.eigvalsh(JP).min() > -1e-12 and np.linalg.eigvalsh(JN).min() > -1e-12, (d, k)
        PI = JP.reshape(d, d, d, d).trace(axis1=1, axis2=3)
        assert np.abs(PI - (d - 1) / 4 * np.eye(d)).max() < 1e-12
    # the 3 x 3 coefficient matrix over the Kraus set {L, B, Bp}
    for mu in np.linspace(0, 1, 101):
        M = np.array([[(d - 1) / 4 + (mu * mu - 1) / 2, -mu / 4, 0], [-mu / 4, 0.5, 0.125], [0, 0.125, (d - 1) / 4]])
        assert np.linalg.eigvalsh(M).min() >= -1e-15, (d, mu)
print("ok: rank-one certificate for d = 3..8, P*(I) = (d-1)/4 I")
