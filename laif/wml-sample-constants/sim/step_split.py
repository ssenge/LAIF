"""Phi_L = E_L - Lind^2/2 = P - N with P = tr(rho K) I/4 + Y, N = (d/4) J + Lind^2/2 + Y,
Y = y rho + Z rho Z+/(4d) + K^2 rho K^2/(64 y), Z = LK + KL, y = 1/8. Assert: P, N completely positive, P - N = Phi,
||P*(I)|| <= d/4 + 1/4 + 1/d."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np
def choi(f, d):
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; J += np.kron(E, f(E))
    return J
rng = np.random.default_rng(3); y = 1 / 8; worst = 0
for d in (2, 3, 4, 5, 6, 8):
    for k in range(200):
        L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        if k % 4 == 1: L = np.outer(L[0], L[1])
        if k % 4 == 2: L = L @ np.diag(np.linspace(1, 0.01, d) ** 3)
        if k == 3: L = np.diag([1.0] + [0] * (d - 1)).astype(complex)
        L /= np.linalg.norm(L); Ld = L.conj().T; K = Ld @ L; Z = L @ K + K @ L; K2 = K @ K
        lind = lambda r: L @ r @ Ld - (K @ r + r @ K) / 2
        Y = lambda r: y * r + Z @ r @ Z.conj().T / (4 * d) + K2 @ r @ K2 / (64 * y)
        P = lambda r: np.trace(r @ K) * np.eye(d) / 4 + Y(r)
        N = lambda r: d / 4 * L @ r @ Ld + lind(lind(r)) / 2 + Y(r)
        Phi = lambda r: np.trace(r @ K) * np.eye(d) / 4 - d / 4 * L @ r @ Ld - lind(lind(r)) / 2
        JP, JN, JF = choi(P, d), choi(N, d), choi(Phi, d)
        assert np.abs(JP - JN - JF).max() < 1e-12
        assert np.linalg.eigvalsh((JP + JP.conj().T) / 2).min() > -1e-12 and np.linalg.eigvalsh((JN + JN.conj().T) / 2).min() > -1e-12
        Pd = np.trace(K) * 0 + (d / 4) * K + y * np.eye(d) + Z.conj().T @ Z / (4 * d) + K2 @ K2 / (64 * y)
        nrm = np.linalg.norm(Pd, 2); worst = max(worst, nrm - d / 4)
        assert nrm <= d / 4 + 1 / 4 + 1 / d + 1e-12
print("ok: P, N CP, P - N = Phi, ||P*(I)|| - d/4 at most %.4f (bound 1/4 + 1/d)" % worst)
