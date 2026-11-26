"""Controlled sample-based Hamiltonian simulation: target CU = |0><0| (x) I + |1><1| (x) e^{-it sigma} = e^{-it |1><1| (x) sigma}.
(1) DME with the program |1><1| (x) sigma on C^2 (x) C^d (one copy of sigma per step, the control qubit prepared in |1>)
    has n-step error <= t^2/n + 2.65 t^3/n^2 (Theorem 1 for the state |1><1| (x) sigma), and n err/t^2 -> 1.
(2) For comparison, the controlled partial swap |0><0| (x) I + |1><1| (x) e^{-i D SWAP} (one copy per step): its
    leading constant lim n err/t^2 at pure sigma, printed."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp
from scipy.linalg import expm

def choi_sop(f, D):
    J = np.zeros((D * D, D * D), complex)
    for i in range(D):
        for j in range(D):
            E = np.zeros((D, D)); E[i, j] = 1; J += np.kron(E, f(E))
    return J

def half_dia(J, D):
    J = (J + J.conj().T) / 2; Z = cp.Variable((D * D, D * D), hermitian=True); s = cp.Variable()
    cp.Problem(cp.Minimize(s), [Z >> 0, Z - J >> 0, s * np.eye(D) - cp.partial_trace(Z, [D, D], axis=1) >> 0]).solve(solver="CLARABEL")
    return s.value

def swap(D):
    S = np.zeros((D * D, D * D))
    for i in range(D):
        for j in range(D): S[i * D + j, j * D + i] = 1
    return S

def run(V, prog, D, n, target):
    def f(r):
        for _ in range(n):
            M = (V @ np.kron(r, prog) @ V.conj().T).reshape(D, prog.shape[0], D, prog.shape[0]); r = np.trace(M, axis1=1, axis2=3)
        return r
    return half_dia(choi_sop(f, D) - choi_sop(lambda r: target @ r @ target.conj().T, D), D)

rng = np.random.default_rng(3)
d = 2; D = 2 * d; P1 = np.diag([0.0, 1.0])
for k in range(3):
    if k == 0: sg = np.diag([1.0, 0.0]).astype(complex)
    else:
        G = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); sg = G @ G.conj().T; sg /= np.trace(sg)
    H = np.kron(P1, sg)
    for t in (0.2, 1.0):
        U = expm(-1j * t * H)
        assert np.allclose(U, np.kron(np.diag([1, 0]), np.eye(d)) + np.kron(P1, expm(-1j * t * sg)))
        for n in (4, 20):
            Vd = expm(-1j * (t / n) * swap(D))
            err = run(Vd, H, D, n, U)
            assert err <= t * t / n + 2.65 * t ** 3 / n ** 2 + 1e-6, (k, t, n, err)
            if k == 0 and n == 20: print("    (1) pure sigma t=%.1f n=20: n err/t^2 = %.4f" % (t, n * err / t ** 2), flush=True)
print("(1) DME with program |1><1| (x) sigma: error <= t^2/n + 2.65 t^3/n^2", flush=True)
sg = np.diag([1.0, 0.0]).astype(complex); t = 0.2
for n in (10, 40):
    Vc = np.kron(np.kron(np.diag([1, 0]), np.eye(d * d)), 1) + np.kron(P1, expm(-1j * (t / n) * swap(d)))
    err = run(Vc, sg, D, n, expm(-1j * t * np.kron(P1, sg)))
    print("    (2) controlled partial swap, pure sigma, t=%.1f n=%d: n err/t^2 = %.4f" % (t, n, n * err / t ** 2), flush=True)
print("ok")
