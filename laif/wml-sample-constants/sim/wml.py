"""Wave matrix Lindbladization (WML) of 2605.30301: exact single-step channel and the leading error map.
One WML step with time Delta applies exp(Delta M) to rho (x) pi_L, pi_L = |L><L| with |L> = (L (x) I)|Gamma>,
||L||_2 = 1, and traces out the program. By the transfer matrix T of [1, App. B],
    Phi_Delta = sum_j (exp(Delta T))_{0j} tr_j,  tr_j = Tr_23 S_j( . (x) pi_L ),
with tr_0 = id, tr_1 = tr_3 = L . L+, tr_2 = {L+L, .}/2, tr_4 = D1[L . L+]  (D1 = I/d Tr_1).
Expanding to second order, Phi_Delta = id + Delta Lind + Delta^2 K / 2 + O(Delta^3) with (T^2)_{0.} = (0, 1/d - d,
d/2, -1/d, d/2), and the leading per-step error map is E = (K - Lind o Lind) / 2.
Superoperators act on column-stacked vec(X) of d x d matrices."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"          # single core: set before numpy, scipy and cvxpy load their thread pools

import numpy as np
from scipy.linalg import expm

def sop_lr(A, B):          # X -> A X B
    return np.kron(B.T, A)

def lind(L):
    d = L.shape[0]; I = np.eye(d); LL = L.conj().T @ L
    return sop_lr(L, L.conj().T) - 0.5 * (sop_lr(LL, I) + sop_lr(I, LL))

def D1(d):                 # X -> I/d Tr X
    v = np.eye(d).reshape(-1, order="F")
    return np.outer(v, v) / d

def tr_maps(L):
    d = L.shape[0]; I = np.eye(d); LL = L.conj().T @ L
    jump = sop_lr(L, L.conj().T)
    return [np.eye(d * d, dtype=complex), jump, 0.5 * (sop_lr(LL, I) + sop_lr(I, LL)), jump, D1(d) @ jump]

def T(d):
    return np.array([[0, 1, -1, 0, 0], [0, 1 / d, 0, -1 / d, 0], [0, d, -d / 2, 0, -d / 2],
                     [0, d, 0, -d / 2, -d / 2], [0, d, 0, 0, -d]], float)

def step(L, Delta):
    row = expm(Delta * T(L.shape[0]))[0]
    return sum(c * m for c, m in zip(row, tr_maps(L)))

def error_map(L):
    d = L.shape[0]; row2 = (T(d) @ T(d))[0]
    K = sum(c * m for c, m in zip(row2, tr_maps(L)))
    Lin = lind(L)
    return 0.5 * (K - Lin @ Lin)

def brute_step(L, Delta):
    """exp(Delta M) on systems 1,2,3 from the definition, then Tr_23; returns the superoperator on system 1"""
    d = L.shape[0]
    G = np.eye(d).reshape(-1)                                    # |Gamma> on 2,3
    SW = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d): SW[i * d + j, j * d + i] = 1          # SWAP_12
    M = np.kron(np.eye(d), np.outer(G, G)) @ np.kron(SW, np.eye(d)) / np.sqrt(d)
    Msup = lind(M)
    vL = (np.kron(L, np.eye(d)) @ G); pi = np.outer(vL, vL.conj())
    U = expm(Delta * Msup); D = d**3
    out = np.zeros((d * d, d * d), complex)
    for k in range(d * d):
        X = np.zeros(d * d, complex); X[k] = 1; X = X.reshape(d, d, order="F")
        Y = (U @ np.kron(X, pi).reshape(-1, order="F")).reshape(D, D, order="F")
        Y = Y.reshape(d, d * d, d, d * d); out[:, k] = np.einsum("ajbj->ab", Y).reshape(-1, order="F")
    return out

def diamond(Phi, d, solver="CLARABEL"):
    """||Phi||_diamond of a Hermiticity-preserving map by the SDP of Watrous (2013): max <J, X> over
    [[rho0 (x) I, X], [X+, rho1 (x) I]] >= 0 with rho0, rho1 states; J the Choi matrix, input factor first."""
    import cvxpy as cp
    J = np.zeros((d * d, d * d), complex)                       # J = sum_ij |i><j| (x) Phi(|i><j|)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1
            J += np.kron(E, (Phi @ E.reshape(-1, order="F")).reshape(d, d, order="F"))
    X = cp.Variable((d * d, d * d), complex=True)
    r0 = cp.Variable((d, d), hermitian=True); r1 = cp.Variable((d, d), hermitian=True)
    I = np.eye(d)
    blk = cp.bmat([[cp.kron(r0, I), X], [X.H, cp.kron(r1, I)]])
    cons = [blk >> 0, cp.trace(r0) == 1, cp.trace(r1) == 1, r0 >> 0, r1 >> 0]
    prob = cp.Problem(cp.Maximize(cp.real(cp.trace(J.conj().T @ X))), cons)
    prob.solve(solver=solver, **({"max_threads": 1} if solver == "CLARABEL" else {}))
    return prob.value

if __name__ == "__main__":
    rng = np.random.default_rng(1)
    for d in (2, 3):
        L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); L /= np.linalg.norm(L)
        for Delta in (0.03, 0.2):
            err = np.abs(step(L, Delta) - brute_step(L, Delta)).max()
            print("d=%d Delta=%.2f  transfer-matrix step vs brute force: %.1e" % (d, Delta, err)); assert err < 1e-10
        h = 1e-3; E = error_map(L)
        fd = (step(L, h) - expm(h * lind(L))) / h**2
        print("d=%d  error map vs finite difference: %.1e" % (d, np.abs(fd - E).max())); assert np.abs(fd - E).max() < 1e-2
