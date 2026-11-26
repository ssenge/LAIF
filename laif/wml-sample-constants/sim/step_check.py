"""Checks for the one-copy protocol (0: the step channel is CP and TP for d <= 6) of route 36 (step of sim/kraus.py, E_L(rho) = tr(rho K) I/4 - (d/4) L rho L+).
(1) The per-step leading error e_L = (1/2)||E_L - Lind_L^2/2||_diamond obeys e_L <= (d - 1/d)k/4 + k^2, k = ||L+L||,
    and e_L <= (d-1)/4 on random and structured L (d = 2..5).
(2) tr(rho K) I - (1/d) L rho L+ is completely positive (Choi PSD).
(3) End to end: n steps (exact superoperator power) against e^{t Lind}; n * err / t^2 -> e_L, and
    err <= t^2 e_L/n + (2/3) t^3 e^{2t/n}/n^2."""
import os, sys
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np
from scipy.linalg import expm
import cvxpy as cp

def sop(f, d):                        # superoperator on row-major vec
    return np.array([f(np.eye(d * d)[k].reshape(d, d)).reshape(-1) for k in range(d * d)]).T

def choi(S, d):
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; J += np.kron(E, (S @ E.reshape(-1)).reshape(d, d))
    return J

def dia_half(S, d):
    J = choi(S, d); J = (J + J.conj().T) / 2
    Z = cp.Variable((d * d, d * d), hermitian=True); s = cp.Variable()
    cons = [Z >> 0, Z - J >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]
    cp.Problem(cp.Minimize(s), cons).solve(solver="CLARABEL", max_threads=1)
    return s.value

def maps(L):
    d = L.shape[0]; Ld = L.conj().T; K = Ld @ L
    lind = sop(lambda r: L @ r @ Ld - (K @ r + r @ K) / 2, d)
    E = sop(lambda r: np.trace(r @ K) * np.eye(d) / 4 - d / 4 * L @ r @ Ld, d)
    return lind, E, np.linalg.norm(K, 2)

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from step_kraus import kraus, choi_full
for d in (2, 3, 4, 5, 6):                       # (0) the step channel itself: CP and TP on S (x) P
    for D in (4.0 / d, 1.0 / d, 0.01):
        ops = kraus(d, D); J = choi_full(ops, d)
        assert np.linalg.eigvalsh(J).min() > -1e-10
        assert np.abs(J.reshape(d ** 3, d, d ** 3, d).trace(axis1=1, axis2=3) - np.eye(d ** 3)).max() < 1e-12
print("step channel: completely positive and trace preserving for d = 2..6", flush=True)
rng = np.random.default_rng(8)
for d in (2, 3, 4, 5):
    Ls = [np.diag([1.0] + [0] * (d - 1)).astype(complex), np.eye(d, dtype=complex) / np.sqrt(d)]
    nil = np.zeros((d, d), complex); nil[0, 1] = 1; Ls.append(nil)
    for k in range(9):
        L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        if k % 3 == 1: L = np.outer(L[0], L[1])
        if k % 3 == 2: L = L @ np.diag([1, 0.2] + [0.05] * (d - 2))
        Ls.append(L / np.linalg.norm(L))
    worst = 0
    for L in Ls:
        lind, E, k = maps(L); e = dia_half(E - lind @ lind / 2, d); worst = max(worst, e)
        assert e <= (d - 1 / d) * k / 4 + k * k + 1e-6 and e <= (d - 1) / 4 + 1e-6, (d, e, k)
        Ld = L.conj().T; K = Ld @ L
        JP = choi(sop(lambda r: np.trace(r @ K) * np.eye(d) - L @ r @ Ld / d, d), d)
        assert np.linalg.eigvalsh((JP + JP.conj().T) / 2).min() > -1e-10
    print("d=%d: %d operators, max e_L = %.5f <= (d-1)/4 = %.4f; crude bound and CP of tr(rK)I - J/d hold" % (d, len(Ls), worst, (d - 1) / 4), flush=True)

for d in (2, 3):
    for L in (np.diag([1.0] + [0] * (d - 1)).astype(complex), Ls[3] if d == 5 else None):
        if L is None:
            L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); L /= np.linalg.norm(L)
        lind, E, k = maps(L); e = dia_half(E - lind @ lind / 2, d)
        for t in (0.5, 2.0):
            for n in (20, 80, 320):
                D = t / n; step = np.eye(d * d) + D * lind + D * D * E
                err = dia_half(np.linalg.matrix_power(step, n) - expm(t * lind), d)
                assert err <= t * t * e / n + 2 / 3 * t ** 3 * np.exp(2 * t / n) / n ** 2 + 1e-7, (d, t, n, err)
                print("d=%d t=%.1f n=%4d: n err/t^2 = %.4f (e_L = %.4f)" % (d, t, n, n * err / t ** 2, e), flush=True)
print("ok")
