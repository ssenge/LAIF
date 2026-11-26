"""Checks for the leading constant 1 of sample-based Hamiltonian simulation (density matrix exponentiation, DME).
(1) Upper bound: the leading error map of DME, Phi(rho) = sigma tr(rho) - rho + {sigma^2, rho}/2 - sigma rho sigma, equals
    P - N with P = sigma tr(.) - sigma . sigma + sigma^2 . sigma^2/4 and N = (I - sigma^2/2) . (I - sigma^2/2), both CP,
    and P*(I) = (I - sigma^2/2)^2 <= I (random states, d = 2..5).
(2) n DME steps against e^{-it[sigma, .]}: error <= t^2/n + 2.65 t^3/n^2 for t/n <= 1/2, and n err/t^2 -> 1 at pure sigma.
(3) Lower bound: the test vectors e = |1>|0^n>|0>, f = -i/(d sqrt n) sum_m |m>|tau>|m> satisfy e+C0e = e+C1e = 0,
    f = -C0^+ C1 e, f+C0f = 1/n, e+C1f = -1/n, f+C1f = 0 (d = 2, 3, n = 1..3), so the forced leak is t^2/n."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import itertools
import numpy as np, cvxpy as cp
from scipy.linalg import expm

def choi_sop(f, d):
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; J += np.kron(E, f(E))
    return J

def dia(J, d):
    J = (J + J.conj().T) / 2; Z = cp.Variable((d * d, d * d), hermitian=True); s = cp.Variable()
    cp.Problem(cp.Minimize(s), [Z >> 0, Z - J >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]).solve(solver="SCS", eps=1e-10)
    return s.value

def rand_state(d, rng, rank=None):
    G = rng.normal(size=(d, rank or d)) + 1j * rng.normal(size=(d, rank or d)); r = G @ G.conj().T; return r / np.trace(r)

rng = np.random.default_rng(12)
# (1)
for d in (2, 3, 4, 5):
    for k in range(100):
        sg = rand_state(d, rng, 1 + k % d); s2 = sg @ sg
        P = lambda r: sg * np.trace(r) - sg @ r @ sg + s2 @ r @ s2 / 4
        M = np.eye(d) - s2 / 2; N = lambda r: M @ r @ M
        Phi = lambda r: sg * np.trace(r) - r + (s2 @ r + r @ s2) / 2 - sg @ r @ sg
        JP, JN = choi_sop(P, d), choi_sop(N, d)
        assert np.abs(JP - JN - choi_sop(Phi, d)).max() < 1e-12
        assert np.linalg.eigvalsh(JP).min() > -1e-12 and np.linalg.eigvalsh(JN).min() > -1e-12
        assert np.linalg.norm(M @ M, 2) <= 1 + 1e-12
print("(1) Phi = P - N with P, N CP and ||P*(I)|| <= 1 for 400 states, d = 2..5", flush=True)
# (2)
for d in (2, 3):
    for k in range(4):
        sg = rand_state(d, rng, 1 if k == 0 else None)
        ad = lambda r: -1j * (sg @ r - r @ sg)
        for t in (0.3, 1.0, 3.0):
            for n in (int(np.ceil(2 * t)), 8, 40):
                D = t / n; c, s = np.cos(D), np.sin(D)
                step = lambda r: c * c * r + s * s * sg * np.trace(r) - 1j * s * c * (sg @ r - r @ sg)
                U = expm(-1j * t * sg)
                def nstep(r):
                    for _ in range(n): r = step(r)
                    return r
                err = dia(choi_sop(nstep, d) - choi_sop(lambda r: U @ r @ U.conj().T, d), d)
                assert err <= t * t / n + 2.65 * t ** 3 / n ** 2 + 1e-8, (d, k, t, n, err)
                if k == 0 and n == 40: print("    d=%d pure sigma t=%.1f n=40: n err/t^2 = %.4f" % (d, t, n * err / t ** 2), flush=True)
print("(2) n-step DME error <= t^2/n + 2.65 t^3/n^2", flush=True)
# (3)
for d in (2, 3):
    for n in (1, 2, 3):
        Din = d ** (n + 1); Dt = Din * d
        def choi(f):
            C = np.zeros((Dt, Dt), complex)
            for a in range(Din):
                for b in range(Din):
                    X = np.zeros((Din, Din)); X[a, b] = 1; C[a * d:(a + 1) * d, b * d:(b + 1) * d] = f(X)
            return C
        def m0(X):
            T = X.reshape([d] * (2 * n + 2))
            for k in range(n, 0, -1): T = np.trace(T, axis1=k, axis2=k + T.ndim // 2)
            return T
        def m1(X):
            out = np.zeros((d, d), complex); T = X.reshape([d] * (2 * n + 2))
            for j in range(1, n + 1):
                U = T
                for k in [q for q in range(n, 0, -1) if q != j]: U = np.trace(U, axis1=k, axis2=k + U.ndim // 2)
                U = U.reshape(d, d, d, d)          # [s, p, s2, p2]
                for s in range(d):
                    for s2 in range(d):
                        R = np.zeros((d, d)); R[s, s2] = 1; Xp = U[s, :, s2, :]
                        out += -1j * (Xp @ R - R @ Xp) / n
            return out
        C0, C1 = choi(m0), choi(m1)
        e = np.zeros(Dt); e[(1 * d ** n) * d] = 1
        f = np.zeros(Dt, complex)
        for m in range(d):
            for j in range(n):
                idx = [0] * n; idx[j] = 1; p = sum(b * d ** (n - 1 - q) for q, b in enumerate(idx))
                f[(m * d ** n + p) * d + m] = -1j / (d * n)
        assert abs(e @ C0 @ e) < 1e-12 and abs(e @ C1 @ e) < 1e-12
        assert np.abs(f + np.linalg.pinv(C0) @ C1 @ e).max() < 1e-10
        assert abs((f.conj() @ C0 @ f) - 1 / n) < 1e-12 and abs(e @ C1 @ f + 1 / n) < 1e-12 and abs(f.conj() @ C1 @ f) < 1e-12
print("(3) test vectors: f+C0f = 1/n, e+C1f = -1/n, f+C1f = 0 for d = 2, 3 and n = 1..3; forced leak t^2/n")
print("ok")
