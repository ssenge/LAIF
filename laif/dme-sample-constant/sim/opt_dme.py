"""Optimal error over ALL channels Lambda: S (x) P^n -> S (P = C^d) for simulating e^{-it[sigma, .]} on pure sigma.
Pure states form one orbit of U(d); twirling keeps the worst case, so WLOG Lambda is covariant under conj(U)^{(x)(n+1)}
(inputs) (x) U (output), and the error at sigma = |0><0| is the worst case over all pure sigma: a lower bound for every
protocol with n copies. Covariant Choi matrices: partially transposed permutations of the n + 2 factors
[sys_in, prog x n, out], symmetrized over the program factors. Compared with n DME steps.
usage: opt_dme.py d t nmax"""
import os, sys, itertools
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np, cvxpy as cp
from scipy.linalg import expm

def ptrace(A, dims, axis):
    k = len(dims); A = A.reshape(dims + dims)
    return np.trace(A, axis1=axis, axis2=k + axis).reshape(int(np.prod(dims) / dims[axis]), -1)

def basis(n, d):
    m = n + 2; seen = {}
    for perm in itertools.permutations(range(m)):
        A = np.zeros((d,) * (2 * m))
        for idx in itertools.product(range(d), repeat=m):
            A[tuple(idx[perm[k]] for k in range(m)) + idx] = 1
        for f in range(n + 1): A = np.swapaxes(A, f, m + f)
        A = A.reshape(d ** m, d ** m)
        # symmetrize over permutations of the program factors 1..n (the program is sigma^{(x)n})
        seen[perm] = A
    mats = list(seen.values())
    progs = list(itertools.permutations(range(1, n + 1)))
    def perm_op(p):
        full = [0] + list(p) + [n + 1]; P = np.zeros((d ** m, d ** m))
        for idx in itertools.product(range(d), repeat=m):
            j = sum(idx[full[k]] * d ** (m - 1 - k) for k in range(m)); i = sum(idx[k] * d ** (m - 1 - k) for k in range(m))
            P[j, i] = 1
        return P
    Ps = [perm_op(p) for p in progs]
    sym = [sum(P @ A @ P.T for P in Ps) / len(Ps) for A in mats]
    M = np.array([x.reshape(-1) for x in sym]); _, sv, vh = np.linalg.svd(M, full_matrices=False)
    span = [vh[k].reshape(d ** m, d ** m) for k in range(int((sv > 1e-9 * sv[0]).sum()))]
    out = []
    for A in span:
        for H in ((A + A.conj().T) / 2, (A - A.conj().T) / 2j):
            if np.abs(H).max() > 1e-12: out.append(H)
    M = np.array([x.reshape(-1) for x in out]); _, sv, vh = np.linalg.svd(np.concatenate([M.real, M.imag], 1), full_matrices=False)
    r = int((sv > 1e-9 * sv[0]).sum()); N = d ** (2 * m)
    return [(vh[k, :N] + 1j * vh[k, N:]).reshape(d ** m, d ** m) for k in range(r)]

def target(d, t):
    sig = np.zeros((d, d)); sig[0, 0] = 1; U = expm(-1j * t * sig); J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; J += np.kron(E, U @ E @ U.conj().T)
    return J

def reduce(C, n, d):
    sig = np.zeros((d, d)); sig[0, 0] = 1; S = sig
    for _ in range(n - 1): S = np.kron(S, sig)
    K = np.kron(np.kron(np.eye(d), S.T), np.eye(d)); return ptrace(K @ C, [d, d ** n, d], 1)

def dme_error(n, d, t):
    sig = np.zeros((d, d), complex); sig[0, 0] = 1; D = t / n; c, s = np.cos(D), np.sin(D)
    step = lambda r: c * c * r + s * s * sig * np.trace(r) - 1j * s * c * (sig @ r - r @ sig)
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; X = E
            for _ in range(n): X = step(X)
            J += np.kron(E, X)
    cons, s = dia(J - target(d, t), d); cp.Problem(cp.Minimize(s), cons).solve(solver="SCS", eps=1e-10); return s.value

def dia(Jd, d):
    Z = cp.Variable((d * d, d * d), hermitian=True); s = cp.Variable()
    H = (Jd + Jd.conj().T) / 2 if isinstance(Jd, np.ndarray) else (Jd + Jd.H) / 2
    cons = [Z >> 0, Z - H >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]
    return cons, s

if __name__ == "__main__":
    d, t, nmax = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    for n in range(1, nmax + 1):
        B = basis(n, d); Din = d ** (n + 1)
        c = cp.Variable(len(B)); C = sum(c[k] * B[k] for k in range(len(B)))
        cons = [C >> 0, cp.partial_trace(C, [Din, d], axis=1) == np.eye(Din)]
        dc, s = dia(sum(c[k] * reduce(B[k], n, d) for k in range(len(B))) - target(d, t), d)
        cp.Problem(cp.Minimize(s), cons + dc).solve(solver="SCS", eps=1e-10, max_iters=400000)
        ed = dme_error(n, d, t)
        print("d=%d t=%.3f n=%d: basis %d, optimal n eps/t^2 = %.4f, DME n eps/t^2 = %.4f" % (d, t, n, len(B), n * s.value / t ** 2, n * ed / t ** 2), flush=True)
