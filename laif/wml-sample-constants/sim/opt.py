"""Optimal sample-based Lindbladian simulation with n program copies, over ALL channels (no step structure).
A protocol is one channel Lambda: S (x) P^n -> S, P = C^d (x) C^d holding |L> = (L (x) I)|Gamma>, ||L||_2 = 1.
The target is e^{t Lind_L}. The error on a witness L is (1/2)||Lambda(. (x) pi_L^n) - e^{t Lind_L}||_diamond, by the
dual SDP of Watrous: min ||Tr_out Z||_inf over Z >= 0, Z >= J(Delta). Witness families are closed under L -> U L U+,
which maps pi_L to (U (x) Ubar) pi_L (U (x) Ubar)+ and e^{t Lind_L} to its U-conjugate. Twirling over U keeps the
worst case over each orbit, so WLOG the Choi matrix J commutes with R(U) = conj(U (x) (U (x) Ubar)^n) (x) U, and the
error at one representative is the error on its orbit. The optimum is a lower bound on the worst case over all L.
Covariant J are combinations of partially transposed permutation operators (walled Brauer algebra) on the 2n+2
tensor factors [sys_in, (prog_a, prog_b) x n, out]; conj(U) acts on sys_in and every prog_a.
Choi convention: J = sum_ab |a><b| (x) Lambda(|a><b|), input first; Lambda(X) = Tr_in[(X^T (x) I) J].
usage: python opt.py n d t [witnesses]   witnesses: comma list of nil (|0><1|), proj (|0><0|)"""
import os, sys, itertools
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
from scipy.linalg import expm
from scipy.stats import unitary_group
import cvxpy as cp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "wml-constant", "sim"))
from wml import lind

def choi_of_sop(S, d):          # superoperator on column-stacked vec -> Choi, input first
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1
            J += np.kron(E, (S @ E.reshape(-1, order="F")).reshape(d, d, order="F"))
    return J

def witness(name, d):
    L = np.zeros((d, d), complex)
    if name == "nil": L[0, 1] = 1
    elif name == "proj": L[0, 0] = 1
    elif name.startswith("near"):               # near<a>_<b>_<re|im>: (|0><0| + delta E_ab or i delta E_ab)/norm
        a_, b_, part = name[4:].split("_"); L[0, 0] = 1
        L[int(a_), int(b_)] += 0.5 * (1 if part == "re" else 1j); L /= np.linalg.norm(L)
    elif name.startswith("rand"):               # seeded random complex L, ||L||_2 = 1
        r = np.random.default_rng(int(name[4:])); L = r.normal(size=(d, d)) + 1j * r.normal(size=(d, d))
        L /= np.linalg.norm(L)
    else: raise ValueError(name)
    return L

def program(L):
    d = L.shape[0]; v = np.kron(L, np.eye(d)) @ np.eye(d).reshape(-1); return np.outer(v, v.conj())

def cov_rep(U, n):
    V = U
    for _ in range(n): V = np.kron(V, np.kron(U, U.conj()))
    return np.kron(V.conj(), U)

def conj_factors(n):
    return [0] + [1 + 2 * c for c in range(n)]

def basis(n, d):
    """orthonormal basis (as d^m x d^m arrays) of the operators commuting with R(U); m = 2n+2"""
    m = 2 * n + 2; T = conj_factors(n); ops = []
    for perm in itertools.permutations(range(m)):
        # permutation operator: |i_0..i_{m-1}> -> |i_{perm^-1}>; as a tensor A[out idx..., in idx...]
        A = np.zeros((d,) * (2 * m))
        for idx in itertools.product(range(d), repeat=m):
            A[tuple(idx[perm[k]] for k in range(m)) + idx] = 1
        for f in T:                                  # partial transpose on the conjugated factors
            A = np.swapaxes(A, f, m + f)
        ops.append(A.reshape(d ** m, d ** m))
    def span(mats):
        if not mats: return []
        M = np.array([x.reshape(-1) for x in mats]); u, sv, vh = np.linalg.svd(M, full_matrices=False)
        r = int((sv > 1e-9 * max(sv[0], 1e-300)).sum()); return [vh[k].reshape(d ** m, d ** m) for k in range(r)]
    sym = span([(A + A.T) / 2 for A in ops]); skw = span([(A - A.T) / 2 for A in ops if np.abs(A - A.T).max() > 0])
    return sym + [1j * k for k in skw]          # real combinations give exactly the Hermitian covariant operators

def ptrace(A, dims, axis):
    k = len(dims); A = A.reshape(dims + dims)
    return np.trace(A, axis1=axis, axis2=k + axis).reshape(int(np.prod(dims) / dims[axis]), -1)

def solve(n, d, t, names, verbose=False):
    Din = d ** (1 + 2 * n); Dp = d ** (2 * n)
    B = basis(n, d)
    rng = np.random.default_rng(7)
    R = cov_rep(unitary_group.rvs(d, random_state=rng), n)
    assert all(np.abs(R @ b @ R.conj().T - b).max() < 1e-9 for b in B)
    c = cp.Variable(len(B))
    J = sum(c[k] * B[k] for k in range(len(B)))
    TrB = [ptrace(b, [Din, d], 1) for b in B]
    cons = [J >> 0, sum(c[k] * TrB[k] for k in range(len(B))) == np.eye(Din)]
    s = cp.Variable()
    for nm in names:
        L = witness(nm, d); piT = program(L).T
        Pn = np.array([[1.0]])
        for _ in range(n): Pn = np.kron(Pn, piT)
        K = np.kron(np.kron(np.eye(d), Pn), np.eye(d))
        red = [ptrace(K @ b, [d, Dp, d], 1) for b in B]
        JL = sum(c[k] * red[k] for k in range(len(B)))
        JT = choi_of_sop(expm(t * lind(L)), d)
        Z = cp.Variable((d * d, d * d), hermitian=True)
        cons += [Z >> 0, Z - (JL - JT) >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]
    prob = cp.Problem(cp.Minimize(s), cons)
    prob.solve(solver="CLARABEL", max_threads=1, verbose=verbose)
    return prob.value, sum(c.value[k] * B[k] for k in range(len(B))), len(B)

if __name__ == "__main__":
    n, d, t = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    names = sys.argv[4].split(",") if len(sys.argv) > 4 else ["nil"]
    val, Jv, nb = solve(n, d, t, names)
    print("n=%d d=%d t=%.3f witnesses=%s basis %d  optimal error %.6e   error/t^2 %.4f"
          % (n, d, t, ",".join(names), nb, val, val / t**2), flush=True)
