"""Same SDP as opt.py, scaled to n = 2: the covariant operators are stored sparse (a partially transposed
permutation operator has d^m nonzeros), J is also symmetrized over permutations of the program copies, and the
constraint J >= 0 is imposed blockwise on the eigenspaces of a generic Hermitian element Y of the group algebra
span{R(U)}. Those eigenspaces are invariant under the commutant, so J is block diagonal in them.
usage: python opt2.py n d t witnesses"""
import os, sys, itertools, math
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
import scipy.sparse as sp
from scipy.linalg import expm
from scipy.stats import unitary_group
import cvxpy as cp
from opt import witness, program, cov_rep, conj_factors, choi_of_sop, lind

def perm_pt_sparse(perm, T, d, m):
    """partially transposed permutation operator as a sparse matrix: |i> -> |i_perm>, transposed on factors T"""
    D = d ** m; rows = np.empty(D, np.int64); cols = np.empty(D, np.int64)
    for c, idx in enumerate(itertools.product(range(d), repeat=m)):
        out = [idx[perm[k]] for k in range(m)]; inn = list(idx)
        for f in T: out[f], inn[f] = inn[f], out[f]
        r = 0; q = 0
        for k in range(m): r = r * d + out[k]; q = q * d + inn[k]
        rows[c] = r; cols[c] = q
    return sp.csr_matrix((np.ones(D), (rows, cols)), shape=(D, D))

def copy_perm_op(sigma, n, d):
    """permutation of the n program copies (pairs of factors), identity on sys_in and out, as a sparse matrix"""
    m = 2 * n + 2; perm = [0] + [0] * (2 * n) + [m - 1]
    for c in range(n):
        perm[1 + 2 * c] = 1 + 2 * sigma[c]; perm[2 + 2 * c] = 2 + 2 * sigma[c]
    return perm

def covariant_basis(n, d):
    m = 2 * n + 2; T = conj_factors(n)
    ops = [perm_pt_sparse(p, T, d, m) for p in itertools.permutations(range(m))]
    # copy symmetrization: average P_c X P_c^T over copy permutations
    Ps = [perm_pt_sparse(copy_perm_op(s, n, d), [], d, m) for s in itertools.permutations(range(n))]
    sym = [sum(P @ A @ P.T for P in Ps) / len(Ps) for A in ops]
    herm, seen = [], set()
    for A in [(A + A.T) / 2 for A in sym] + [1j * (A - A.T) / 2 for A in sym]:
        A = A.tocsr(); A.eliminate_zeros(); A.sort_indices()
        if A.nnz == 0: continue
        key = (A.indices.tobytes(), A.indptr.tobytes(), np.round(A.data, 12).tobytes())
        if key not in seen: seen.add(key); herm.append(A)
    # rank reduction by the Gram matrix (real inner product on Hermitian operators)
    G = np.array([[np.real((a.conj().multiply(b)).sum()) for b in herm] for a in herm])
    w, V = np.linalg.eigh(G); keep = w > 1e-9 * w.max()
    coef = V[:, keep] / np.sqrt(w[keep])
    return herm, coef                         # basis element j = sum_k coef[k, j] herm[k] (orthonormal)

def ptrace_sparse_out(A, Din, d):
    A = A.tocoo(); out = np.zeros((Din, Din), complex)
    ia, io = np.divmod(A.row, d); ja, jo = np.divmod(A.col, d); mask = io == jo
    np.add.at(out, (ia[mask], ja[mask]), A.data[mask]); return out

def solve(n, d, t, names, verbose=False):
    m = 2 * n + 2; D = d ** m; Din = D // d; Dp = d ** (2 * n)
    herm, coef = covariant_basis(n, d); nb = coef.shape[1]
    rng = np.random.default_rng(11)
    Y = sp.csr_matrix((D, D), dtype=complex)
    Ys = 0
    for _ in range(3):
        Rr = cov_rep(unitary_group.rvs(d, random_state=rng), n); Ys = Ys + rng.normal() * (Rr + Rr.conj().T)
    ev, Q = np.linalg.eigh(Ys)
    groups = np.split(np.arange(D), np.where(np.diff(ev) > 1e-7)[0] + 1)
    Bk = [herm[k] for k in range(len(herm))]
    blocks = [[] for _ in groups]; trs = []; reds = {nm: [] for nm in names}
    Ks = {}
    for nm in names:
        piT = program(witness(nm, d)).T; Pn = np.array([[1.0]])
        for _ in range(n): Pn = np.kron(Pn, piT)
        Ks[nm] = sp.kron(sp.kron(sp.identity(d), sp.csr_matrix(Pn)), sp.identity(d)).tocsr()
    for k, A in enumerate(Bk):
        AQ = A @ Q
        for g, idx in enumerate(groups):
            blocks[g].append(Q[:, idx].conj().T @ AQ[:, idx])
        trs.append(ptrace_sparse_out(A, Din, d))
        for nm in names:
            X = (Ks[nm] @ A).toarray().reshape(d, Dp, d, d, Dp, d)
            reds[nm].append(np.einsum("spotpu->sotu", X).reshape(d * d, d * d))
    c = cp.Variable(nb)
    lin = lambda mats: sum(c[j] * sum(coef[k, j] * mats[k] for k in range(len(mats)) if abs(coef[k, j]) > 1e-14) for j in range(nb))
    # precontract to keep the cvxpy expressions small
    def contract(mats):
        M = np.array(mats); return np.tensordot(coef, M, axes=([0], [0]))     # (nb, ...)
    def mat_expr(Bg):                         # Bg: (nb, a, a) -> a x a cvxpy expression sum_j c_j Bg[j]
        a = Bg.shape[1]; F = Bg.reshape(nb, a * a).T
        return cp.reshape(F @ c, (a, a), order="C")
    cons = []
    for g in range(len(groups)):
        Bg = contract(blocks[g]); expr = mat_expr(Bg)
        if Bg.shape[1] == 1: cons.append(cp.real(expr) >= 0)
        else: cons.append((expr + expr.H) / 2 >> 0)
    Tr = contract(trs).reshape(nb, -1).T                  # rows: entries of Tr_out J; keep distinct nonzero rows
    target = np.eye(Din).reshape(-1)
    A = np.hstack([np.vstack([Tr.real, Tr.imag]), np.concatenate([target.real, target.imag])[:, None]])
    A = A[np.abs(A).max(axis=1) > 1e-12]
    A = np.unique(np.round(A, 10), axis=0)
    cons.append(A[:, :-1] @ c == A[:, -1])
    s = cp.Variable()
    for nm in names:
        Rd = contract(reds[nm]); JL = mat_expr(Rd)
        JT = choi_of_sop(expm(t * lind(witness(nm, d))), d)
        Z = cp.Variable((d * d, d * d), hermitian=True)
        cons += [Z >> 0, Z - ((JL + JL.H) / 2 - JT) >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]
    prob = cp.Problem(cp.Minimize(s), cons)
    prob.solve(solver="CLARABEL", max_threads=1, verbose=verbose)
    return prob.value, nb, [len(g) for g in groups]

if __name__ == "__main__":
    n, d, t = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    names = sys.argv[4].split(",")
    val, nb, gs = solve(n, d, t, names)
    print("n=%d d=%d t=%.3f witnesses=%s basis %d blocks %d (max %d)  optimal error %.6e  n*err/t^2 %.4f"
          % (n, d, t, sys.argv[4], nb, len(gs), max(gs), val, n * val / t**2), flush=True)
