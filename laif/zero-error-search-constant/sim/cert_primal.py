"""Exact primal certificate: a feasible point of the program of findall2.py (with gn = 0), checked in exact fractions,
whose cost is an upper bound on the optimal expected number of queries of zero-error Find-All, k = 2, m = 1
(every feasible Gram sequence is realized by an algorithm; the mass left after T rounds restarts an exact
deterministic algorithm with R queries).
Faces: where a Johnson eigenvalue j of C_t is exactly 0, every query block must annihilate the PSD matrix M^(j) with
A(M^(j)) = (Sp J_j^T): these linear equalities are imposed in the solve and kept exactly after rounding.
usage: cert_primal.py N T [eps]"""
import os, sys
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp, sympy
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import findall2 as F, cert_dual as CD
from math import ceil, asin, pi as PI, sqrt

def exact_R(N):
    """queries of a deterministic zero-error Find-All: exact amplitude amplification (k = 2 among N, then 1 among N - 1)"""
    j = lambda n, k: ceil(PI / (4 * asin(sqrt(k / n))) - 0.5)
    return j(N, 2) + j(N - 1, 1)

def blockmats(gF, blkF):
    """exact query blocks for coefficients gF: list of 2x2 / 1x1 sympy matrices"""
    return [sympy.Matrix(len(B[0]), len(B[0]), lambda i, j: sum(gF[q] * B[q][i][j] for q in range(len(gF)))) for B in blkF]

def face_rows(blk, Sp, J, zero_eigs):
    """linear equalities (rows over g, exact) forcing every block to annihilate M^(j) for j in zero_eigs"""
    A = sympy.Matrix([[sympy.Integer(int(round(v))) for v in row] for row in CD.zcoords(blk)])
    rows = []
    for j in zero_eigs:
        s = sympy.Matrix([sum(int(Sp[q, k]) * int(J[j, k]) for k in range(3)) for q in range(len(F.KEYS))])
        Mc = list(A.inv() * s); i = 0
        for b, Bq in enumerate(blk):
            k = Bq.shape[1]
            if k == 2: M = sympy.Matrix([[Mc[i], Mc[i + 1]], [Mc[i + 1], Mc[i + 2]]]); i += 3
            else: M = sympy.Matrix([[Mc[i]]]); i += 1
            assert all(ev >= 0 for ev in M.eigenvals()), "M not PSD: face argument fails"
            if M.is_zero_matrix: continue
            # rows: (sum_q g_q B_q) M = 0, entries linear in g
            for r in range(k):
                for c in range(k):
                    rows.append([sum(sympy.Integer(int(round(Bq[q, r, m]))) * M[m, c] for m in range(k)) for q in range(len(F.KEYS))])
    if not rows: return sympy.zeros(0, len(F.KEYS))
    return _indep(sympy.Matrix(rows))

def _indep(R):
    piv = R.T.rref()[1]
    return R.extract(list(piv), list(range(R.shape[1])))

def solve_margin(N, T, eps, R, faces):
    blkI, Sp, Sm, J = CD.data(N)
    nq = len(F.KEYS); w = 1 / np.abs(Sp).max(axis=1)
    blk = []
    for Bq in blkI:
        Bs = Bq * w[:, None, None]; dg = np.sqrt(np.abs(np.einsum("qii->qi", Bs)).max(axis=0)); dg[dg == 0] = 1
        blk.append(Bs / np.outer(dg, dg)[None])
    Jn = J / np.abs(J).max(axis=1, keepdims=True)
    h = cp.Variable((T, nq)); c = cp.Variable((T + 1, 3)); d = cp.Variable(T, nonneg=True)
    cons = [c[0] == np.ones(3), h[0] == (1 / N) / w]
    for t in range(T):
        Fr_ = faces.get(t)
        if Fr_ is not None and Fr_.shape[0]:
            Fn = np.array(Fr_.tolist(), float) * w[None, :]; Fn /= np.abs(Fn).max(axis=1, keepdims=True)
            cons.append(Fn @ h[t] == 0)
        for Bq in blk:
            M = sum(h[t, q] * Bq[q] for q in range(nq))
            if t in faces: cons.append(M >> 0 if Bq.shape[1] > 1 else M[0, 0] >= 0)
            else: cons.append(M - eps * np.eye(Bq.shape[1]) >> 0 if Bq.shape[1] > 1 else M[0, 0] >= eps)
        cons += [c[t] == h[t] @ (Sp * w[:, None])]
        post = h[t] @ (Sm * w[:, None])
        cons += [c[t + 1][:2] == post[:2], c[t + 1][2] == post[2] - d[t]]
        cons += [Jn @ c[t + 1] >= (eps if t >= 1 else 0)]
    prob = cp.Problem(cp.Minimize(cp.sum(c[:T, 2]) + R * c[T, 2]), cons)
    prob.solve(solver="CLARABEL", tol_gap_abs=1e-9, tol_gap_rel=1e-9, tol_feas=1e-9, max_iter=2000)
    print("primal status", prob.status, "value", prob.value, file=sys.stderr)
    return h.value * w[None, :], d.value, blkI, Sp, Sm, J

def certify(N, T, eps):
    R = exact_R(N)
    blkI, Sp, Sm, J = CD.data(N)
    # faces: t = 0 (all states equal, g_0 = 1/N forced) and t = 1 (C_1 has no (N-3,2) part)
    faces = {0: face_rows(blkI, Sp, J, [1, 2]), 1: face_rows(blkI, Sp, J, [2])}
    g, d, blkI, Sp, Sm, J = solve_margin(N, T, eps, R, faces)
    q = 10 ** 15; rat = lambda x: sympy.Rational(int(round(x * q)), q)
    blkF = [[[[sympy.Integer(int(round(v))) for v in r] for r in Bq[qq]] for qq in range(len(F.KEYS))] for Bq in blkI]
    SpS = sympy.Matrix([[int(v) for v in row] for row in Sp]); SmS = sympy.Matrix([[int(v) for v in row] for row in Sm])
    JS = sympy.Matrix([[int(v) for v in row] for row in J])
    C = sympy.Matrix([[1, 1, 1]]); U = sympy.Integer(0)
    for t in range(T):
        U += C[2]
        eig = JS * C.T
        zero = [j for j in range(3) if eig[j] == 0]
        assert all(e >= 0 for e in eig), ("C not PSD", t)
        if t == 0: gt = sympy.Matrix([[sympy.Rational(1, N)] * len(F.KEYS)])
        else:
            g0 = sympy.Matrix([[rat(x) for x in g[t]]])
            rows = [SpS.T] + ([face_rows(blkI, Sp, J, zero)] if zero else [])
            Aeq = sympy.Matrix.vstack(*rows); b = sympy.Matrix.vstack(C.T, sympy.zeros(Aeq.shape[0] - 3, 1))
            Aeq_ind = _indep(Aeq.row_join(b)); Aeq, b = Aeq_ind[:, :-1], Aeq_ind[:, -1]
            corr = Aeq.T * (Aeq * Aeq.T).inv() * (b - Aeq * g0.T)          # exact least-norm projection
            gt = g0 + corr.T
        assert gt * SpS == C, ("equality", t)
        for M in blockmats(list(gt), blkF):
            if M.shape[0] == 1: ok = M[0, 0] >= 0
            else: ok = M[0, 0] >= 0 and M[1, 1] >= 0 and M.det() >= 0
            if not ok: print("block not PSD at t =", t, M.evalf(6)); return None
        post = gt * SmS
        pe = JS * post.T
        dt = min(max(sympy.Integer(0), rat(d[t])), min(pe))
        C = post - dt * sympy.Matrix([[0, 0, 1]])
    U += C[2] * R
    return U, R

if __name__ == "__main__":
    N, T = int(sys.argv[1]), int(sys.argv[2]); eps = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-7
    r = certify(N, T, eps)
    ref = np.pi / 4 * np.sqrt(N) * (1 + 2 ** -0.5)
    if r: print("N=%d T=%d eps=%g: CERTIFIED feasible point with cost %.6f (ratio %.5f), restart cost R=%d"
                % (N, T, eps, float(r[0]), float(r[0]) / ref, r[1]), flush=True)
