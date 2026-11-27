"""Exact dual certificate: a rigorous lower bound on the expected number of queries of every zero-error Find-All
algorithm, k = 2 marked items among N, m = 1 (program of findall2.py, run truncated at T rounds with the remaining
Gram C_T free, so the bound holds for algorithms of any length).
Primal (per round t < T): C_t = g_t Sp + gn_t, C_{t+1} = g_t Sm + gn_t - d_t e_2, query blocks sum_q g_tq B_q >= 0,
J gn_t >= 0, J C_{t+1} >= 0, d_t >= 0, C_0 = (1, 1, 1); cost sum_{t<T} C_t[2].
Lagrangian with multipliers y_t, z_t (equalities), Z_t >= 0 (blocks), mu_t, nu_t >= 0 (Johnson eigenvalues),
rho_t = -z_t[2] >= 0 (halting) is constant iff
  y_t + z_t = J^T mu_t,  y_t + z_{t-1} = e_2 - J^T nu_{t-1} (1 <= t < T),  z_{T-1} = -J^T nu_{T-1},
  Sp y_t + Sm z_t = A(Z_t) (A(Z)_q = sum_b <Z_b, B_q^b>),
and then every feasible point costs >= 1 - <y_0, (1,1,1)>. Given rational mu, nu >= 0 the y, z follow by back
substitution and Z_t by a 7x7 solve, all in exact fractions; the certificate checks Z_t >= 0 and rho_t >= 0 exactly.
usage: cert_dual.py N T [eps]"""
import os, sys
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp
from fractions import Fraction as Fr
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import findall2 as F

def data(N):
    blk = F.blocks(N) if N <= 200 else F.blocks_poly(N)
    assert all(np.abs(b).max() < 2 ** 52 for b in blk)
    Sp, Sm = F.sums(N)
    J = np.array([[comb(N - 2, 2), 2 * (N - 2), 1], [-(N - 3), N - 4, 1], [1, -2, 1]], float)
    return blk, Sp, Sm, J

def zcoords(blk):
    """the linear map Z -> A(Z) on coordinates (Z11, Z12, Z22 per 2x2 block, Z11 per 1x1 block)"""
    cols = []
    for Bq in blk:
        if Bq.shape[1] == 2: cols += [Bq[:, 0, 0], 2 * Bq[:, 0, 1], Bq[:, 1, 1]]
        else: cols += [Bq[:, 0, 0]]
    return np.array(cols).T     # (q, coords)

def solve_dual(N, T, eps):
    blk, Sp, Sm, J = data(N)
    nq = len(F.KEYS); w = 1 / np.abs(Sp).max(axis=1)
    r = np.abs(J).max(axis=1); Jn = J / r[:, None]
    blks, D = [], []
    for Bq in blk:
        Bs = Bq * w[:, None, None]; dg = np.sqrt(np.abs(np.einsum("qii->qi", Bs)).max(axis=0)); dg[dg == 0] = 1
        blks.append(Bs / np.outer(dg, dg)[None]); D.append(dg)
    e2 = np.array([0, 0, 1.0])
    y = cp.Variable((T, 3)); z = cp.Variable((T, 3)); mu = cp.Variable((T, 3), nonneg=True); nu = cp.Variable((T, 3), nonneg=True)
    cons = []
    for t in range(T):
        cons += [y[t] + z[t] == Jn.T @ mu[t], -z[t, 2] >= eps]
        cons += [(y[t + 1] + z[t] == e2 - Jn.T @ nu[t]) if t + 1 < T else (z[t] == -Jn.T @ nu[t])]
        lhs = cp.multiply(w, Sp @ y[t] + Sm @ z[t]); rhs = 0
        for Bs in blks:
            k = Bs.shape[1]; Zb = cp.Variable((k, k), symmetric=True)
            cons.append(Zb - eps * np.eye(k) >> 0 if k > 1 else Zb[0, 0] >= eps)
            rhs = rhs + cp.hstack([cp.trace(Zb @ Bs[q]) for q in range(nq)])
        cons.append(lhs == rhs)
    prob = cp.Problem(cp.Maximize(1 - cp.sum(y[0])), cons)
    prob.solve(solver="CLARABEL", tol_gap_abs=1e-9, tol_gap_rel=1e-9, tol_feas=1e-9, max_iter=2000)
    print("dual status", prob.status, "value", prob.value, file=sys.stderr)
    return mu.value / r[None, :], nu.value / r[None, :], blk, Sp, Sm, J

def certify(N, T, eps):
    mu, nu, blk, Sp, Sm, J = solve_dual(N, T, eps)
    q = 10 ** 15
    rat = lambda x: Fr(max(0, int(round(x * q))), q)
    JF = [[Fr(int(v)) for v in row] for row in J]
    JT = lambda v: [sum(JF[i][j] * v[i] for i in range(3)) for j in range(3)]
    SpF = [[Fr(int(v)) for v in row] for row in Sp]; SmF = [[Fr(int(v)) for v in row] for row in Sm]
    A = [[Fr(int(round(v))) for v in row] for row in zcoords(blk)]
    import sympy
    Ainv = sympy.Matrix(A).inv()                      # exact rational inverse (7 x 7)
    muF = [[rat(x) for x in row] for row in mu]; nuF = [[rat(x) for x in row] for row in nu]
    y = [None] * T; z = [None] * T
    z[T - 1] = [-v for v in JT(nuF[T - 1])]
    for t in range(T - 1, -1, -1):
        y[t] = [a - b for a, b in zip(JT(muF[t]), z[t])]
        if t > 0: z[t - 1] = [e - a - b for e, a, b in zip((0, 0, 1), JT(nuF[t - 1]), y[t])]
    for t in range(T):
        if z[t][2] > 0: print("rho < 0 at t =", t); return None
        rhs = sympy.Matrix([sum(SpF[qq][j] * y[t][j] + SmF[qq][j] * z[t][j] for j in range(3)) for qq in range(len(A))])
        Zc = list(Ainv * rhs); i = 0
        for Bq in blk:
            if Bq.shape[1] == 2:
                a, b, c = Zc[i:i + 3]; i += 3
                if not (a >= 0 and c >= 0 and a * c - b * b >= 0): print("Z not PSD at t =", t); return None
            else:
                if not Zc[i] >= 0: print("Z not PSD at t =", t); return None
                i += 1
    global DUAL; DUAL = dict(y=y, z=z, mu=muF, nu=nuF, Ainv=Ainv, A=A, Sp=SpF, Sm=SmF, J=JF)
    return Fr(1) - sum(y[0])

if __name__ == "__main__":
    N, T = int(sys.argv[1]), int(sys.argv[2]); eps = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-7
    LB = certify(N, T, eps)
    ref = np.pi / 4 * np.sqrt(N) * (1 + 2 ** -0.5)
    if LB is not None:
        print("N=%d T=%d eps=%g: CERTIFIED every zero-error Find-All algorithm uses >= %.6f queries in expectation"
              " (ratio %.5f to (pi/4) sqrt(N) (1 + 1/sqrt 2)); exact value %s" % (N, T, eps, float(LB), float(LB) / ref,
              "%d/%d" % (LB.numerator, LB.denominator) if LB.denominator < 10 ** 40 else "(large fraction)"), flush=True)
