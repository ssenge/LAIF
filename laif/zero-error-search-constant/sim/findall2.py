"""Find-All and Find-Any for k = 2 marked items, m = 1: the program of findall.py with problem size independent of N.
Stab(0) = S_{N-1} acts on 2-sets as (1-sets of [N-1]) + (2-sets of [N-1]) = 2 triv + 2 std + 1 (N-3,2), so a
Stab(0)-invariant symmetric matrix is PSD iff its 2x2, 2x2, 1x1 compressions to corresponding vectors are PSD.
Vectors: triv u1 = 1[0 in S], u2 = 1[0 not in S]; std f1 = e{0,1} - e{0,2}, f2 = image of e1 - e2 on 2-sets of [N-1];
(N-3,2): h = e{1,2} - e{1,4} - e{3,2} + e{3,4}. Johnson J(N,2) eigenvalues in closed form.
usage: findall2.py N T [all|any]   (asserts agreement with findall.py at N = 16 when run with 'selftest')"""
import os, sys
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp
from math import comb

KEYS = [(0, 0, 0), (0, 0, 1), (1, 0, 0), (1, 0, 1), (1, 1, 1), (2, 0, 0), (2, 1, 1)]   # (|S cap S'|, min, max of [0 in .])
KIDX = {k: i for i, k in enumerate(KEYS)}; MIXED = [k[1] != k[2] for k in KEYS]; BOTH0 = [i for i, k in enumerate(KEYS) if k[1] == 1]

def orb(Y1, Z1, Y2, Z2):
    """orbit index of the pairs ({Y1,Z1}, {Y2,Z2}) (arrays, broadcast)"""
    inter = ((Y1 == Y2) | (Y1 == Z2)).astype(int) + ((Z1 == Y2) | (Z1 == Z2)).astype(int)
    a = ((Y1 == 0) | (Z1 == 0)).astype(int); b = ((Y2 == 0) | (Z2 == 0)).astype(int)
    lo, hi = np.minimum(a, b), np.maximum(a, b)
    out = np.full(np.broadcast(inter, lo).shape, -1)
    for i, (j, l, h) in enumerate(KEYS): out[(inter == j) & (lo == l) & (hi == h)] = i
    assert (out >= 0).all()
    return out

def vec(pairs):   # list of ((y, z), coeff) -> arrays
    Y = np.array([min(p) for p, _ in pairs]); Z = np.array([max(p) for p, _ in pairs]); C = np.array([c for _, c in pairs], float)
    return Y, Z, C

def inner(wa, wb):
    """<wa, B_q wb> for all q"""
    Ya, Za, Ca = wa; Yb, Zb, Cb = wb
    o = orb(Ya[:, None], Za[:, None], Yb[None, :], Zb[None, :]); w = Ca[:, None] * Cb[None, :]
    return np.array([w[o == q].sum() for q in range(len(KEYS))])

def blocks(N):
    n1 = N - 1
    rest = [(y, z) for y in range(1, N) for z in range(y + 1, N)]
    u1 = vec([((0, y), 1.0) for y in range(1, N)]); u2 = vec([(p, 1.0) for p in rest])
    # trivial block by invariance: <u_a, B u_b> = |supp u_a| * (B u_b)(rep_a)
    def triv(a_rep, a_size, wb): return a_size * inner(vec([(a_rep, 1.0)]), wb)
    T = [[triv((0, 1), n1, u1), triv((0, 1), n1, u2)], [triv((1, 2), comb(n1, 2), u1), triv((1, 2), comb(n1, 2), u2)]]
    f1 = vec([((0, 1), 1.0), ((0, 2), -1.0)])
    f2 = vec([((1, z), 1.0) for z in range(2, N)] + [((1, 2) if z == 1 else (2, z), -1.0) for z in range(1, N) if z != 2])
    S = [[inner(f1, f1), inner(f1, f2)], [inner(f2, f1), inner(f2, f2)]]
    out = [np.array(T).transpose(2, 0, 1), np.array(S).transpose(2, 0, 1)]
    if N >= 5:
        h = vec([((1, 2), 1.0), ((1, 4), -1.0), ((2, 3), -1.0), ((3, 4), 1.0)])
        out.append(inner(h, h).reshape(-1, 1, 1))
    return out   # each: array (q, d, d)

def sums(N):
    """sum over x of pi_x(B_q) in the Johnson basis J_0, J_1, J_2, with and without the query sign"""
    reps = [((0, 1), (2, 3)), ((0, 1), (0, 2)), ((0, 1), (0, 1))]
    Sp = np.zeros((len(KEYS), 3)); Sm = np.zeros((len(KEYS), 3))
    for j, (s, t) in enumerate(reps):
        for x in range(N):
            q = KIDX[(j, min(x in s, x in t), max(x in s, x in t))]
            Sp[q, j] += 1; Sm[q, j] += -1 if MIXED[q] else 1
    return Sp, Sm

_POLY = None
def blocks_poly(N):
    """block entries are integer polynomials in N of degree <= 5: exact Lagrange fit on N = 12..17, checked on 18..23"""
    global _POLY
    from fractions import Fraction as Fr
    xs = list(range(12, 18))
    def lag(vals, x):
        return sum(Fr(int(round(v))) * np.prod([Fr(x - xm, xi - xm) for xm in xs if xm != xi]) for xi, v in zip(xs, vals))
    if _POLY is None:
        data = [blocks(x) for x in xs]
        _POLY = [np.array([d[b] for d in data]) for b in range(len(data[0]))]
        for x in range(18, 24):
            ch = blocks(x)
            for b, arr in enumerate(_POLY):
                pred = np.vectorize(lambda *v: float(lag(v, x)))(*arr)
                assert np.array_equal(pred, ch[b]), (b, x)
    return [np.vectorize(lambda *v: float(lag(v, N)))(*arr) for arr in _POLY]

def solve(N, T, mode="all"):
    blk = blocks(N) if N <= 200 else blocks_poly(N)
    Sp, Sm = sums(N); nq = len(KEYS)
    # variable scaling g_q = w_q h_q so that the transfer coefficients are O(1)
    w = 1 / np.abs(Sp).max(axis=1); Sp = Sp * w[:, None]; Sm = Sm * w[:, None]
    blk = [Bq * w[:, None, None] for Bq in blk]
    # diagonal congruence per block (PSD unchanged) so that all entries are O(1)
    for i, Bq in enumerate(blk):
        dg = np.sqrt(np.abs(np.einsum("qii->qi", Bq)).max(axis=0)); dg[dg == 0] = 1
        blk[i] = Bq / np.outer(dg, dg)[None]
    Jeig = np.array([[comb(N - 2, 2), 2 * (N - 2), 1], [-(N - 3), N - 4, 1], [1, -2, 1]], float)
    Jeig = Jeig / np.abs(Jeig).max(axis=1, keepdims=True)     # positive row scaling: same constraints, better conditioned
    g = cp.Variable((T, nq)); gn = cp.Variable((T, 3)); c = cp.Variable((T + 1, 3)); d = cp.Variable(T, nonneg=True)
    cons = [c[0] == np.ones(3), c[T] == 0]
    for t in range(T):
        for Bq in blk:
            M = sum(g[t, q] * Bq[q] for q in range(nq)); cons.append(M >> 0 if Bq.shape[1] > 1 else M[0, 0] >= 0)
        cons += [Jeig @ gn[t] >= 0, c[t] == g[t] @ Sp + gn[t]]
        post = g[t] @ Sm + gn[t]
        if mode == "all":
            cons += [c[t + 1][:2] == post[:2], c[t + 1][2] == post[2] - d[t]]
        else:
            hz = cp.Variable(len(BOTH0))
            for Bq in blk:
                M = sum(hz[i] * Bq[q] for i, q in enumerate(BOTH0)); cons.append(M >> 0 if Bq.shape[1] > 1 else M[0, 0] >= 0)
            cons += [c[t + 1] == post - hz @ Sp[BOTH0]]
        cons += [Jeig @ c[t + 1] >= 0]
    prob = cp.Problem(cp.Minimize(cp.sum(c[:T, 2])), cons)
    prob.solve(solver="CLARABEL", tol_gap_abs=1e-8, tol_gap_rel=1e-8, tol_feas=1e-8, max_iter=1000)
    print("status", prob.status, file=sys.stderr)
    global LAST; LAST = dict(c=c.value, d=d.value, g=g.value, gn=gn.value)
    return prob.value

if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        for N, T, mode, ref in [(16, 40, "all", 3.7421), (32, 50, "all", 5.5341), (16, 40, "any", 1.6613), (64, 70, "all", 7.9843)]:
            v = solve(N, T, mode); print(N, mode, v, ref); assert abs(v - ref) < 2e-3
        print("ok"); sys.exit()
    N, T = int(sys.argv[1]), int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else "all"
    v = solve(N, T, mode)
    ref = np.pi / 4 * (np.sqrt(N) * (1 + 2 ** -0.5) if mode == "all" else np.sqrt(N / 2))
    print("N=%d T=%d %s: min E = %.4f, ratio = %.5f" % (N, T, mode, v, v / ref), flush=True)
