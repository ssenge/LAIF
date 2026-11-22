"""Certified lower bounds on an active-space Hamiltonian from the spin-free sum-of-squares algebra {I, a_js, a+_js, E_ij}.

H = ecore + sum h_pq E_pq + 1/2 sum (pq|rs) N2(p, r, s, q),  E_pq = sum_s a+_ps a_qs,  N2(j,k,l,i) = sum_st a+_js a+_kt a_lt a_is.
Certificate (Fock space):  H - E = v+ Z v + sum P_ij E_ij + sum Q_ij (2 d_ij - E_ji),  v = (I, E_ab),  Z, P, Q PSD.
The odd generators a_js, a+_js enter through P and Q; pairing and spin-mixing blocks vanish after averaging over the
U(1) and SU(2) symmetries of H, so this is the optimum of the full spin-free algebra.
Sector N0: add (N - N0)(y0 + sum y_ab E_ab), which is zero on every state with N0 electrons.
The SDP is solved by SCS. The certificate is then repaired to satisfy the operator identity (least-squares correction
of Z), made PSD by diagonal shifts, and every shift and residual is subtracted with an operator-norm bound:
||E_pq|| <= 2, ||N2|| <= 4, <v+ v> <= 1 + 4 n^2, ||N|| <= 2n.
Usage: python -I sos_gap.py FCIDUMP N0 out.json   |   python -I sos_gap.py test"""
import sys, json, time
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spl


class Basis:
    """Rows: 0 = I, 1 + p n + q = E_pq, then one row per class {N2(j,k,l,i), N2(k,j,i,l)}."""
    def __init__(s, n):
        s.n = n; j, k, l, i = np.indices((n,) * 4).reshape(4, -1)
        o = ((j * n + k) * n + l) * n + i; part = ((k * n + j) * n + i) * n + l
        canon = np.minimum(o, part); s.uniq, inv = np.unique(canon, return_inverse=True)
        s.row_of_op = np.empty(n ** 4, np.int64); s.row_of_op[o] = 1 + n * n + inv
        s.nrows = 1 + n * n + len(s.uniq)
    def E(s, p, q): return 1 + p * s.n + q
    def N2(s, j, k, l, i): return s.row_of_op[((j * s.n + k) * s.n + l) * s.n + i]


def blocks(B, N0):
    """Sparse maps from the certificate variables to operator coefficients (rows of B)."""
    n = B.n; D = 1 + n * n; R, C, V = [], [], []
    def add(r, c, v): R.append(r); C.append(c); V.append(v)
    add(0, 0, 1.0)
    for c in range(n):
        for d in range(n):
            Bc = 1 + c * n + d
            add(B.E(c, d), Bc * D, 1.0)                 # Z[0, (c,d)]: I+ E_cd
            add(B.E(d, c), Bc, 1.0)                     # Z[(c,d), 0]: E_dc I
    for a in range(n):
        for b in range(n):
            A = 1 + a * n + b
            for c in range(n):
                for d in range(n):
                    Bc = 1 + c * n + d; col = A + Bc * D      # E_ba E_cd = N2(b,c,d,a) + d_ac E_bd
                    add(B.N2(b, c, d, a), col, 1.0)
                    if a == c: add(B.E(b, d), col, 1.0)
    Sz = sp.csr_matrix((V, (R, C)), shape=(B.nrows, D * D))
    R, C, V = [], [], []
    for i in range(n):
        for j in range(n):
            R.append(B.E(i, j)); C.append(i + j * n); V.append(1.0)        # column-major, as cp.vec(order='F')
    Sp = sp.csr_matrix((V, (R, C)), shape=(B.nrows, n * n))
    R, C, V = [], [], []
    for i in range(n):
        for j in range(n):
            R.append(B.E(j, i)); C.append(i + j * n); V.append(-1.0)
        R.append(0); C.append(i + i * n); V.append(2.0)
    Sq = sp.csr_matrix((V, (R, C)), shape=(B.nrows, n * n))
    R, C, V = [], [], []                                # y = (y0, y_ab): (N - N0) and (N - N0) E_ab
    for p in range(n):
        R.append(B.E(p, p)); C.append(0); V.append(1.0)
    R.append(0); C.append(0); V.append(-float(N0))
    for a in range(n):
        for b in range(n):
            col = 1 + a * n + b; R.append(B.E(a, b)); C.append(col); V.append(1.0 - N0)
            for p in range(n):
                R.append(B.N2(p, a, b, p)); C.append(col); V.append(1.0)
    Sy = sp.csr_matrix((V, (R, C)), shape=(B.nrows, 1 + n * n))
    return Sz, Sp, Sq, Sy


def target(B, h, eri, ecore):
    n = B.n; t = np.zeros(B.nrows); t[0] = ecore
    for p in range(n):
        for q in range(n):
            t[B.E(p, q)] += h[p, q]
    p, q, r, s = np.indices((n,) * 4).reshape(4, -1)
    np.add.at(t, B.row_of_op[((p * n + r) * n + s) * n + q], 0.5 * eri.reshape(-1))
    return t


def solve(h, eri, ecore, N0=None, eps=1e-9, max_iters=200000, verbose=False):
    import cvxpy as cp
    n = len(h); B = Basis(n); D = 1 + n * n
    Sz, Sp, Sq, Sy = blocks(B, N0 if N0 is not None else 0)
    t = target(B, h, eri, ecore)
    Z = cp.Variable((D, D), PSD=True); P = cp.Variable((n, n), PSD=True); Q = cp.Variable((n, n), PSD=True)
    E = cp.Variable(); eI = np.zeros(B.nrows); eI[0] = 1.0
    lhs = Sz @ cp.vec(Z, order="F") + Sp @ cp.vec(P, order="F") + Sq @ cp.vec(Q, order="F") + eI * E
    y = None
    if N0 is not None:
        y0 = cp.Variable(); Y = cp.Variable((n, n), symmetric=True)
        lhs = lhs + Sy @ cp.hstack([cp.reshape(y0, (1,), order="F"), cp.vec(Y, order="F")])
    prob = cp.Problem(cp.Maximize(E), [lhs == t])
    t0 = time.time()
    prob.solve(solver="SCS", eps_abs=eps, eps_rel=eps, max_iters=max_iters, verbose=verbose)
    assert prob.status in ("optimal", "optimal_inaccurate"), prob.status
    sol = dict(Z=Z.value, P=P.value, Q=Q.value, E=float(E.value), status=prob.status, t_solve=time.time() - t0)
    if N0 is not None:
        sol["y"] = np.concatenate([[y0.value], Y.value.reshape(-1, order="F")])
    return certify(B, (Sz, Sp, Sq, Sy), t, sol, N0), sol


def certify(B, S, t, sol, N0):
    """Exact operator identity by a least-squares correction of Z, then PSD shifts; returns the certified bound."""
    Sz, Sp, Sq, Sy = S; n = B.n; D = 1 + n * n
    Z = 0.5 * (sol["Z"] + sol["Z"].T); P = 0.5 * (sol["P"] + sol["P"].T); Q = 0.5 * (sol["Q"] + sol["Q"].T)
    y = sol.get("y"); y = np.zeros(1 + n * n) if y is None else y
    if N0 is not None:
        Y = y[1:].reshape(n, n, order="F"); y = np.concatenate([[y[0]], (0.5 * (Y + Y.T)).reshape(-1, order="F")])
    def resid(Z):
        return t - (Sz @ Z.reshape(-1, order="F") + Sp @ P.reshape(-1, order="F") + Sq @ Q.reshape(-1, order="F")
                    + (Sy @ y if N0 is not None else 0))
    iu = np.triu_indices(D); cols_ab = iu[0] + iu[1] * D; cols_ba = iu[1] + iu[0] * D
    Ssym = (Sz[:, cols_ab] + Sz[:, cols_ba].multiply((iu[0] != iu[1]).astype(float))).tocsr()
    r = resid(Z); r_noI = r.copy(); r_noI[0] = 0.0
    for _ in range(3):                                  # min-norm correction of the symmetric Z, rows other than I
        dz = spl.lsqr(Ssym[1:], r_noI[1:], atol=1e-15, btol=1e-15, iter_lim=20000)[0]
        dZ = np.zeros((D, D)); dZ[iu] = dz; dZ = dZ + np.triu(dZ, 1).T; Z = Z + dZ
        r = resid(Z); r_noI = r.copy(); r_noI[0] = 0.0
    E = r[0]                                            # I row: ecore - E = (SOS identity coefficient)
    r[0] = 0.0
    lamZ = np.linalg.eigvalsh(Z)[0]; lamP = np.linalg.eigvalsh(P)[0]; lamQ = np.linalg.eigvalsh(Q)[0]
    eZ, eP, eQ = max(0.0, -lamZ), max(0.0, -lamP), max(0.0, -lamQ)
    nE = 1 + n * n
    res_norm = 2 * np.abs(r[1:nE]).sum() + 4 * np.abs(r[nE:]).sum()
    shift = eZ * (1 + 4 * n * n) + (eP + eQ) * 2 * n
    safety = 1e-6
    return dict(E_solver=sol["E"], E_repaired=float(E), residual_bound=float(res_norm), shift_bound=float(shift),
                lam_min=[float(lamZ), float(lamP), float(lamQ)],
                E_certified=float(E - res_norm - shift - safety), status=sol["status"], t_solve=sol["t_solve"])


def read_fcidump(path):
    from pyscf.tools import fcidump
    from pyscf import ao2mo
    d = fcidump.read(path)
    n = d["NORB"]; eri = ao2mo.restore(1, d["H2"], n)
    return d["H1"], eri, d["ECORE"], n, d["NELEC"]


def test():
    """Algebra against explicit fermion matrices on the full Fock space (n = 3), bounds against exact diagonalization per sector."""
    import openfermion as of
    from pyscf import ao2mo, fci
    n = 3; B = Basis(n); Sz, Sp, Sq, Sy = blocks(B, 2); rng = np.random.default_rng(0)
    def op_of(coef):
        F = of.FermionOperator((), coef[0])
        for p in range(n):
            for q in range(n):
                for s in range(2):
                    F += of.FermionOperator(((2 * p + s, 1), (2 * q + s, 0)), coef[B.E(p, q)])
        for r_, u in enumerate(B.uniq):
            u = int(u); i = u % n; l = (u // n) % n; k = (u // n ** 2) % n; j = u // n ** 3
            for s in range(2):
                for t_ in range(2):
                    F += of.FermionOperator(((2 * j + s, 1), (2 * k + t_, 1), (2 * l + t_, 0), (2 * i + s, 0)), coef[1 + n * n + r_])
        return of.get_sparse_operator(F, n_qubits=2 * n).toarray()
    Eop = lambda a, b: sum(of.FermionOperator(((2 * a + s, 1), (2 * b + s, 0))) for s in range(2))
    D = 1 + n * n; X = rng.normal(size=(D, D)); X = X + X.T
    v = [of.FermionOperator(())] + [Eop(a, b) for a in range(n) for b in range(n)]
    F = sum((of.hermitian_conjugated(v[A]) * v[Bc]) * X[A, Bc] for A in range(D) for Bc in range(D))
    assert np.allclose(op_of(Sz @ X.reshape(-1, order="F")), of.get_sparse_operator(F, n_qubits=2 * n).toarray())
    Pm = rng.normal(size=(n, n)); Qm = rng.normal(size=(n, n)); Yv = rng.normal(size=1 + n * n)
    Fp = sum(Eop(i, j) * Pm[i, j] for i in range(n) for j in range(n))
    Fq = sum((of.FermionOperator(((2 * i + s, 0), (2 * j + s, 1))) * Qm[i, j]) for i in range(n) for j in range(n) for s in range(2))
    Nop = sum(Eop(p, p) for p in range(n)) - 2 * of.FermionOperator(())
    Fy = Nop * Yv[0] + sum(Nop * Eop(a, b) * Yv[1 + a * n + b] for a in range(n) for b in range(n))
    for S_, x, Fx in ((Sp, Pm, Fp), (Sq, Qm, Fq)):
        assert np.allclose(op_of(S_ @ x.reshape(-1, order="F")), of.get_sparse_operator(Fx, n_qubits=2 * n).toarray())
    Yf = np.concatenate([[Yv[0]], Yv[1:].reshape(n, n).reshape(-1, order="F")])   # column-major E_ab index
    assert np.allclose(op_of(Sy @ Yv), of.get_sparse_operator(Fy, n_qubits=2 * n).toarray())
    for seed in range(3):                               # bounds below the exact minima
        rng = np.random.default_rng(seed); h = rng.normal(size=(n, n)); h = h + h.T
        L = rng.normal(size=(4, n, n)); L = L + L.transpose(0, 2, 1)       # Coulomb-like (pq|rs) = sum_x L_pq L_rs, PSD
        eri = np.einsum("xpq,xrs->pqrs", L, L)
        H = op_of(target(B, h, eri, 0.0)); w = np.linalg.eigvalsh(H)
        Nm = np.diag(of.get_sparse_operator(sum(of.FermionOperator(((k, 1), (k, 0))) for k in range(2 * n)), 2 * n).toarray()).real
        Uv = np.linalg.eigh(H)[1]
        sect = {}
        for N0 in range(2 * n + 1):
            idx = np.where(np.abs(Nm - N0) < 0.5)[0]; sect[N0] = np.linalg.eigvalsh(H[np.ix_(idx, idx)])[0]
        cf, _ = solve(h, eri, 0.0, None, eps=1e-8)
        assert cf["E_certified"] <= w[0] + 1e-7, (cf, w[0])
        for N0 in (2, 3):
            cn, _ = solve(h, eri, 0.0, N0, eps=1e-8)
            assert cn["E_certified"] <= sect[N0] + 1e-7, (N0, cn, sect[N0])
            assert cn["E_certified"] >= cf["E_certified"] - 1e-4, (cn, cf)
        print("seed", seed, "fock", round(cf["E_certified"], 6), "exact", round(w[0], 6),
              "N=3", round(cn["E_certified"], 6), "exact N=3", round(sect[3], 6))
    print("sos_gap self-checks passed")


if __name__ == "__main__":
    if sys.argv[1] == "test":
        test(); sys.exit()
    h, eri, ecore, n, nelec = read_fcidump(sys.argv[1]); N0 = int(sys.argv[2]) if sys.argv[2] != "fock" else None
    c, sol = solve(h, eri, ecore, N0, eps=float(sys.argv[4]) if len(sys.argv) > 4 else 1e-9)
    c.update(n=n, nelec=nelec, ecore=ecore, N0=N0)
    json.dump(c, open(sys.argv[3], "w"), indent=1); print(json.dumps(c))
