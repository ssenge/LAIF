"""LCU 1-norm of a Majorana encoding that keeps one QROM entry per fermionic term, as in 2607.21563.
Each hermitian two-body term W (a+p a+q a_s a_r + h.c.) (or the diagonal n_p n_q term) is expanded into Majorana
monomials; its length-4 monomials stay with the term (cost: sum of their |coefficients|), its length-2 monomials
(Z_p, and hopping from terms with one shared index) are merged into one global one-body operator together with the
one-body term, and identity parts are dropped. Shifts are optimized for this norm by a linear program.
usage: python hybrid.py snt A Z N"""
import sys, numpy as np, scipy.sparse.linalg as sla
from scipy.optimize import linprog
from shell import build, basis, hamiltonian
from shifts import operators, lam, l1_fit
from majorana import expand

def herm_terms(W):
    """group W into hermitian terms: key (p,q,r,s) with (p,q) <= (r,s)"""
    out = {}
    for (p, q, r, s), v in W.items():
        k = (p, q, r, s) if (p, q) <= (r, s) else (r, s, p, q)
        out.setdefault(k, 0)
    return sorted(out)

def term_monomials(k):
    p, q, r, s = k
    d = expand([(p, True), (q, True), (s, False), (r, False)])
    if (p, q) != (r, s):
        e = expand([(r, True), (s, True), (q, False), (p, False)])
        for m, v in e.items(): d[m] = d.get(m, 0) + v
    return {m: v for m, v in d.items() if abs(v) > 1e-12}

def setup(t, W, ops, names, terms):
    """linear data: per term the length-4 coefficients as functions of c; global length-2 coefficients"""
    mon = {k: term_monomials(k) for k in terms}
    def coef(Wd, k):  # coefficient of the hermitian term k in W (same for both orderings)
        return Wd.get(k, 0)
    rows4, rows2 = [], {}
    for k in terms:
        base = coef(W, k); cs = [coef(ops[n][1], k) for n in names]
        for m, v in mon[k].items():
            if len(m) == 4: rows4.append((base * v, [c * v for c in cs]))
            elif len(m) == 2:
                rows2.setdefault(m, [0, np.zeros(len(names), dtype=complex)]); rows2[m][0] += base * v; rows2[m][1] += np.array(cs) * v
    for p in range(len(t)):
        d = expand([(p, True), (p, False)])
        for m, v in d.items():
            if len(m) == 2:
                rows2.setdefault(m, [0, np.zeros(len(names), dtype=complex)]); rows2[m][0] += t[p] * v
                rows2[m][1] += np.array([ops[n][0][p] for n in names]) * v
    rows = rows4 + [(b, list(a)) for b, a in rows2.values()]
    b = np.array([r[0] for r in rows]); A = np.array([r[1] for r in rows])
    ph = np.where(np.abs(np.imag(b)) > 1e-12, 1j, 1)
    for j in range(A.shape[1]):
        ph = np.where((np.abs(b) < 1e-12) & (np.abs(np.imag(A[:, j])) > 1e-12), 1j, ph)
    br, Ar = np.real(b / ph), np.real(A / ph[:, None])
    assert np.allclose(br * ph, b) and np.allclose(Ar * ph[:, None], A)
    return br, Ar, len(rows4), len(rows2)

def commutes(states, orbs, t, W, S, tol=1e-8):
    """[H, S] = 0 on all one- and two-particle sectors (a necessary condition; the commutator of two two-body
    operators is up to three-body, so the target sector is checked separately in the 'ed' mode)"""
    for Zv, Nv in ((1, 0), (0, 1), (2, 0), (0, 2), (1, 1)):
        Ms = sorted({m for (o, m) in states})
        for M2 in range(-2 * max(Ms), 2 * max(Ms) + 1):
            B = basis(states, orbs, Zv, Nv, M2)
            if len(B) == 0: continue
            H = hamiltonian(states, t, W, B); X = hamiltonian(states, S[0], S[1], B)
            if abs(H @ X - X @ H).max() > tol: return False
    return True

if __name__ == "__main__":
    path, A, Z, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    states, orbs, t, W = build(path, A)
    ops = operators(states, orbs)
    names = ["Np", "Nn", "Np2", "Nn2", "NpNn", "Jz", "Jz2"]
    for k in ("J2", "T2"):
        ok = commutes(states, orbs, t, W, ops[k]); print("[H, %s] = 0: %s" % (k, ok))
        if ok: names.append(k)
    target = {"J2": 0, "T2": abs(Z - N) / 2 * (abs(Z - N) / 2 + 1), "Np2": Z * Z, "Nn2": N * N, "NpNn": Z * N, "Jz2": 0, "Np": Z, "Nn": N, "Jz": 0}
    allW = dict(W)
    for n in names:
        for k in ops[n][1]: allW.setdefault(k, 0.0)
    terms = herm_terms(allW)
    br, Ar, n4, n2 = setup(t, W, ops, names, terms)
    print("orbitals %d, hermitian two-body terms %d, source QROM entries d = %d" % (len(states), len(herm_terms(W)), len(herm_terms(W)) + int((t != 0).sum())))
    print("lambda source encoding %.2f | Majorana per-term, unshifted %.2f (ratio %.3f)" % (lam(t, W), np.abs(br).sum(), lam(t, W) / np.abs(br).sum()))
    c = l1_fit(br, Ar); r = br - Ar @ c
    W2 = dict(W)
    for ci, n in zip(c, names):
        for k, v in ops[n][1].items(): W2[k] = W2.get(k, 0) - ci * v
    W2 = {k: v for k, v in W2.items() if abs(v) > 1e-9}
    t2 = t - sum(ci * ops[n][0] for ci, n in zip(c, names))
    n_one = int((np.abs(r[n4:]) > 1e-9).sum())
    print("Majorana per-term, shifted: lambda %.2f, ratio %.3f; QROM entries d = %d (two-body %d, one-body monomials %d)"
          % (np.abs(r).sum(), lam(t, W) / np.abs(r).sum(), len(herm_terms(W2)) + n_one, len(herm_terms(W2)), n_one))
    print("shifts", {n: round(ci, 4) for n, ci in zip(names, c)}, "constant", round(sum(ci * target[n] for ci, n in zip(c, names)), 4))
    if len(sys.argv) > 5 and sys.argv[5] == "ed":   # exact check that the shifted H has the same ground energy up to the constant
        B = basis(states, orbs, Z, N, 0)
        e = sla.eigsh(hamiltonian(states, t, W, B), k=1, which="SA")[0][0]
        e2 = sla.eigsh(hamiltonian(states, t2, W2, B), k=1, which="SA")[0][0]
        assert abs(e2 + sum(ci * target[n] for ci, n in zip(c, names)) - e) < 1e-6
        print("E0 %.4f reproduced after the shift" % e)
        H = hamiltonian(states, t, W, B)
        for n in ("J2", "T2"):
            X = hamiltonian(states, ops[n][0], ops[n][1], B); cm = abs(H @ X - X @ H).max()
            print("max |[H, %s]| on the target sector: %.1e" % (n, cm)); assert cm < 1e-7
