"""k-point certified lambda floor: (E(hi det) - E(lo det))/2 with translation-invariant UHF-type determinants
(densities D_s(k) = C C^dagger, k-diagonal). Physical ERI as in dflam (1/Nk). Constants dropped."""
import sys, json, numpy as np

def energy(h, L, Da, Db, nk):
    """E and Fock matrices F_s(k) with E = sum_k Tr(h D) + E2, dE ~ Tr(F dD)."""
    T = sum(np.einsum("npq,qp->n", L[k, k], Da[k] + Db[k]) for k in range(nk))
    E = sum(np.trace(h[k] @ (Da[k] + Db[k])) for k in range(nk)) + 0.5 * (np.abs(T)**2).sum() / nk
    Fa, Fb = [], []
    for k in range(nk):
        J = np.einsum("npq,n->pq", L[k, k], T.conj()) / nk
        Ka = sum(np.einsum("npr,rs,nqs->pq", L[k, q], Da[q], L[k, q].conj(), optimize=True) for q in range(nk)) / nk
        Kb = sum(np.einsum("npr,rs,nqs->pq", L[k, q], Db[q], L[k, q].conj(), optimize=True) for q in range(nk)) / nk
        E -= 0.5 * (np.trace(Ka @ Da[k]) + np.trace(Kb @ Db[k]))
        Fa.append(h[k] + J - Ka); Fb.append(h[k] + J - Kb)
    return E.real, Fa, Fb

def occ_from_fock(F, n_tot, sign):
    """Fill the n_tot lowest (sign=+1) or highest (sign=-1) Fock levels across all k."""
    es, vs = zip(*[np.linalg.eigh(0.5 * (f + f.conj().T)) for f in F])
    allE = np.concatenate([sign * e for e in es]); order = np.argsort(allE, kind="stable")[:n_tot]
    nk, m = len(F), F[0].shape[0]
    D = []
    for k in range(nk):
        idx = [i - k * m for i in order if k * m <= i < (k + 1) * m]
        C = vs[k][:, idx]; D.append(C @ C.conj().T)
    return D

def scf(h, L, na, nb, sign, nk, iters=150, start=None):
    m = h[0].shape[0]
    Da, Db = start if start is not None else (occ_from_fock(list(h), na, sign), occ_from_fock(list(h), nb, sign))
    best = None
    for it in range(iters):
        E, Fa, Fb = energy(h, L, Da, Db, nk)
        best = E if best is None or sign * E < sign * best else best
        Da2, Db2 = occ_from_fock(Fa, na, sign), occ_from_fock(Fb, nb, sign)
        if max(np.abs(x - y).max() for x, y in zip(Da + Db, Da2 + Db2)) < 1e-8:
            break
        Da, Db = Da2, Db2
    return best

if __name__ == "__main__":
    d = np.load(sys.argv[1], allow_pickle=True)
    L, h = d["L"], d["hcore"]; nk = len(h)
    na, nb = 17 * nk, 16 * nk
    occ = d["mo_occ"]                      # ROHF occupations in its own MO basis (the basis of h and L)
    ref = ([np.diag((occ[k] > 0).astype(float)) for k in range(nk)], [np.diag((occ[k] > 1).astype(float)) for k in range(nk)])
    lo = min(scf(h, L, na, nb, +1, nk), scf(h, L, na, nb, +1, nk, start=ref))
    hi = scf(h, L, na, nb, -1, nk)
    out = {"file": sys.argv[1], "E_lo_det": lo, "E_hi_det": hi, "floor": (hi - lo) / 2}
    print(json.dumps(out))
    with open("floor.jsonl", "a") as fh:
        fh.write(json.dumps(out) + "\n")
