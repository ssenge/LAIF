"""Optimal Q=0 symmetry shift (c_n per DF vector, mu for the one-body term) for the k-point DF lambda.
The objective is convex in (c, mu); minimized with L-BFGS on its subgradient, then re-evaluated exactly with dflam.lam.
Usage: opt_shift.py data.npz"""
import sys, json, time
import numpy as np
from scipy.optimize import minimize
import dflam

def setup(path):
    d = np.load(path, allow_pickle=True)
    L, hc, kpts = d["L"], d["hcore"], d["kpts"]
    import lno_cell
    a = lno_cell.r3m().lattice_vectors()
    return L, hc, kpts, a, int(d["nelec"]) * len(kpts), d

def make_objective(L, hc, nelec_total):
    nk, nmo = len(hc), hc[0].shape[0]
    M = [0.5 * (m + m.conj().T) for m in dflam.onebody(hc, L)]
    Lkk = [L[k, k] for k in range(nk)]
    naux = Lkk[0].shape[0]
    f = np.concatenate([np.array([np.linalg.eigvalsh(X[n]) for n in range(naux)]) for X in Lkk], axis=1)  # (naux, nk*nmo)
    beta = nelec_total / nk - nmo
    def obj(x):
        c, mu = x[:-1], x[-1]
        val, g = 0.0, np.zeros_like(x)
        for k in range(nk):
            Mk = M[k] + beta * np.einsum("n,npq->pq", c, Lkk[k]) - mu * np.eye(nmo)
            e, V = np.linalg.eigh(Mk)
            val += np.abs(e).sum()
            S = (V * np.sign(e)) @ V.conj().T
            g[:-1] += beta * np.einsum("qp,npq->n", S, Lkk[k]).real
            g[-1] -= np.trace(S).real
        r = f - c[:, None]
        s = np.abs(r).sum(1) / np.sqrt(nk)
        val += 0.25 * (s**2).sum()
        g[:-1] += 0.25 * 2 * s * (-np.sign(r).sum(1) / np.sqrt(nk))
        return val, g
    return obj, beta, naux

def q0_part(L, hc):
    """Lambda contribution that the shift can change: one-body plus Q=0 A-terms (no truncation)."""
    obj, _, naux = make_objective(L, hc, 0)
    return obj(np.zeros(naux + 1))[0]

if __name__ == "__main__":
    L, hc, kpts, a, ne, d = setup(sys.argv[1])
    mkq = dflam.kmap(kpts, a)
    nk, nmo = len(hc), hc[0].shape[0]
    obj, beta, naux = make_objective(L, hc, ne)
    # the closed-form one-body change used in obj equals the generic re-evaluation (up to a multiple of I)
    rng = np.random.default_rng(0); c0 = rng.normal(size=naux) * 1e-2
    h2, L2 = dflam.shifted(hc, L, c0, 0.0, ne)
    M0, M1 = dflam.onebody(hc, L), dflam.onebody(h2, L2)
    for k in range(nk):
        D = M1[k] - M0[k] - beta * np.einsum("n,npq->pq", c0, L[k, k])
        assert np.allclose(D, D[0, 0] * np.eye(nmo), atol=1e-8), np.abs(D - D[0, 0] * np.eye(nmo)).max()
    out = {"file": sys.argv[1], "nk": nk, "nmo": nmo, "naux": naux, "nelec_total": ne, "beta": beta}
    for th in [1e-13, 1e-4, 1e-3]:
        out[f"base_{th:g}"] = dflam.lam(hc, L, mkq, th, return_parts=True)[:4]
    t0 = time.time()
    x0 = np.zeros(naux + 1)
    best = None
    for start in [x0]:
        r = minimize(obj, start, jac=True, method="L-BFGS-B", options={"maxiter": 3000, "maxfun": 6000})
        if best is None or r.fun < best.fun:
            best = r
    c, mu = best.x[:-1], best.x[-1]
    h2, L2 = dflam.shifted(hc, L, c, mu, ne)
    for th in [1e-13, 1e-4, 1e-3]:
        out[f"shift_{th:g}"] = dflam.lam(h2, L2, mkq, th, return_parts=True)[:4]
    out["obj0"], out["obj_opt"], out["t_opt"] = obj(x0)[0], best.fun, time.time() - t0
    np.save(sys.argv[1].replace(".npz", "_shift.npy"), best.x)
    print(json.dumps(out, default=float))
    with open("shift.jsonl", "a") as fh:
        fh.write(json.dumps(out, default=float) + "\n")
