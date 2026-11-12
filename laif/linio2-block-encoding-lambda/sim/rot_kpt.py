"""k-point gauge optimization of the first DF factor, per momentum transfer Q.
For fixed Q the vectors X_n[k] = L[k, k-Q]_n give eri(Q) = sum_n vec(X_n) conj(vec(X_n))^T; any Y = W X with W
unitary (real orthogonal at Q = 0, which keeps L[k,k] Hermitian) gives the same eri(Q). Start: pivoted Cholesky of
eri(Q) computed column by column, then Riemannian descent on the two-body lambda term of Q."""
import sys, time, json
import numpy as np
from scipy.linalg import expm
import dflam

def pchol(F, tol=1e-8):
    """Pivoted Cholesky of E = F^T conj(F) (D x D, never formed). Returns rows R with R^T conj(R) = E to tol."""
    diag = (np.abs(F)**2).sum(0)
    R = []
    while diag.max() > tol:
        i = int(np.argmax(diag))
        col = F.T @ F[:, i].conj()
        if R:
            Ra = np.array(R)
            col = col - Ra.T @ Ra[:, i].conj()
        r = col / np.sqrt(diag[i].real)
        R.append(r)
        diag = diag - np.abs(r)**2
    return np.array(R)

def qterm(Y, herm, nk):
    """Two-body lambda term of one Q (no truncation) and its gradient dY (Wirtinger: df = Re sum conj(G) dY)."""
    r, _, m, _ = Y.shape
    if herm:
        e, V = np.linalg.eigh(Y)
        nn = np.abs(e).sum(-1)
        P = np.einsum("akpi,aki,akqi->akpq", V, np.sign(e), V.conj())
        coef = 0.25
    else:
        U, s, Vh = np.linalg.svd(Y)
        nn = s.sum(-1)
        P = U @ Vh
        coef = 0.5
    S = nn.sum(1) / np.sqrt(nk)
    val = coef * (S**2).sum()
    G = (2 * coef * S / np.sqrt(nk))[:, None, None, None] * P
    return val, G

def optimize(X, herm, nk, iters=300, log=False):
    r = X.shape[0]
    W = np.eye(r, dtype=float if herm else complex)
    Y = X
    val, G = qterm(Y, herm, nk)
    t, hist = 1.0, [val]
    for it in range(iters):
        E = G.reshape(len(G), -1) @ X.reshape(len(X), -1).conj().T
        if herm:
            E = E.real
            if np.iscomplexobj(X):
                W = W.real
        Om = 0.5 * (E @ W.conj().T - W @ E.conj().T)
        gn = np.sum(np.abs(Om)**2)
        while True:
            Wn = expm(-t * Om) @ W
            Yn = (Wn @ X.reshape(len(X), -1)).reshape(X.shape)
            vn, Gn = qterm(Yn, herm, nk)
            if vn <= val - 1e-4 * t * gn or t < 1e-12:
                break
            t *= 0.5
        W, Y, val, G = Wn, Yn, vn, Gn
        hist.append(val)
        t *= 1.5
        if log and it % 25 == 0:
            print(" it", it, val, flush=True)
        if it > 50 and hist[-2] - hist[-1] < 1e-7 * hist[-1]:
            break
    return Y, hist

def run(L, kpts, a, iters=300, log=True):
    nk = len(kpts)
    mkq = dflam.kmap(kpts, a)
    L2 = np.empty_like(L)
    rep = []
    done = set()
    for Q in range(nk):
        ks = [(k, mkq[Q, k]) for k in range(nk)]
        # -Q: if its partner was optimized already, take adjoints (L[k-Q,k] = L[k,k-Q]^dagger keeps eri(-Q))
        if any(k != km for k, km in ks):
            mQ = next(P for P in range(nk) if all(mkq[P, km] == k for k, km in ks))
            if mQ in done and mQ != Q:
                for k, km in ks:
                    L2[k, km] = L2[km, k].conj().transpose(0, 2, 1)
                src = next(r for r in rep if r["Q"] == mQ)
                rep.append({"Q": Q, "partner": int(mQ), "gdf": src["gdf"], "opt": src["opt"]})
                print(json.dumps(rep[-1]), flush=True)
                done.add(Q)
                continue
        X = np.stack([L[k, km] for k, km in ks], axis=1)          # (naux, nk, m, m)
        naux, _, m, _ = X.shape
        herm = all(k == km for k, km in ks)
        F = X.reshape(naux, -1)
        if herm:   # real-linear Cholesky (rows are real combinations of the Hermitian vectors, so they stay Hermitian)
            D = F.shape[1]
            R = pchol(np.concatenate([F.real, F.imag], axis=1))
            R = R[:, :D] + 1j * R[:, D:]
        else:
            R = pchol(F)
        Xc = R.reshape(-1, nk, m, m)
        if herm and np.abs(Xc.imag).max() < 1e-12:
            Xc = Xc.real
        X0 = X.real if herm and np.abs(X.imag).max() < 1e-12 else X
        Y, hist = optimize(Xc, herm, nk, iters, log)           # start 1: pivoted Cholesky
        Yg, hg = optimize(X0, herm, nk, iters, log)            # start 2: the GDF vectors themselves
        if hg[-1] < hist[-1]:
            Y, best = Yg, "gdf"
        else:
            best = "chol"
        rep.append({"Q": Q, "herm": herm, "naux": naux, "rank": int(R.shape[0]), "gdf": hg[0], "chol": hist[0],
                    "opt_chol": hist[-1], "opt_gdf": hg[-1], "opt": min(hist[-1], hg[-1]), "best": best})
        print(json.dumps(rep[-1]), flush=True)
        for i, (k, km) in enumerate(ks):
            L2[k, km] = Y[:, i]
        done.add(Q)
    return L2, rep

if __name__ == "__main__":
    d = np.load(sys.argv[1], allow_pickle=True)
    import lno_cell
    a = lno_cell.r3m().lattice_vectors()
    t0 = time.time()
    L2, rep = run(d["L"], d["kpts"], a, iters=int(sys.argv[2]) if len(sys.argv) > 2 else 300)
    np.save(sys.argv[1].replace(".npz", "_rotL.npy"), L2, allow_pickle=True)
    print("time", time.time() - t0)
