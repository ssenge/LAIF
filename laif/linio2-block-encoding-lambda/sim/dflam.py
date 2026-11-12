"""Memory-light k-point double-factorization lambda, same formulas and truncation as
openfermion.resource_estimates.pbc.df (compute_lambda + DFABKpointIntegrals.double_factorize),
plus the Q=0 identity shift of the DF vectors (symmetry shift on the N_e sector).

Conventions: L[k1,k2] has shape (naux, nmo, nmo); physical ERI
(p k1 q k2 | r k3 s k4) = (1/Nk) sum_n L[k1,k2]_npq conj(L[k4,k3]_nsr)."""
import numpy as np

def kmap(kpts, a):
    """m[Q,k] = index of k-Q (Q indexed like k)."""
    nk = len(kpts)
    frac = kpts @ a.T / (2 * np.pi)
    m = np.zeros((nk, nk), dtype=int)
    for Q in range(nk):
        for k in range(nk):
            d = frac[k] - frac[Q] + frac[0] - frac
            hit = np.where(np.abs(d - np.rint(d)).sum(1) < 1e-8)[0]
            assert len(hit) == 1
            m[Q, k] = hit[0]
    return m

def onebody(hcore, L):
    """M_k = hcore_k - 1/2 K_k + J_k as in compute_lambda."""
    nk = len(hcore)
    T = sum(np.einsum("npp->n", L[q, q]) for q in range(nk))  # sum_q Tr L[q,q]_n
    M = []
    for k in range(nk):
        K = sum(np.einsum("npr,nqr->pq", L[k, q], L[k, q].conj()) for q in range(nk)) / nk
        J = np.einsum("npq,n->pq", L[k, k], T.conj()) / nk
        M.append(hcore[k] - 0.5 * K + J)
    return M

def trunc(e, thresh):
    e = np.asarray(e)
    return e[np.abs(e) * np.abs(e).sum() >= thresh]

def lam(hcore, L, mkq, thresh=1e-13, return_parts=False):
    nk = len(hcore)
    M = onebody(hcore, L)
    l1 = sum(np.abs(np.linalg.eigvalsh(0.5 * (m + m.conj().T))).sum() for m in M)
    l2, neig = 0.0, 0
    for Q in range(nk):
        naux = max(L[k, mkq[Q, k]].shape[0] for k in range(nk))
        sa, sb = np.zeros(naux), np.zeros(naux)
        for k in range(nk):
            km = mkq[Q, k]
            X = L[k, km]
            for n in range(X.shape[0]):
                if km == k:
                    ea = np.linalg.eigvalsh(X[n])          # nmo zeros of the padded block drop out
                    eb = np.linalg.eigvalsh(0.5j * (X[n] - X[n].conj().T))
                    ea, eb = trunc(np.r_[ea, np.zeros(len(ea))], thresh), trunc(np.r_[eb, np.zeros(len(eb))], thresh)
                else:
                    s = np.linalg.svd(X[n], compute_uv=False)
                    ea = eb = trunc(np.r_[s, -s] / 2, thresh)
                sa[n] += np.abs(ea).sum() / np.sqrt(nk)
                sb[n] += np.abs(eb).sum() / np.sqrt(nk)
                neig += len(ea) + len(eb)
        l2 += (sa**2).sum() + (sb**2).sum()
    l2 *= 0.25
    return (l1 + l2, l1, l2, neig) if return_parts else l1 + l2

def shifted(hcore, L, c, mu, nelec_total):
    """Hamiltonian that equals the original one on the N_e sector (up to a constant):
    L[k,k]_n -> L[k,k]_n - c_n I, hcore_k -> hcore_k + (N_e - 1)/Nk sum_n c_n L[k,k]_n - mu I."""
    nk, nmo = len(hcore), hcore[0].shape[0]
    L2 = L.copy()
    h2 = []
    for k in range(nk):
        L2[k, k] = L[k, k] - c[:, None, None] * np.eye(nmo)[None]
        h2.append(hcore[k] + (nelec_total - 1) / nk * np.einsum("n,npq->pq", c, L[k, k]) - mu * np.eye(nmo))
    return np.array(h2), L2
