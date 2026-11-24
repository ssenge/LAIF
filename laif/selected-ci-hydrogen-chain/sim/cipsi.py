"""Linear H12 chain, STO-3G, canonical RHF orbitals, CAS(12,12) = all 853,776 determinants with Na = Nb = 6, as in
arXiv:2611.12672. Classical selection at their final budget N = 20,000 determinants, variational energy against FCI:
  cipsi  iterative EN-PT2 selection (first-order energy |<I|H|psi>|^2 / (E0 - H_II)) from the RHF determinant, the space
         growing by a factor g per step, then one variational diagonalization at exactly N
  ideal  the N determinants of largest FCI weight (reference for what any selection can reach at this budget)
Spaces are spin complete (whole bundles of determinants with the same doubly and singly occupied orbitals, bundle
score = sum of member scores, as in their S1.C), and the lowest singlet is taken (penalty S^2 added)."""
import sys, json, time, numpy as np
from pyscf import gto, scf, ao2mo, fci
from pyscf.fci import cistring, spin_op
from scipy.sparse.linalg import LinearOperator, eigsh

def setup(R):
    mol = gto.M(atom=[("H", (0, 0, i * R)) for i in range(12)], basis="sto-3g", unit="Angstrom", verbose=0)
    mf = scf.RHF(mol).run(conv_tol=1e-12); C = mf.mo_coeff; norb, ne = 12, (6, 6)
    h1 = C.T @ mf.get_hcore() @ C; eri = ao2mo.restore(1, ao2mo.kernel(mol, C), norb)
    return mol.energy_nuc(), mf.e_tot, h1, eri, norb, ne

class Ham:
    def __init__(self, h1, eri, norb, ne):
        self.h2 = fci.direct_spin1.absorb_h1e(h1, eri, norb, ne, 0.5); self.norb, self.ne = norb, ne
        self.hd = fci.direct_spin1.make_hdiag(h1, eri, norb, ne).reshape(924, 924)
    def mv(self, X): return fci.direct_spin1.contract_2e(self.h2, X, self.norb, self.ne).reshape(924, 924)
    def mvs(self, X, lam=1.0):
        return self.mv(X) + lam * spin_op.contract_ss(X, self.norb, self.ne).reshape(924, 924)
    def solve(self, mask):
        e, X = self._solve(mask); X = X / np.linalg.norm(X); return float(np.vdot(X, self.mv(X))), X
    def _solve(self, mask):
        idx = np.flatnonzero(mask.ravel()); n = idx.size
        def f(v):
            X = np.zeros(924 * 924); X[idx] = v; return self.mvs(X.reshape(924, 924)).ravel()[idx]
        if n <= 300:
            A = np.array([f(c) for c in np.eye(n)]).T; w, U = np.linalg.eigh((A + A.T) / 2); e, v = w[:1], U[:, :1]
            X = np.zeros(924 * 924); X[idx] = v[:, 0]; return e[0], X.reshape(924, 924)
        v0 = self.hd.ravel()[idx]; v0 = (v0 == v0.min()).astype(float)
        e, v = eigsh(LinearOperator((n, n), matvec=f, dtype=float), k=1, which="SA", v0=v0 + 1e-3, tol=1e-10)
        X = np.zeros(924 * 924); X[idx] = v[:, 0]; return e[0], X.reshape(924, 924)

STR = cistring.make_strings(range(12), 6)
_A, _B = STR[:, None], STR[None, :]
BID = np.unique(((_A & _B) << 12) | (_A ^ _B), return_inverse=True)[1].reshape(924, 924)
BSIZE = np.bincount(BID.ravel())

def bundles_take(score, mask, n_add):
    """Add whole spin bundles outside mask, by largest summed score, up to exactly n_add determinants."""
    bs = np.bincount(BID.ravel(), weights=np.where(mask, 0.0, score).ravel())
    chosen = np.unique(BID[mask]); bs[chosen] = -np.inf; added = 0; take = []
    for b in np.argsort(-bs):
        if not np.isfinite(bs[b]): break
        if added + BSIZE[b] > n_add: continue
        take.append(b); added += BSIZE[b]
        if added == n_add: break
    return mask | np.isin(BID, take)

def run(R, N=20000, g=2.0):
    enuc, ehf, h1, eri, norb, ne = setup(R); H = Ham(h1, eri, norb, ne)
    efci, cfci = fci.direct_spin1.FCI().kernel(h1, eri, norb, ne, tol=1e-12, max_cycle=200)
    cfci = cfci.reshape(924, 924)
    ideal = bundles_take(cfci ** 2, np.zeros((924, 924), bool), N); e_id, _ = H.solve(ideal)
    mask = np.zeros((924, 924), bool); mask |= BID == BID[0, 0]; e0, X = H.solve(mask)
    while mask.sum() < N:
        sig = H.mv(X); score = sig ** 2 / np.maximum(np.abs(e0 - H.hd), 1e-12)
        mask = bundles_take(score, mask, min(N, int(np.ceil(g * mask.sum())) + 1) - mask.sum()); e0, X = H.solve(mask)
    assert mask.sum() == N and e0 >= efci - 1e-9 and np.array_equal(np.isin(BID, np.unique(BID[mask])), mask)
    ss = fci.spin_op.spin_square(X / np.linalg.norm(X), norb, ne)[0]
    sig = H.mv(X); out = ~mask; e2 = float(np.sum(sig[out] ** 2 / (e0 - H.hd[out])))   # EN-PT2 as their Eq. (5)
    return dict(R=R, N=int(mask.sum()), g=g, E_rhf=ehf, E_fci=efci + enuc, err_cipsi_mHa=1e3 * (e0 - efci),
                err_ideal_mHa=1e3 * (e_id - efci), S2_cipsi=ss, err_cipsi_pt2_mHa=1e3 * (e0 + e2 - efci), ideal_size=int(ideal.sum()))

if __name__ == "__main__":
    out = open(sys.argv[1], "a")
    for R in [float(x) for x in sys.argv[2].split(",")]:
        for g in [float(x) for x in sys.argv[3].split(",")]:
            t = time.time(); r = run(R, g=g); r["sec"] = round(time.time() - t)
            out.write(json.dumps(r) + "\n"); out.flush(); print(r, flush=True)
