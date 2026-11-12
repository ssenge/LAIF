"""Checks: (1) dflam.lam equals openfermion compute_lambda on its diamond test system;
(2) the shifted Hamiltonian equals the original on the N_e sector (exact diagonalization, nk = 1 and 2)."""
import itertools, numpy as np
from functools import reduce
import openfermion as of
import dflam

def check_openfermion():
    """Same lambda as openfermion on diamond (gth-szv, 1x1x3 k-mesh, KRHF + GDF), for three thresholds."""
    from pyscf.pbc import gto, scf
    from openfermion.resource_estimates.pbc.df.compute_lambda_df import compute_lambda
    from openfermion.resource_estimates.pbc.df.df_integrals import DFABKpointIntegrals
    import run_chol
    cell = gto.Cell()
    cell.atom = "C 0 0 0; C 1.685068664391 1.685068664391 1.685068664391"
    cell.basis, cell.pseudo, cell.unit, cell.verbose = "gth-szv", "gth-hf-rev", "B", 0
    cell.a = "0 3.370137329 3.370137329; 3.370137329 0 3.370137329; 3.370137329 3.370137329 0"
    cell.build()
    mf = scf.KRHF(cell, cell.make_kpts([1, 1, 3])).density_fit(); mf.kernel()
    Luv = run_chol.mo_chol(mf)
    hc = np.asarray([C.conj().T @ h @ C for C, h in zip(mf.mo_coeff, mf.get_hcore())])
    mkq = dflam.kmap(mf.kpts, cell.lattice_vectors())
    for th in [1e-13, 1e-3, 1e-1]:
        h = DFABKpointIntegrals(cholesky_factor=Luv, kmf=mf); h.double_factorize(thresh=th)
        ref = compute_lambda(hc, h)
        mine = dflam.lam(hc, Luv, mkq, th, return_parts=True)
        assert np.isclose(ref.lambda_total, mine[0], rtol=1e-9), (th, ref.lambda_total, mine)
        assert ref.num_eig == mine[3], (ref.num_eig, mine[3])
        print("openfermion match", th, ref.lambda_total, mine[0], ref.num_eig)

def fermion_H(hcore, L, nk):
    nmo = hcore.shape[1]
    idx = lambda k, p, s: 2 * (k * nmo + p) + s
    H = of.FermionOperator()
    for k, p, q, s in itertools.product(range(nk), range(nmo), range(nmo), range(2)):
        H += of.FermionOperator(((idx(k, p, s), 1), (idx(k, q, s), 0)), hcore[k][p, q])
    for kp, kq, kr, ks in itertools.product(range(nk), repeat=4):
        if (kp - kq - ks + kr) % nk:
            continue
        eri = np.einsum("npq,nsr->pqrs", L[kp, kq], L[ks, kr].conj()) / nk
        for p, q, r, s in itertools.product(range(nmo), repeat=4):
            for a, b in itertools.product(range(2), repeat=2):
                H += of.FermionOperator(((idx(kp, p, a), 1), (idx(kr, r, b), 1), (idx(ks, s, b), 0), (idx(kq, q, a), 0)), 0.5 * eri[p, q, r, s])
    return H

def check_shift(nk, nmo, naux, seed):
    rng = np.random.default_rng(seed)
    L = np.empty((nk, nk), dtype=object)
    for k1 in range(nk):
        for k2 in range(k1, nk):
            X = rng.normal(size=(naux, nmo, nmo)) + 1j * rng.normal(size=(naux, nmo, nmo)) * (nk > 1)
            if k1 == k2:
                X = 0.5 * (X + X.conj().transpose(0, 2, 1))
            L[k1, k2], L[k2, k1] = X, X.conj().transpose(0, 2, 1)
    hc = rng.normal(size=(nk, nmo, nmo)) + 1j * rng.normal(size=(nk, nmo, nmo)) * (nk > 1)
    hc = 0.5 * (hc + hc.conj().transpose(0, 2, 1))
    nso = 2 * nk * nmo
    c, mu = rng.normal(size=naux), rng.normal()
    H0 = of.get_sparse_operator(fermion_H(hc, L, nk), nso).toarray()
    for ne in range(nso + 1):
        h2, L2 = dflam.shifted(hc, L, c, mu, ne)
        H1 = of.get_sparse_operator(fermion_H(h2, L2, nk), nso).toarray()
        P = [i for i in range(2**nso) if bin(i).count("1") == ne]
        D = (H1 - H0)[np.ix_(P, P)]
        const = D[0, 0]
        assert np.allclose(D, const * np.eye(len(P)), atol=1e-9), (nk, ne, np.abs(D - const * np.eye(len(P))).max())
    print("shift identity holds on every N_e sector", nk, nmo, naux)

if __name__ == "__main__":
    check_shift(1, 3, 2, 1)
    check_shift(2, 2, 2, 2)
    check_openfermion()
