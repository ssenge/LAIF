"""KROHF + GDF for LiNiO2 R-3m, then 3-index MO integrals L[k1,k2][n,p,q] and hcore in the MO basis.
Usage: run_chol.py n1 n2 n3 out.npz [max_cycle]"""
import sys, time
import numpy as np
from pyscf.pbc import scf
import lno_cell

def mo_chol(mf):
    """L[k1,k2] = (n | p k1, q k2) with Coulomb-metric DF vectors, shape (naux, nmo, nmo)."""
    kpts, C = mf.kpts, mf.mo_coeff
    nk, nao = len(kpts), C[0].shape[0]
    L = np.empty((nk, nk), dtype=object)
    for i in range(nk):
        for j in range(nk):
            blocks = []
            for LR, LI, sign in mf.with_df.sr_loop((kpts[i], kpts[j]), compact=False):
                assert sign == 1
                blocks.append((LR + 1j * LI).reshape(-1, nao, nao))
            Lao = np.concatenate(blocks)
            L[i, j] = np.einsum("up,nuv,vq->npq", C[i].conj(), Lao, C[j], optimize=True)
    return L

if __name__ == "__main__":
    mesh = [int(x) for x in sys.argv[1:4]]
    out = sys.argv[4]
    maxc = int(sys.argv[5]) if len(sys.argv) > 5 else 30
    t0 = time.time()
    cell = lno_cell.r3m(verbose=4)
    kpts = cell.make_kpts(mesh)
    mf = scf.KROHF(cell, kpts).density_fit()
    nk = len(kpts)
    mf.nelec = (17 * nk, 16 * nk)   # one unpaired electron per cell (ferromagnetic)
    mf.max_cycle, mf.level_shift = maxc, 0.2
    mf.kernel()
    t1 = time.time()
    L = mo_chol(mf)
    hcore = np.array([C.conj().T @ h @ C for C, h in zip(mf.mo_coeff, mf.get_hcore())])
    np.savez(out, L=L, hcore=hcore, kpts=kpts, mesh=mesh, e_tot=mf.e_tot, e_nuc=cell.energy_nuc(),
             converged=mf.converged, nelec=cell.nelectron, mo_coeff=np.array(mf.mo_coeff),
             mo_occ=np.array(mf.mo_occ), allow_pickle=True)
    print("DONE e_tot", mf.e_tot, "conv", mf.converged, "naux", L[0, 0].shape[0],
          "t_scf", round(t1 - t0), "t_chol", round(time.time() - t1))
