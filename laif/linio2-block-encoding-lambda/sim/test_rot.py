"""Gauge optimization keeps every ERI block and lowers lambda; per-Q terms add up to dflam.lam. Diamond gth-szv 1x1x3."""
import itertools, numpy as np
from pyscf.pbc import gto, scf
import run_chol, dflam, rot_kpt

cell = gto.Cell()
cell.atom = "C 0 0 0; C 1.685068664391 1.685068664391 1.685068664391"
cell.basis, cell.pseudo, cell.unit, cell.verbose = "gth-szv", "gth-hf-rev", "B", 0
cell.a = "0 3.370137329 3.370137329; 3.370137329 0 3.370137329; 3.370137329 3.370137329 0"
cell.build()
mf = scf.KRHF(cell, cell.make_kpts([1, 1, 3])).density_fit(); mf.kernel()
L = run_chol.mo_chol(mf)
hc = np.asarray([C.conj().T @ h @ C for C, h in zip(mf.mo_coeff, mf.get_hcore())])
a = cell.lattice_vectors(); mkq = dflam.kmap(mf.kpts, a); nk = 3
L2, rep = rot_kpt.run(L, mf.kpts, a, iters=200, log=False)
for kp, kq, kr, ks in itertools.product(range(nk), repeat=4):
    if mkq[dflam.np.argmax([mkq[Q, kp] == kq for Q in range(nk)]), ks] != kr:
        continue
    e0 = np.einsum("npq,nsr->pqrs", L[kp, kq], L[ks, kr].conj())
    e1 = np.einsum("npq,nsr->pqrs", L2[kp, kq], L2[ks, kr].conj())
    assert np.abs(e0 - e1).max() < 1e-6, np.abs(e0 - e1).max()
for k in range(nk):
    assert np.allclose(L2[k, k], L2[k, k].conj().transpose(0, 2, 1))
l0 = dflam.lam(hc, L, mkq, 1e-13, True); l1 = dflam.lam(hc, L2, mkq, 1e-13, True)
assert np.isclose(l0[1], l1[1]), (l0, l1)                       # one-body unchanged
assert np.isclose(l1[2], sum(r["opt"] for r in rep), rtol=1e-8), (l1, rep)
assert np.isclose(l0[2], sum(r["gdf"] for r in rep), rtol=1e-8)
print("ok: eri kept, lambda", l0[0], "->", l1[0], [round(r["gdf"], 2) for r in rep], [round(r["opt"], 2) for r in rep])
