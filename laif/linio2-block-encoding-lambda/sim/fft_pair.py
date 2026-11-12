"""FFT check of (p k, q k' | p k, q k')-type Coulomb integrals at momentum transfer Q = k - k' for the pairs with the
largest DF values and a few random pairs: per-cell integral sum_n |L[k,k']_npq|^2 vs FFT of the pair density."""
import sys, numpy as np, lno_cell
from pyscf.pbc import tools
d = np.load(sys.argv[1], allow_pickle=True); L = d["L"]; kpts = d["kpts"]; C = d["mo_coeff"]
cell = lno_cell.r3m(); mesh = cell.mesh; coords = cell.gen_uniform_grids(mesh); ng = len(coords)
rng = np.random.default_rng(0)
for k, kq in [(0, 3), (1, 5), (3, 5), (0, 7), (2, 6)]:
    G = (np.abs(L[k, kq])**2).sum(0)                       # (p,q) per-cell integrals from DF
    top = np.dstack(np.unravel_index(np.argsort(G.ravel())[::-1][:4], G.shape))[0].tolist()
    pairs = top + rng.integers(0, 58, size=(3, 2)).tolist()
    aok = cell.pbc_eval_gto("GTOval", coords, kpt=kpts[k]); aoq = cell.pbc_eval_gto("GTOval", coords, kpt=kpts[kq])
    coulG = tools.get_coulG(cell, k=kpts[k] - kpts[kq], mesh=mesh)
    phase = np.exp(-1j * coords @ (kpts[k] - kpts[kq]))   # make the pair density cell-periodic
    for p, q in pairs:
        rho = (aok @ C[k][:, p]).conj() * (aoq @ C[kq][:, q]) * phase
        rG = tools.fft(rho, mesh) * cell.vol / ng
        f = (coulG * np.abs(rG)**2).sum() / cell.vol
        print(k, kq, p, q, "fft %.4f df %.4f" % (f, G[p, q]), flush=True)
