"""All diagonal Q=0 Coulomb integrals (pp|pp) at one k by FFT (G=0 dropped) vs the DF vectors: per-cell integral = sum_n |L_npp|^2."""
import sys, numpy as np, lno_cell
from pyscf.pbc import tools
def fft_diag(cell, kpt, C, mesh=None):
    mesh = mesh or cell.mesh
    coords = cell.gen_uniform_grids(mesh)
    ao = cell.pbc_eval_gto("GTOval", coords, kpt=kpt)
    coulG = tools.get_coulG(cell, mesh=mesh)
    out = []
    for p in range(C.shape[1]):
        phi = ao @ C[:, p]
        rG = tools.fft((phi.conj() * phi).real, mesh) * cell.vol / len(coords)
        out.append((coulG * np.abs(rG)**2).sum() / cell.vol)
    return np.array(out)
if __name__ == "__main__":
    d = np.load(sys.argv[1], allow_pickle=True); k = int(sys.argv[2])
    cell = lno_cell.r3m()
    f = fft_diag(cell, d["kpts"][k], d["mo_coeff"][k])
    g = (np.abs(d["L"][k, k].transpose(1, 2, 0)[np.arange(58), np.arange(58)])**2).sum(-1)
    bad = np.where(np.abs(g - f) > 1e-3 * np.maximum(1, f))[0]
    print("max rel err", (np.abs(g - f) / f).max(), "bad orbitals", bad.tolist(), "occ", d["mo_occ"][k][bad].tolist())
    print("fft", f[bad].round(4).tolist()); print("gdf", g[bad].round(4).tolist())
