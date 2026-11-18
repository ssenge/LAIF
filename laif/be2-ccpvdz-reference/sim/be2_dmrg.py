"""All-electron Be2 / cc-pVDZ (8 electrons, 28 RHF orbitals) by spin-adapted DMRG with a forward bond-dimension schedule
up to Mmax and a reverse schedule without noise; the energy is extrapolated linearly in the discarded weight.
Usage: python -I be2_dmrg.py <R in Angstrom> <Mmax> [scratch dir]"""
import sys, os, numpy as np
from pyscf import gto, scf
from pyblock2._pyscf.ao2mo import integrals as itg
from pyblock2.driver.core import DMRGDriver, SymmetryTypes

R, Mmax = float(sys.argv[1]), int(sys.argv[2]); scratch = sys.argv[3] if len(sys.argv) > 3 else "./tmp_dmrg"
mol = gto.M(atom=f"Be 0 0 0; Be 0 0 {R}", basis="cc-pvdz", symmetry="d2h", verbose=0)
mf = scf.RHF(mol).run(conv_tol=1e-12); assert mf.converged
ncas, n_elec, spin, ecore, h1e, g2e, orb_sym = itg.get_rhf_integrals(mf, ncore=0, ncas=None, g2e_symm=1)
assert (ncas, n_elec, spin) == (28, 8, 0)
assert abs(ecore - mol.energy_nuc()) < 1e-10                       # all-electron: the core energy is nuclear repulsion only
driver = DMRGDriver(scratch=scratch, symm_type=SymmetryTypes.SU2, n_threads=1, stack_mem=4 << 30)
driver.initialize_system(n_sites=ncas, n_elec=n_elec, spin=spin, orb_sym=orb_sym)
idx = driver.orbital_reordering(h1e, g2e)
h1e = h1e[idx][:, idx]; g2e = g2e[idx][:, idx][:, :, idx][:, :, :, idx]; orb_sym = np.array(orb_sym)[idx]
driver.initialize_system(n_sites=ncas, n_elec=n_elec, spin=spin, orb_sym=orb_sym)
mpo = driver.get_qc_mpo(h1e=h1e, g2e=g2e, ecore=ecore, iprint=0)
ket = driver.get_random_mps(tag="KET", bond_dim=250, nroots=1)
fwd = [m for m in (250, 500, 1000, 2000, 3000, 4000) if m <= Mmax]
rev = sorted({m for m in (Mmax * 5 // 6, Mmax * 2 // 3, Mmax // 2, Mmax // 3) if m >= 100}, reverse=True)
bond_dims = sum([[m] * 4 for m in fwd], []) + sum([[m] * 2 for m in rev], [])
noises = sum([[1e-5] * 2 + [0.0] * 2 for m in fwd[:-1]], []) + [0.0] * 4 + [0.0] * (2 * len(rev))
thrds = [1e-9] * len(bond_dims)
e = driver.dmrg(mpo, ket, n_sweeps=len(bond_dims), bond_dims=bond_dims, noises=noises, thrds=thrds, tol=0, iprint=0)
E = np.array(driver._dmrg.sweep_energies)[:, 0]; DW = np.array(driver._dmrg.sweep_discarded_weights)
K = min(len(E), len(DW), len(bond_dims)); rows = []
print("sweep energies:", " ".join(f"{bond_dims[k]}:{E[k]:.8f}" for k in range(K)), flush=True)
for k in range(K):
    m = bond_dims[k]
    if k == K - 1 or bond_dims[k + 1] != m: rows.append((m, E[k], DW[k]))
print(f"R={R} RHF {mf.e_tot:.8f} E_nuc {mol.energy_nuc():.8f}")
for m, en, dw in rows: print(f"  M={m:5d}  E={en:.8f}  discarded weight={dw:.3e}")
nf = min(len(fwd), len(rows)); rv = [(dw, en) for m, en, dw in rows[nf:]] + [(rows[nf - 1][2], rows[nf - 1][1])]
if len(rv) >= 3:
    x, y = np.array(rv).T; A = np.vstack([x, np.ones_like(x)]).T; c, res, *_ = np.linalg.lstsq(A, y, rcond=None)
    print(f"R={R} extrapolated E(dw -> 0) = {c[1]:.8f}, |E(Mmax) - E_extrap| = {abs(rows[nf - 1][1] - c[1]):.2e}")
