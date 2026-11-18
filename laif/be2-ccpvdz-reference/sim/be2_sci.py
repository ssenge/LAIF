"""Independent variational check: selected CI (PySCF SCI) for all-electron Be2 / cc-pVDZ (8 electrons, 28 RHF orbitals).
Usage: python -I be2_sci.py <R in Angstrom> <selection cutoff>"""
import sys, time
from pyscf import gto, scf, fci, ao2mo
R = float(sys.argv[1]); cut = float(sys.argv[2])
mol = gto.M(atom=f"Be 0 0 0; Be 0 0 {R}", basis="cc-pvdz", verbose=0); mf = scf.RHF(mol).run(conv_tol=1e-12)
h1 = mf.mo_coeff.T @ mf.get_hcore() @ mf.mo_coeff; g2 = ao2mo.full(mol, mf.mo_coeff)
s = fci.SCI(mol); s.select_cutoff = cut; s.ci_coeff_cutoff = cut; s.conv_tol = 1e-10
t = time.time(); e, c = s.kernel(h1, g2, 28, 8, ecore=mol.energy_nuc())
print(f"R={R} SCI cutoff {cut}: E = {e:.8f} ({time.time() - t:.0f} s, {c.shape[0]} x {c.shape[1]} strings)", flush=True)
