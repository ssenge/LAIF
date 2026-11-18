"""RHF, all-electron CCSD(T) and frozen-core FCI (two lowest orbitals doubly occupied, 4 electrons in 26 orbitals) for
Be2 / cc-pVDZ at R = 2.555 and 2.564 Angstrom."""
from pyscf import gto, scf, cc, mcscf
for R in (2.555, 2.564):
    mol = gto.M(atom=f"Be 0 0 0; Be 0 0 {R}", basis="cc-pvdz", symmetry=True, verbose=0)
    mf = scf.RHF(mol).run(conv_tol=1e-12); assert mf.converged
    cas = mcscf.CASCI(mf, 26, 4); cas.fcisolver.conv_tol = 1e-10; efc = cas.kernel()[0]
    mycc = cc.CCSD(mf).run(); et = mycc.ccsd_t()
    print(f"R={R}: RHF {mf.e_tot:.8f}  CCSD(T) {mycc.e_tot + et:.8f}  frozen-core FCI {efc:.8f}", flush=True)
