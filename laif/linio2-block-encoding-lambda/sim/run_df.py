"""Rebuild the 3-index MO integrals for saved orbitals with a chosen density-fitting setup (no SCF), and check the
diagonal Q=0 integrals against the FFT reference at chosen k.
Usage: run_df.py in.npz out.npz variant [kcheck...]; variant in rs7, rs6, cc, jk"""
import sys, time, numpy as np
from pyscf.pbc import df, scf
import lno_cell, run_chol, fft_diag
src, out, var = sys.argv[1], sys.argv[2], sys.argv[3]
kc = [int(x) for x in sys.argv[4:]]
d = np.load(src, allow_pickle=True)
cell = lno_cell.r3m(); kpts = d["kpts"]
auxbasis = "def2-universal-jkfit" if var.startswith("jk") else None
mydf = df.GDF(cell, kpts, auxbasis=auxbasis) if auxbasis else df.GDF(cell, kpts)
if var in ("rs7", "jk7"):
    mydf.linear_dep_threshold = 1e-7
if var == "rs6":
    mydf.linear_dep_threshold = 1e-6
if var == "cc":
    mydf._prefer_ccdf = True
t0 = time.time(); mydf.build(); t1 = time.time()
class MF:  # minimal stand-in for run_chol.mo_chol
    pass
mf = MF(); mf.kpts, mf.mo_coeff, mf.with_df = kpts, list(d["mo_coeff"]), mydf
L = run_chol.mo_chol(mf)
for k in kc:
    f = fft_diag.fft_diag(cell, kpts[k], d["mo_coeff"][k])
    g = (np.abs(np.einsum("npp->np", L[k, k]))**2).sum(0)
    print(var, "k", k, "naux", L[k, k].shape[0], "max rel err diag", (np.abs(g - f) / f).max().round(4), "worst p", int(np.argmax(np.abs(g - f) / f)), flush=True)
np.savez(out, L=L, hcore=d["hcore"], kpts=kpts, mesh=d["mesh"], e_tot=d["e_tot"], e_nuc=d["e_nuc"], converged=d["converged"],
         nelec=d["nelec"], mo_coeff=d["mo_coeff"], mo_occ=d["mo_occ"], allow_pickle=True)
print("DONE", var, "t_df", round(t1 - t0), "t_mo", round(time.time() - t1))
