"""LiNiO2 R-3m primitive cell (one formula unit) in PySCF, GTH-DZVP (UZH MOLOPT) with HF pseudopotentials."""
import os
import numpy as np
from pyscf.pbc import gto
from pyscf.gto.basis import parse_cp2k
import pyscf.pbc.gto.basis as pb

_UZH = os.path.join(os.path.dirname(pb.__file__), "BASIS_MOLOPT_UZH")

def _seg(name):
    txt = open(_UZH).read()
    lines = txt[txt.index("\n" + name) + 1:].split("\n")
    out = [lines[0]]
    for l in lines[1:]:
        if l and l[0].isalpha():
            break
        out.append(l)
    return parse_cp2k.parse("\n".join(out))

def dzvp(fam="PBE0"):
    return {s: _seg(f"{s} DZVP-MOLOPT-{fam}-GTH-q{q}") for s, q in [("Ni", 18), ("Li", 3), ("O", 6)]}

def r3m(a=2.8783, c=14.190, zO=0.2586, basis=None, verbose=0):
    s3 = np.sqrt(3.0)
    cell = gto.Cell()
    cell.a = np.array([[a/2, -a/(2*s3), c/3], [0, a/s3, c/3], [-a/2, -a/(2*s3), c/3]])
    cell.atom = [["Ni", (0, 0, 0)], ["Li", (0, 0, c/2)], ["O", (0, 0, zO*c)], ["O", (0, 0, -zO*c)]]
    cell.basis = basis or dzvp()
    cell.pseudo = "gth-hf-rev"
    cell.unit, cell.verbose, cell.spin = "A", verbose, 1
    cell.build()
    return cell

if __name__ == "__main__":
    c = r3m()
    assert c.nao_nr() == 58, c.nao_nr()
    assert c.nelectron == 33, c.nelectron
    print("nao", c.nao_nr(), "nelec", c.nelectron, "vol A^3", c.vol * 0.529177**3)
