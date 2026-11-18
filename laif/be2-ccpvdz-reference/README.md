# Converged reference energy for the Be₂/cc-pVDZ benchmark of variable-geometry sample-based quantum diagonalization

_18 November 2026_

In [1], variable-geometry sample-based quantum diagonalization (VGSQD) on an IBM Heron r2 processor gives the equilibrium energy of the beryllium dimer in the cc-pVDZ basis as −29.2356 Ha at R = 2.555 Å. The reference values of [1, Table 4], computed with all electrons correlated (8 electrons in 28 orbitals), are RHF −29.1346, CCSD(T) −29.2345 and DMRG −29.2352 Ha at R = 2.564 Å, the DMRG with bond dimension M = 1000.

## Result

On the same Hamiltonian, a spin-adapted DMRG with all electrons correlated converges to

| R (Å) | DMRG energy (Ha) | change from M = 250 to M = 2000 | discarded weight at M = 2000 |
|---|---|---|---|
| 2.555 | −29.2356098 | below 10⁻⁷ | 5 · 10⁻¹⁷ |
| 2.564 | −29.2356085 | below 10⁻⁷ | 6 · 10⁻¹⁷ |

The final sweeps carry no noise, so these are variational upper bounds on the exact energy. At R = 2.564 Å, the variational DMRG upper bound on the same Hamiltonian lies 0.41 mHa below the reference value −29.2352 of [1]. The reported VGSQD energy −29.2356 at R = 2.555 Å agrees with the converged value to its printed digits.

The Hamiltonian is the one of [1]: RHF −29.13462925 and CCSD(T) −29.23454603 at R = 2.564 Å match [1, Table 4] to all printed digits. With the two lowest orbitals frozen, full CI gives −29.2343, so the value of [1] belongs to the all-electron problem.

Selected configuration interaction, a second variational method, approaches the DMRG value from above at R = 2.555 Å: −29.234282, −29.235468, −29.235588 and −29.235603 Ha for selection cutoffs 10⁻³, 3 · 10⁻⁴, 10⁻⁴ and 4 · 10⁻⁵.

## Scope

- DMRG uses the block2 package with SU(2) symmetry, a Fiedler orbital order, a forward schedule M = 250, 500, 1000, 2000 with decreasing noise and a reverse schedule M = 1666 to 666 without noise. Larger M was not run. A DMRG run is variational but can stop in a local minimum, so the values are upper bounds; one run from another random start stopped 0.03 mHa higher at M ≤ 500.
- The comparison concerns the cc-pVDZ basis. The cc-pVTZ values of [1] are not recomputed here.

## Files

- `sim/be2_ref.py`: RHF, CCSD(T) and frozen-core full CI at both geometries (`data/be2_ref.txt`).
- `sim/be2_dmrg.py`: the DMRG with the bond-dimension schedule and the discarded-weight extrapolation (`data/be2_dmrg_2.555.txt`, `data/be2_dmrg_2.564.txt`).
- `sim/be2_sci.py`: the selected CI (`data/be2_sci.txt`).

## References

1. M. Fortin-Deschenes, I. Shehzad. Sample-based quantum diagonalization for variable molecular geometries. arXiv:2610.38701.
