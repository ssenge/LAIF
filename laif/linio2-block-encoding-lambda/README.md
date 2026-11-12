# Lower block-encoding cost for the LiNiO2 cathode Hamiltonian in Bloch orbitals

_12 November 2026_

The battery cathode material LiNiO2 is a benchmark for fault-tolerant quantum simulation of materials. In [1], its Hamiltonian in Bloch orbitals is block-encoded with a k-point double factorization (DF), and the cost of phase estimation is given in its Table VI. That cost grows with the normalization λ of the block encoding.

This folder lowers λ for the same Hamiltonian by two changes that keep the two-electron integrals:

1. **Gauge of the first factor.** At each momentum transfer Q, the DF vectors can be replaced by any other factor with the same Gram matrix: a unitary combination of them, or a real orthogonal one at Q = 0, where the vectors must stay Hermitian. The integrals do not change, but the two-body part of λ does. We start from a pivoted Cholesky factor and from the density-fitting factor itself, and we minimize the two-body λ over the unitary group.
2. **Symmetry shift at Q = 0.** Replace each Q = 0 vector L_n by L_n − c_n I and add (N_e − 1)/N_k · Σ_n c_n L_n − μ I to the one-body term. The result equals the original Hamiltonian, up to a constant, on every state with N_e electrons. This is the block-invariant symmetry shift of [2] in k-point form. Its λ is convex in (c, μ), and we minimize it.

We also give a certified floor. No block encoding of any Hamiltonian that agrees with H on the N_e-electron sector can have λ below half the spectral width of that sector, and two Slater determinants bound this width from below.

## Result

LiNiO2 in the R-3m structure, one formula unit, Γ point, 58 orbitals (116 spin-orbitals), 33 valence electrons. Each variant is compared at matched accuracy: it uses the largest second-factorization cutoff whose truncation error of the two-electron tensor (Frobenius norm) is at most that of the baseline at the cutoff 10⁻³ of [1]. Toffolis are from the DF cost model of [1], as implemented in OpenFermion, with phase-estimation error 1.6 mHa.

| Factorization | Cutoff | λ | Retained eigenvectors | Toffolis |
|---|---|---|---|---|
| Density-fitting vectors (previous best bound) | 1.0 · 10⁻³ | 558.3 | 18 241 | 3.42 · 10¹⁰ |
| With symmetry shift | 0.9 · 10⁻³ | 500.7 | 18 587 | 3.08 · 10¹⁰ |
| Optimized gauge | 0.9 · 10⁻³ | 452.0 | 17 263 | 2.74 · 10¹⁰ |
| Optimized gauge and symmetry shift | 0.9 · 10⁻³ | **407.7** | 17 332 | **2.47 · 10¹⁰** |
| Certified floor for any block encoding | | 136.9 | | |

Together the two changes lower λ by 27% and the Toffoli count by a factor of 1.38. Without truncation, the gauge lowers the two-body part from 410.9 to 304.6, and the shift mostly lowers the one-body part, from 148.8 to 99.8. The floor leaves room for at most a further factor of 3.0 in λ for any method that keeps the Hamiltonian on the sector.

For scale: the smallest system in Table VI of [1], the P2/c structure at the Γ point with four formula units, has λ = 2753.9, about 690 per formula unit.

## The floor

For any block encoding of a Hamiltonian H′ that agrees with H on the N_e-electron sector, λ ≥ min_c ‖H′ − c‖ ≥ (E_max − E_min)/2, with E_max and E_min the extreme energies of H on the sector. Any two determinants Φ_hi and Φ_lo in the sector satisfy E_max ≥ E(Φ_hi) and E_min ≤ E(Φ_lo). We take Φ_lo from aufbau and Φ_hi from anti-aufbau self-consistent iterations (spin-unrestricted, 17 α and 16 β electrons): E(Φ_hi) − E(Φ_lo) = 187.32 − (−86.42) = 273.75 Ha, so λ ≥ 136.9.

## Setup

- **Structure:** R-3m with a = 2.8783 Å, c = 14.190 Å and oxygen at z = 0.2586 in the hexagonal setting, rhombohedral primitive cell (33.94 Å³).
- **Basis and pseudopotentials:** DZVP-MOLOPT (UZH set, 58 functions per formula unit as in [1]) and the GTH pseudopotentials optimized for Hartree-Fock.
- **Orbitals:** canonical orbitals of a restricted open-shell Hartree-Fock calculation. λ does not depend on this choice, since every reduction here is invariant under unitary changes of the orbitals at each k.
- **Integrals:** Gaussian density fitting with an even-tempered auxiliary basis, built with the compensated-charge (CC) GDF builder of PySCF. All 58 diagonal Coulomb integrals at the Γ point agree with a plane-wave FFT reference (mesh 145³) to 0.15%. With the range-separated GDF builder and default settings, some virtual-space integrals of this cell differ from the reference by up to a factor of three, and λ then comes out higher.
- **λ:** the formula of [1, Eqs. (50) and (53)]. `sim/dflam.py` agrees with the OpenFermion implementation to 10⁻⁹ in relative terms, and in the number of retained eigenvectors, on diamond at three cutoffs.

## Status and checks

Numerical. The checks:

- The shift identity: the shifted and original Hamiltonians agree on every N_e sector up to a constant, by exact diagonalization in Fock space for random k-point tensors (`sim/test_dflam.py`, N_k = 1 and 2).
- The gauge: every two-electron block is unchanged, to the pivoted Cholesky tolerance 10⁻⁸, and the λ terms add up to the λ of the transformed factor (`sim/test_rot.py`, diamond on a 1 × 1 × 3 mesh, where it lowers λ from 179.6 to 153.1).
- The floor: determinant energies agree with exact expectation values in Fock space (`sim/test_floor.py`).
- Matched truncation error: `sim/matched.py`.

## Not covered

- k-point meshes beyond Γ and the distorted structures of [1].
- The tensor hypercontraction and sparse block encodings of [1].
- Reductions that change the integrals, such as compressed and regularized factorizations [3], and joint optimization of shifts and factors as done for molecules in [4].

## Files

- `sim/lno_cell.py`, `sim/run_chol.py`, `sim/run_df.py`: the cell, the mean-field orbitals and the 3-index integrals.
- `sim/dflam.py`: λ and the symmetry shift. `sim/opt_shift.py`: the optimal shift. `sim/rot_kpt.py`: the gauge optimization.
- `sim/stack.py`, `sim/matched.py`, `sim/trunc_err.py`: the tables (`data/gamma_stack.jsonl`, `data/gamma_matched.jsonl`).
- `sim/floor_k.py`: the floor (`data/gamma_floor.json`).
- `sim/fft_diag.py`, `sim/fft_pair.py`: the FFT reference for the integrals.

## References

1. N. C. Rubin, D. W. Berry, F. D. Malone, A. F. White, T. Khattar, A. E. DePrince III, S. Sicolo, M. Kühn, M. Kaicher, J. Lee, R. Babbush. Fault-tolerant quantum simulation of materials using Bloch orbitals. PRX Quantum 4, 040303 (2023). arXiv:2302.05531.
2. I. Loaiza, A. F. Izmaylov. Block-invariant symmetry shift: preprocessing technique for second-quantized Hamiltonians to improve their decompositions to linear combination of unitaries. arXiv:2304.13772.
3. O. Oumarou, M. Scheurer, R. M. Parrish, E. G. Hohenstein, C. Gogolin. Accelerating quantum computations of chemistry through regularized compressed double factorization. Quantum 8, 1371 (2024). arXiv:2212.07957.
4. K. Deka, E. Zak. Simultaneously optimizing symmetry shifts and tensor factorizations for cost-efficient fault-tolerant quantum simulations of electronic Hamiltonians. arXiv:2412.01338.
