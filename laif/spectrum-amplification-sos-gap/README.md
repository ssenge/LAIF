# A tighter certified sum-of-squares gap for spectrum amplification on Fe₂S₂

_22 November 2026_

Spectrum amplification [1] writes an electronic-structure Hamiltonian as H = Σ_α O_α† O_α + E_SOS with E_SOS a lower bound on its energy. The cost of phase estimation then depends on the gap E_gap = E_gs − E_SOS instead of the full spectral range, roughly as its square root. In [1, Table II] the bound E_SOS comes from a semidefinite program over the spin-free algebra {I, a_jσ, a_jσ†, E_ij} with E_ij = Σ_σ a_iσ† a_jσ, and it holds for every particle number. It was noted in [1] that tighter bounds could come from adding penalty or symmetry-shift operators to the sum of squares.

## Result

For the Fe₂S₂ cluster in the [30e, 20o] active space of [2], the same spin-free algebra with the electron-number terms (N̂ − 30)(y₀ + Σ_ab y_ab E_ab) added to the certificate gives a lower bound of −117.4458 Ha on every state with 30 electrons. Against the same DMRG energy, the gap falls from 0.976 Ha to 0.8403 Ha, 14% lower.

| Bound | Valid for | E_SOS (Ha) | E_gap against DMRG −116.60551 Ha (Ha) |
|---|---|---|---|
| Spin-free algebra [1, Table II] | all particle numbers | −117.582 | 0.976 |
| Spin-free algebra, recomputed here | all particle numbers | −117.5817 | 0.9762 |
| **Spin-free algebra with electron-number terms** | **30 electrons** | **−117.4458** | **0.8403** |

Previous best bound: E_gap = 0.976 Ha [1, Table II].

The recomputed bound over all particle numbers agrees with [1, Table II] to its printed digits, which also checks the Hamiltonian and the algebra used here. Both bounds are certified (below) and rounded down, and the gaps are rounded up. The DMRG energy is the upper bound of [1, Table II] for the same Hamiltonian, with no core energy.

The added terms vanish on every state with 30 electrons, so H − E_SOS remains a sum of squares on that sector, which is where phase estimation runs.

## Method

- **Hamiltonian.** H = Σ h_pq E_pq + ½ Σ (pq|rs) Σ_στ a_pσ† a_rτ† a_sτ a_qσ with the integrals of [2] (20 spatial orbitals, 30 electrons, core energy 0).
- **Certificate.** H − E = v† Z v + Σ P_ij E_ij + Σ Q_ij (2δ_ij − E_ji) + (N̂ − 30)(y₀ + Σ y_ab E_ab), with v = (I, E_ab), Z ⪰ 0 of size 401 and P, Q ⪰ 0 of size 20. The odd generators a_jσ, a_jσ† enter through P and Q. Their pairing and spin-mixing blocks can be dropped without loss, by averaging any certificate over the particle-number and spin symmetries of H. Both sides are matched operator by operator after normal ordering, which gives about 80 000 linear equalities, and E is maximized. Without the last term the program is the bound over all particle numbers.
- **Solver and rigour.** The program is solved by SCS on one CPU core (53 and 63 minutes). The solution is then turned into an exact identity: a least-squares correction of Z makes every coefficient match, with a remaining residual of at most 2.4 · 10⁻¹⁴ in operator norm, and diagonal shifts make Z, P and Q positive semidefinite. Each shift and residual is subtracted using ‖E_pq‖ ≤ 2, ‖Σ_στ a†a†aa‖ ≤ 4, ⟨v†v⟩ ≤ 1 + 4n² and ‖N̂‖ ≤ 2n, which costs at most 3.1 mHa, together with a further 10⁻⁶ Ha. The certified bound is therefore a true lower bound for any solver accuracy.

## Scope

- **Not computed.** The block-encoding cost of the new sum of squares, and its effect on the normalization λ_eff of [1, Table II]. Only E_gap is improved.
- **One system.** Fe₂S₂ [30e, 20o]. The other systems of [1, Table II] have 36 to 150 orbitals.
- **Not formalized.** The bounds are numerical certificates with the rigour stated above.
- **Checks.** `sim/sos_gap.py test` compares the operator expansions with explicit fermion matrices on the full Fock space of three orbitals, and checks on random Hamiltonians with Coulomb-like integrals that the certified bounds lie below the exact ground-state energies over all particle numbers and in fixed-electron sectors.

## Files

- `sim/sos_gap.py`: the program and the certificate (`python -I sos_gap.py FCIDUMP fock|N0 out.json`; `python -I sos_gap.py test`).
- `data/fe2s2_fock.json`, `data/fe2s2_30.json`: solver value, repaired value, residual and shift bounds, smallest eigenvalues and the certified bound. The integrals of [2] are in the repository named there (`Fe2S2_and_Fe4S4/Fe2S2/fe2s2`) and are not copied here.

## References

1. G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush, R. D. Somma, N. C. Rubin. Fast quantum simulation of electronic structure by spectrum amplification. arXiv:2502.15882.
2. Z. Li, G. K.-L. Chan. Spin-projected matrix product states: versatile tool for strongly correlated systems. Journal of Chemical Theory and Computation 13, 2681 (2017). Integrals: github.com/zhendongli2008/Active-space-model-for-Iron-Sulfur-Clusters.
3. B. O'Donoghue, E. Chu, N. Parikh, S. Boyd. Conic optimization via operator splitting and homogeneous self-dual embedding. Journal of Optimization Theory and Applications 169, 1042 (2016).
