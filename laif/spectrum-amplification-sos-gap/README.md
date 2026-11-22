# A tighter certified sum-of-squares gap for spectrum amplification on Fe₂S₂

_22 November 2026_

Spectrum amplification [1] writes the electronic-structure energy operator H as H = Σ_α O_α† O_α + E_SOS with E_SOS a lower bound on its energy. The cost of phase estimation then depends on the gap E_gap = E_gs − E_SOS instead of the full spectral range, roughly as its square root. In [1, Table II] the bound E_SOS comes from a semidefinite program over the spin-free algebra {I, a_jσ, a_jσ†, E_ij} with E_ij = Σ_σ a_iσ† a_jσ. It is taken over the space of all occupation numbers, that is, over every particle number at once. It was noted in [1] that this lower bound could be tightened by adding penalty or symmetry-shift operators to the sum of squares.

## Result

For the Fe₂S₂ cluster in the [30e, 20o] active space of [2], the same spin-free algebra with the electron-number terms (N̂ − 30)(y₀ + Σ_ab y_ab E_ab) added to the certificate gives a lower bound of −117.4458 Ha on every state with 30 electrons. Against the same DMRG energy, the gap falls from 0.976 Ha to 0.8403 Ha, 14% lower.

| Bound | Valid for | E_SOS (Ha) | E_gap against DMRG −116.60551 Ha (Ha) |
|---|---|---|---|
| Spin-free algebra [1, Table II] | all particle numbers | −117.582 | 0.976 |
| Spin-free algebra, recomputed here | all particle numbers | −117.5817 | 0.9762 |
| **Spin-free algebra with electron-number terms** | **30 electrons** | **−117.4458** | **0.8403** |

Previous best bound: E_gap = 0.976 Ha [1, Table II].

The recomputed bound over all particle numbers agrees with [1, Table II] to its printed digits, which also checks the energy operator and the algebra used here. Both bounds are certified (below) and rounded down, and the gaps are rounded up. The DMRG energy is the upper bound of [1, Table II] for the same energy operator, with no core energy.

The added terms vanish on every state with 30 electrons, so H − E_SOS remains a sum of squares on that sector, which is where phase estimation runs.

The resource estimates of [1, Table V] use a different object: a compressed factorization of the two-electron integrals (DFTHC) that already includes a symmetry shift, with E_gap = 1.2381 Ha, Λ = 17.53 Ha and λ_eff = 6.469 Ha for this system. That gap belongs to one explicit factorization chosen for a cheap block-encoding. The gaps in the table above are the smallest values reachable by any sum of squares over the spin-free algebra, without and with the electron-number terms. They bound from below the gap any such factorization can reach on the 30-electron sector. A factorization with a gap near 0.8403 Ha and a block-encoding cost close to that of [1, Table V] has not been constructed here.

## Block-encoding cost

The number of walk steps in phase estimation is proportional to λ_eff = √(E_gap (2Λ − E_gap)) [1, Eq. (11)], with Λ = λ_sqrt²/2 and λ_sqrt² = Σ_α λ_α² the sum of the squared normalizations of the block-encodings of the operators O_α. Both certificates are factorized here in the same way. The eigenvectors of Z = Σ_α μ_α u_α u_αᵀ give O_α = √μ_α (u_0 I + Σ_ab g_ab E_ab) with λ_α = √μ_α (|u_0| + 2‖g‖_*), where ‖g‖_* is the sum of the singular values of g, and the terms with P and Q add twice the sum of their eigenvalues.

| Certificate | E_gap (Ha) | Λ (Ha) | λ_eff (Ha) |
|---|---|---|---|
| All particle numbers | 0.9762 | 433.24 | 29.07 |
| 30 electrons | 0.8403 | 106.57 | 13.36 |

With this factorization the certificate on the 30-electron sector has a Λ about 4 times smaller and a λ_eff about 2.2 times smaller, so the smaller gap comes with a smaller normalization as well. For its own sum of squares, the compressed factorization of [1, Table V] reaches λ_eff = 6.469 Ha. Values are rounded up.

## Method

- **Energy operator.** H = Σ h_pq E_pq + ½ Σ (pq|rs) Σ_στ a_pσ† a_rτ† a_sτ a_qσ with the integrals of [2] (20 spatial orbitals, 30 electrons, core energy 0).
- **Certificate.** H − E = v† Z v + Σ P_ij E_ij + Σ Q_ij (2δ_ij − E_ji) + (N̂ − 30)(y₀ + Σ y_ab E_ab), with v = (I, E_ab), Z ⪰ 0 of size 401 and P, Q ⪰ 0 of size 20. The odd generators a_jσ, a_jσ† enter through P and Q. Their pairing and spin-mixing blocks can be dropped without loss, by averaging any certificate over the particle-number and spin symmetries of H. Both sides are matched operator by operator after normal ordering, which gives about 80 000 linear equalities, and E is maximized. Without the last term the program is the bound over all particle numbers.
- **Solver and rigour.** The program is solved by SCS on one CPU core (54 and 64 minutes). The solution is then turned into an exact identity: a least-squares correction of Z makes every coefficient match, with a remaining residual of at most 2.4 · 10⁻¹⁴ in operator norm, and diagonal shifts make Z, P and Q positive semidefinite. Each shift and residual is subtracted using ‖E_pq‖ ≤ 2, ‖Σ_στ a†a†aa‖ ≤ 4, ⟨v†v⟩ ≤ 1 + 4n² and ‖N̂‖ ≤ 2n, which costs at most 3.1 mHa, together with a further 10⁻⁶ Ha. The certified bound is therefore a true lower bound for any solver accuracy.

## Scope

- **Not computed.** A compressed factorization of the certificates here, such as that of [1, Table V], and the Toffoli cost of their block-encodings.
- **One system.** Fe₂S₂ [30e, 20o]. The other systems of [1, Table II] have 36 to 150 orbitals.
- **Not formalized.** The bounds are numerical certificates with the rigour stated above.
- **Checks.** `sim/sos_gap.py test` compares the operator expansions with explicit fermion matrices on the space of all occupation numbers of three orbitals, and checks on random energy operators with Coulomb-like integrals that the certified bounds lie below the exact ground-state energies over all particle numbers and in fixed-electron sectors, and that the norm of each sum of squares is at most 2Λ.

## Files

- `sim/sos_gap.py`: the program and the certificate (`python -I sos_gap.py FCIDUMP fock|N0 out.json`; `python -I sos_gap.py check FCIDUMP fock|N0 cert.npz` re-certifies a saved certificate without the solver; `python -I sos_gap.py test`).
- `data/fe2s2_fock.json`, `data/fe2s2_30.json`: solver value, repaired value, residual and shift bounds, smallest eigenvalues, the certified bound and Λ. A solver run also writes the matrices Z, P, Q and the coefficients y of the certificate to `out.npz` beside `out.json`, and the check mode re-certifies the bound from that file. The integrals of [2] are in the repository named there (`Fe2S2_and_Fe4S4/Fe2S2/fe2s2`) and are not copied here.

## References

1. G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush, R. D. Somma, N. C. Rubin. Fast quantum simulation of electronic structure by spectrum amplification. arXiv:2502.15882.
2. Z. Li, G. K.-L. Chan. Spin-projected matrix product states: versatile tool for strongly correlated systems. Journal of Chemical Theory and Computation 13, 2681 (2017). Integrals: github.com/zhendongli2008/Active-space-model-for-Iron-Sulfur-Clusters.
3. B. O'Donoghue, E. Chu, N. Parikh, S. Boyd. Conic optimization via operator splitting and homogeneous self-dual embedding. Journal of Optimization Theory and Applications 169, 1042 (2016).
