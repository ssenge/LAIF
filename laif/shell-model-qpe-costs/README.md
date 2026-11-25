# A smaller 1-norm for phase estimation of shell-model nuclei

2026-11-26

Fault-tolerant phase estimation for atomic nuclei was compiled in [1] for M-scheme shell-model Hamiltonians, with Toffoli and logical-qubit counts for ²⁴Mg (USDB interaction [2]), ³²Mg and ²¹⁹At. The walk operator queries a block encoding of H with 1-norm λ, so the number of walk steps grows linearly in λ. For ²⁴Mg with an energy error of 0.01 MeV, [1, Table I(a)] gives 1.07 × 10⁹ Toffoli gates at 608 logical qubits for phase estimation on the whole Hamiltonian.

## Results

| ²⁴Mg, USDB, ε = 0.01 MeV | Previous best bound [1] | Result |
|---|---|---|
| LCU 1-norm λ | 1849.97 MeV | 706.72 MeV |
| QROM entries d | 2224 | 2202 |
| Toffoli gates per walk step | 2041 | about 2189 |
| Walk steps, query count of [1, App. A] | 2¹⁹ | 2¹⁸ (error split x ∈ [0.307, 0.717]), 2¹⁷ (x ≥ 0.717) |
| Toffoli gates per phase estimation | 1.07 × 10⁹ at 608 qubits | 5.74 × 10⁸ (x ≤ 0.717), 2.87 × 10⁸ (x ≥ 0.717), at 616 qubits |

With a query count proportional to λ instead of the power of two of [1, App. A], the Toffoli count falls by a factor of 2.44.

**Theorem 4 (a second interaction).** For ³²Mg with the SDPF-MU interaction [6] (sd and pf shells for protons and neutrons, 64 orbitals, 4 valence protons and 12 valence neutrons), the encoding of [1] has λ = 20435.09 MeV with 45864 QROM entries, and the encoding of Theorem 2 has λ = 9124.82 MeV with 45832 entries, on the sector M = 0, J = 0, T = 4 of the ground state. This interaction is not the one of [1], so this compares the two encodings on the same Hamiltonian, not with a count of [1]. The sector is the standard one for the ground state of an even-even nucleus with N − Z = 8 and is not checked by diagonalization here.

*Which 1-norm.* The prepared state of [1, Eqs. (24), (25)] carries the weight ω² = 2 on every pair (pq) < (rs), and its normalization, like the per-block sums of [1, Table III], is λ = 1849.97 MeV, the baseline used here. The formula for λ printed below [1, Eq. (24)] sums over (pq) ≤ (rs) without ω² and gives 1091.34 MeV. If the counts of [1] were computed from that value, the gain over them is a factor of about 1.5 in the continuous form, and the power-of-two query counts can coincide. The same factors hold for the two other qubit counts of [1, Table I(a)] (1.09 × 10⁹ at 349 qubits and 1.36 × 10⁹ at 220 qubits).

**Theorem 1 (reproduction).** The M-scheme Hamiltonian built from the USDB matrix elements (with the mass scaling (A/18)^(−0.3) of the interaction file) has ground-state energies −40.4723 MeV for ²⁰Ne and −87.1044 MeV for ²⁴Mg, and its two-body term has exactly the numbers of nonzero elements per pair-M block of [1, Table III]. Summed over both orderings of the pair indices, the per-block 1-norms agree with [1, Table III] to 0.003 MeV, and with the one-body term the 1-norm of the block encoding of [1] is λ = 1849.97 MeV.

**Theorem 2 (1-norm).** For ²⁴Mg there is a block encoding of H − Σₖ cₖ (Sₖ − sₖ), with the operators Sₖ of the shift below and their values sₖ on the sector Z = 4, N = 4 valence nucleons, M = 0, J = 0, T = 0, with 1-norm 706.72 MeV and one QROM entry for each of 2182 two-body terms and 20 one-body Majorana monomials. Its lowest eigenvalue on that sector equals E₀(²⁴Mg) up to the known constant Σₖ cₖ sₖ.

**Estimate (cost per step).** In the circuit model described below, the encoding of Theorem 2 adds about 148 Toffoli gates and 8 qubits to a walk step of [1]. With twice that overhead the ratios in the table change by less than 7%.

## Construction

*Hermitian terms.* The block encoding of [1] prepares the terms a†_p a†_q a_s a_r and their adjoints as separate entries, so a hermitian pair W (a†_p a†_q a_s a_r + h.c.) contributes 2|W| to λ. Expanding the pair into Majorana monomials, a_p = (γ_{2p} + iγ_{2p+1})/2, gives eight Pauli strings of weight |W|/8 when the four indices are distinct, which is the standard Majorana form of a linear combination of unitaries [4]. A pair with one shared index splits into a length-two part, which is merged with the one-body term into a single one-body operator, and a length-four part of weight |W|/2; a diagonal term n_p n_q contributes |W|/4 through Z_p Z_q and merges its Z_p and Z_q parts into the one-body operator. The QROM keeps one entry per fermionic term; the term class follows from comparing the indices, and the Majorana choice within a term comes from a uniform superposition over 8, 2 or 1 choices. Without shifts this gives λ = 939.69 MeV.

*Symmetry shifts.* On the sector of the ground state, the operators N_p, N_n, N_p², N_n², N_p N_n, J_z, J_z², J² and T² take the values 4, 4, 16, 16, 16, 0, 0, 0 and 0. Subtracting cₖ (Sₖ − sₖ) leaves the spectrum on that sector unchanged up to a constant, in the spirit of the block-invariant symmetry shift of [5]. The 1-norm of the encoding is a convex piecewise-linear function of the coefficients cₖ, so its minimum is a linear program. Its solution has c(N_p) = c(N_n) = −3.988, c(N_p²) = c(N_n²) = −0.383, c(N_p N_n) = −0.810, c(J²) = −0.037 and c(T²) = 1.240 (J_z and J_z² do not change the minimum). Both J² and T² commute with H: on the ²⁴Mg target sector the largest entry of [H, J²] is below 10⁻¹² and that of [H, T²] below 10⁻⁸, the rounding of the interaction file. Exact diagonalization of the shifted operator on the whole sector Z = 4, N = 4, M = 0, which contains all J and T, gives E₀ as its lowest value.

*Cost per step.* The step cost of [1] is C_W = 1.07 × 10⁹ / 2¹⁹ = 2041 Toffoli gates. The exponent is 19, assuming that the 220-qubit row of [1, Table I(a)] reads its d = 2224 QROM entries without extra ancillae: such a read costs at least d Toffoli gates per step, and 1.36 × 10⁹ / 2²⁰ < 2224. An exponent of 18 would need x > 1. This gives x ≥ 0.307 for the error split of [1, App. A]. The estimate keeps the two-body select circuit of [1] and adds, on top of it, four selected Majorana operators by unary iteration (4 (N − 1) = 92 Toffoli gates for N = 24 orbitals), the index comparisons that give the term class (40) and the uniform superposition over the Majorana choices with its uncomputation (16). Signs and phases of the monomials are parities of the choice bits and the stored sign, which are Clifford operations. Replacing the select circuit of [1] instead of adding to it, and the smaller alias-sampling precision that a smaller λ allows, would lower the count further; neither is used above.

## A possible gap in the block-wise variant

The bold rows of [1, Table I] (9.52 × 10⁸ Toffoli gates for ²⁴Mg) apply phase estimation separately to the one-body term plus the two-body terms of a single pair-M block, and take the lowest output. The many-body Hamiltonian is the sum of all blocks, not a direct sum of them. For ²⁴Mg this hints at a possible gap: the minimum over pair-M blocks of the lowest eigenvalue of T + V_M is −54.61 MeV (block M = 0), while E₀ = −87.10 MeV. For two valence nucleons the block-wise minimum is exact, since H restricted to two-particle states is block diagonal in the pair M; from three nucleons on, the blocks act together. The comparison above therefore uses the rows of [1, Table I(a)] for the whole Hamiltonian.

## Scope

- The counts of [1] are taken from its tables and its cost model (App. A); the circuits of [1] are not recompiled. The bound per step is an upper bound in that model, not a compiled circuit.
- The shift is exact on the sector J = 0, T = 0 of the ²⁴Mg ground state; the initial state of phase estimation must lie in that sector, as for any symmetry-adapted estimate.
- The interaction files of ³²Mg (SDPF-U) and ²¹⁹At used in [1] are not part of the public interaction set used here; Theorem 4 uses SDPF-MU instead.
- For ³²Mg, J² and T² are checked to commute with H on all one- and two-particle sectors only.

## Files

- `sim/shell.py`: M-scheme Hamiltonian from a KSHELL interaction file, exact diagonalization.
- `sim/check_usdb.py`: Theorem 1.
- `sim/hybrid.py`: Theorem 2, with the linear program and the exact check of E₀ after the shift (`python hybrid.py ../data/usdb.snt 24 4 4 ed`).
- `sim/hybrid.py` with `../data/sdpf-mu.snt 32 4 12`: Theorem 4.
- `sim/cost.py`: the cost estimate and the Toffoli counts.
- `sim/approach2.py`: the block-wise lowest eigenvalues.
- The scripts read the matrix elements of USDB [2] and SDPF-MU [6] from the files `usdb.snt` and `sdpf-mu.snt` of the interaction set distributed with KSHELL [3], placed in `data/` (not included here).

## References

1. J. Benstead, M. Garn, N. Gaspar, S. Greenaway, A. Kan, L. La Ronde, C. Sarma, P. Stevenson. Fault-tolerant quantum algorithms for simulating atomic nuclei. arXiv:2607.21563 (2026).
2. B. A. Brown, W. A. Richter. New "USD" Hamiltonians for the sd shell. Phys. Rev. C 74, 034315 (2006).
3. N. Shimizu, T. Mizusaki, Y. Utsuno, Y. Tsunoda. Thick-restart block Lanczos method for large-scale shell-model calculations. Comput. Phys. Commun. 244, 372 (2019).
4. R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, H. Neven. Encoding electronic spectra in quantum circuits with linear T complexity. Phys. Rev. X 8, 041015 (2018).
5. I. Loaiza, A. F. Izmaylov. Block-invariant symmetry shift: preprocessing technique for second-quantized Hamiltonians to improve their decompositions to linear combination of unitaries. arXiv:2304.13772 (2023).
6. Y. Utsuno, T. Otsuka, B. A. Brown, M. Honma, T. Mizusaki, N. Shimizu. Phys. Rev. C 86, 051301(R) (2012).

## Use of AI

The constructions, checks and text were produced with Claude Opus 5.5.
