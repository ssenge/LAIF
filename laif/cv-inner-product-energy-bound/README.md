# Copy complexity of distributed inner product estimation for energy-constrained bosonic states

2026-11-21

## Problem

Two laboratories hold N copies each of unknown m-mode bosonic states ρ and σ from the energy-constrained class

C_{m,E} = {τ : Tr(Ê_m τ) ≤ mE},  Ê_m = ν̂_tot + m/2,

where ν̂_tot is the total photon number and E ≥ 1/2. Equivalently Tr(ν̂_tot τ) ≤ b with b = m(E − 1/2). With local operations and classical communication only, they must output Tr(ρσ) within additive error ε with failure probability at most δ, for every pair in the class. In [1], three protocols are given. The best of them, which truncates to photon numbers below L = ⌈4mE/ε⌉ in every mode and then runs the coordinated finite-dimensional protocol of [2], uses

O(log(2/δ) max{1/ε², (1 + 4mE/ε)^{m/2}/ε})

copies per party [1, Proposition 5]. No lower bound for the energy-constrained problem is given there, and the optimal worst-case copy complexity is named as an open question [1, Section V].

| | copies per party (constant δ) |
|---|---|
| Previous best bound | O(max{1/ε², (1 + 4mE/ε)^{m/2}/ε}) [1] |
| Previous lower bound | none stated for C_{m,E} |
| Theorem 1 (lower bound, any LOCC protocol) | Ω(((E − 1/2)/(100ε))^{m/2}/ε), and Ω(1/ε²) when b ≥ 1 |
| Theorem 2 (upper bound) | O(max{1/ε², (e + 4e(E − 1/2)/ε)^{m/2}/ε}) |

For fixed m and E ≥ 1/2 + 1/m the two bounds agree up to a factor C^m in the leading term: the optimal copy complexity is Θ(max{1/ε², ((E − 1/2)/ε)^{m/2}/ε}), with exponent max{2, m/2 + 1} for 1/ε and m/2 for E − 1/2.

## Results

**Theorem 1.** Let m ≥ 1, E > 1/2, b = m(E − 1/2) and 0 < ε ≤ min{b/100, 10⁻⁴}. Every protocol with local operations and classical communication (more generally, separable operations) that estimates Tr(ρσ) within ε with success probability at least 2/3 for all ρ, σ ∈ C_{m,E} uses at least

c ((E − 1/2)/(100ε))^{m/2} / ε

copies per party, for a universal constant c > 0. If b ≥ 1, it also uses at least c/ε² copies.

**Theorem 2.** Let N_c = max{1, ⌈4b/ε⌉} and D = C(N_c − 1 + m, m) + 2. Running the protocol of [1, Algorithm 2] with the projector onto total photon number at most N_c − 1 in place of the per-mode cutoff estimates Tr(ρσ) within ε with failure probability at most δ for all ρ, σ ∈ C_{m,E}, with

O(log(2/δ) max{1/ε², √D/ε}) copies per party,  D ≤ 2 + (e(1 + 4(E − 1/2)/ε))^m.

## Proofs

*Theorem 1.* Let K = ⌊b/(100ε)⌋ ≥ 1, and let H_K be the span of the photon-number states of total photon number between 1 and K. Its dimension is d = C(K + m, m) − 1. The hard instance of [2, Theorem 11] in dimension d + 1 uses states √(1 − ε₁) e^{iθ}|0⟩ + √ε₁ |φ⟩ with |φ⟩ ⊥ |0⟩ and ε₁ = 100ε. Identify |0⟩ with the vacuum and the orthogonal complement with H_K. Each such state then has Tr(ν̂_tot τ) ≤ ε₁K ≤ b, so it lies in C_{m,E}. A protocol for C_{m,E} restricted to these inputs is a protocol for the finite-dimensional problem. The reduction in the proof of [2, Theorem 12] turns an estimate within ε₁/100 = ε with success probability 0.99 into a solution of [2, Problem 1] with parameter ε₁ ≤ 0.01. Raising the success probability from 2/3 to 0.99 takes the median of a constant number of runs. So [2, Theorem 11] gives Ω(√d/ε₁) = Ω(√d/ε) copies. Since K ≥ 1, d ≥ C(K + m, m)/2, and

C(K + m, m) = Π_{j=1}^{m} (K + j)/j ≥ (1 + K/m)^m ≥ (b/(100 m ε))^m = ((E − 1/2)/(100ε))^m,

using K ≥ b/(100ε) − 1. For the second bound, the two states of [2, Lemma 13] lie in the span of |0⟩ and |1⟩ and have weight at most 1/2 + ε on |1⟩. Map |0⟩ to the vacuum and |1⟩ to one photon in the first mode. Their energy is then at most 1/2 + ε ≤ b, and the lemma gives Ω(1/ε²) even for joint measurements. ∎

*Theorem 2.* Let P be the projector onto total photon number at most N_c − 1, and Q = 1 − P. Any outcome in the range of Q has at least N_c photons, so the first-moment bound gives q_τ = Tr(Qτ) ≤ b/N_c ≤ ε/4 for every τ ∈ C_{m,E}. The bias bound of [1, Eq. (27)] is proved in [1, Appendix B] from this tail bound alone: ‖τ − PτP‖₂² ≤ 2q_τ, and the cross terms of Tr(ρσ) vanish. So |Tr(ρσ) − Tr(PρP PσP)| ≤ 2 max{q_ρ, q_σ} ≤ ε/2. The flag construction and the finite-dimensional protocol of [2, Theorem 6] in dimension D, run with accuracy ε/2, complete the proof exactly as in [1, Proposition 5]. For the dimension, C(n, m) ≤ (en/m)^m with n = N_c − 1 + m ≤ 4b/ε + m gives D ≤ 2 + (e(1 + 4(E − 1/2)/ε))^m. ∎

## Check

`sim/check.py` checks three things.

- **Counting bounds, in exact rational arithmetic, for m ≤ 8 and a grid of E and ε:** C(K + m, m) ≥ (1 + K/m)^m ≥ ((E − 1/2)/(100ε))^m, the bound on D, and b/N_c ≤ ε/4.
- **Hard states:** the instances of Theorem 1 satisfy the energy constraint, for m = 1, 2, 3 with random φ on H_K.
- **Bias bound:** the inequality |Tr(ρσ) − Tr(PρP PσP)| ≤ 2 max{q_ρ, q_σ} ≤ 2b/N_c holds for the total-photon projector. It is tested on random mixed states of the class with m ≤ 3, truncated at a finite total photon number.

## Scope

- Theorem 1 holds for every protocol with local operations and classical communication, shared randomness included. It does not separate coordinated from independent measurements, which [1] also names as an open question. The coordinated protocol of [1] attains the optimal exponents. The exponents of the parity and homodyne protocols of [1] are higher.
- The constants of Theorem 1 come from [2] and are not explicit. The constants of the two bounds differ by a factor C^m.
- [2, Theorem 11, Theorem 12, Lemma 13, Theorem 6] and the proof of [1, Proposition 5] are used as stated there. Not formalized in Lean.

## References

[1] K. Wang. Cross-platform verification of continuous-variable quantum systems. arXiv:2610.39912.

[2] A. Anshu, Z. Landau, Y. Liu. Distributed quantum inner product estimation. STOC 2022. arXiv:2111.03273.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
