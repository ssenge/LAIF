# Robust shadow tomography with few observables: random linear combinations

2026-11-12

## Problem

In shadow tomography one estimates tr(O_i ρ) for observables O_1, …, O_M with ‖O_i‖_op ≤ 1 from copies of an unknown state ρ of dimension d. In the adversarial model of [1, Definition 1.1], each copy is measured on its own with a measurement fixed in advance (non-adaptive). An adversary then changes a γ-fraction of the outcomes, knowing the measurement scheme and, as in [1, Remark 2.3], even the random choices behind it. The question is how small the error can be made, even with unlimited copies.

In [1] it is shown that some family of observables forces error Ω̃(γ min{√M, √d}) [1, Theorem 1.2]. Classical shadows with a truncated mean reach O(γ log(1/γ) max_i ‖O_i‖_HS) with O(log(M/δ)/γ²) copies [1, Theorem 1.4], and measuring each observable directly gives O(γM). For M ≥ d this matches the lower bound up to logarithms. For M < d the bounds are γ√M from below and γ√d from above, even on the family that proves the lower bound.

## Results

For a family O = (O_1, …, O_M) let

κ(O) = sup_ψ ( Σ_i ⟨ψ|O_i|ψ⟩² )^{1/2} = sup_{‖a‖₂ = 1} ‖Σ_i a_i O_i‖_op,   δ(O) = min_π max_ψ E_{i∼π} ⟨ψ|O_i|ψ⟩²,

with ψ over unit vectors and π over distributions on {1, …, M}. Then max_i ‖O_i‖_op ≤ κ ≤ √M and δ ≤ κ²/M. For Pauli observables, δ is the quantity that governs shadow tomography without corruption in [2, Theorem 3].

**Theorem 1.** The random-combination scheme below estimates every tr(O_i ρ) to error

O( γ κ(O) √(M log(1/γ)) )

with probability at least 1 − δ from O(log(M/δ)/γ²) copies, under γ-corruption of the records (outcomes and random choices). Splitting the copies between this scheme and that of [1] gives error Õ(γ min{κ√M, max_i ‖O_i‖_HS}).

**Proposition 2 (lower bound, implied by the proof of [1, Theorem 1.2]).** Let the O_i be traceless with ‖O_i‖_op ≤ 1. Every non-adaptive single-copy algorithm that reaches error ε with probability 0.8 under γ-corruption, with any number of copies, has

ε ≥ min{ 1/3, γ/(3√(2δ(O))) } ≥ min{ 1/3, γ√M/(3√2 κ(O)) }.

So for every family the best error lies between Ω(γ√M/κ) and O(γκ√(M log(1/γ))), a range of width κ²√log(1/γ).

**Corollary 3.**

- (a) *The family of [1, Theorem 1.2].* For the observables O_i = U_i†ZU_i of [1, Lemma 5.4], with Z diagonal with entries ±1 and U_i uniformly random unitaries, and 2 ≤ M ≤ d, the bound of [1, Lemma 5.4] gives κ² ≤ 2304π³ ln(1 + 2M) + 4 + M/(d + 1) = O(log M). The error is O(γ√(M log M · log(1/γ))), and the lower bound on this family is Ω(γ√(M/log M)). The optimal error on the family behind the lower bound of [1] is therefore Θ̃(γ√M), against the previous O(γ log(1/γ)√d).
- (b) *Anticommuting observables.* If O_i² = I and the O_i anticommute pairwise, as for Pauli observables such as the 2n fermionic mode operators on n qubits, then (Σ a_i O_i)² = ‖a‖² I and κ = 1. The error is O(γ√(M log(1/γ))), and the lower bound is γ√M/(3√2). Previous best bound: min{O(γM), O(γ log(1/γ)√d)}.

Whether γ√M can be reached for every family with M < d stays open. Commuting families can have κ = √M, but those are easy to measure jointly.

## Algorithm

For each copy, draw a uniformly from the unit sphere in R^M, measure ρ in an eigenbasis of A_a = Σ_i a_i O_i, and record the eigenvalue λ. For each i, set X_i = M a_i λ. The estimate of tr(O_i ρ) is the truncated mean of the X_i: drop the largest and the smallest 2γ-fraction of the values and average the rest [1, Algorithm 1].

## Proof

*Mean.* Given a, E[λ] = tr(A_a ρ) = Σ_j a_j tr(O_j ρ). Since E[a aᵀ] = I/M, E[X_i] = M Σ_j E[a_i a_j] tr(O_j ρ) = tr(O_i ρ).

*Moments.* |λ| ≤ ‖A_a‖_op ≤ κ. For a uniform on the sphere, E[a_i^{2k}] = (2k − 1)!!/(M(M + 2)⋯(M + 2k − 2)) ≤ (2k/M)^k. So (E|X_i|^h)^{1/h} ≤ Mκ (E a_i^{2h})^{1/(2h)} ≤ κ√(2hM), and with |tr(O_i ρ)| ≤ κ, (E|X_i − tr(O_i ρ)|^h)^{1/h} ≤ 2κ√(hM) for h, M ≥ 2.

*Robust mean.* The truncated mean of γ-corrupted samples of a variable whose central h-th moment is at most σ^h has error O(σγ^{1−1/h}) with probability 1 − δ′ from O(log(1/δ′)/γ²) samples [1, Theorem 2.4]. A corrupted record (a, λ) gives arbitrary values X_i, which this covers. Take h = max{2, ⌈ln(1/γ)⌉}, so that γ^{−1/h} ≤ e, and δ′ = δ/M with a union bound over i. This gives Theorem 1. For the combination, each half of the copies holds at most a 2γ-fraction of corrupted records.

*Proposition 2.* Follow [1, Section 5.1] with i drawn from a distribution π in place of the uniform one. An algorithm with error ε ≤ 1/3 separates ρ = I/d from σ_i = (I + 3εO_i)/d with i ∼ π. For a rank-one measurement {d w_x |ψ_x⟩⟨ψ_x|} the divergence of the second moment is 9ε² Σ_x w_x ⟨ψ_x|O_i|ψ_x⟩². Averaging over i ∼ π and using the inequality between total variation and this divergence as in [1, (9) to (11)], the expected total variation per copy is at most (3ε/√2)(max_ψ E_{i∼π}⟨ψ|O_i|ψ⟩²)^{1/2}. By [1, Lemmas 5.2 and 5.3], separation fails when this is at most γ/2. Minimizing over π gives the bound.

*Corollary 3.* (a) [1, Lemma 5.4] bounds (1/M) Σ_i ⟨ψ|O_i|ψ⟩² by 2304π³ log(1 + 2 min{M, d})/min{M, d} + 4/min{M, d} + 1/(d + 1) for every unit ψ. Multiply by M. (b) A_a² = Σ_i a_i² I, since the cross terms cancel.

## Check

`sim/robust.py` runs the scheme on four random observables U†ZU in dimension 128 and on ten anticommuting Pauli observables on five qubits, with a random pure state and 8000 copies. It checks with asserts:

- that the X_i are unbiased;
- the moment bound for h = 2, 4 and 6, with κ replaced by the largest sampled ‖A_a‖_op;
- that, under an attack that moves a γ-fraction of the samples to just inside the trimming boundary, the error divided by γ√(M ln(1/γ))·κ stays at most 2;
- that for γ ≥ 0.02 this error is below that of classical shadows with the truncated mean under the same attack.

| family | γ = 0.01 | γ = 0.02 | γ = 0.05 |
|---|---|---|---|
| random, d = 128, M = 4: combination / classical shadows | 0.087 / 0.274 | 0.121 / 0.454 | 0.205 / 0.927 |
| anticommuting, d = 32, M = 10: combination / classical shadows | 0.085 / 0.259 | 0.148 / 0.342 | 0.278 / 0.576 |

Output in `sim/robust_out.txt`.

## Scope

- **Assuming:** the guarantee of the truncated mean [1, Theorem 2.4], and [1, Lemmas 5.2, 5.3 and 5.4] for Proposition 2 and Corollary 3 (a).
- **Not formalized:** the results have no Lean proof.
- The model is non-adaptive, as in [1]; adaptive schemes are not covered by Proposition 2. κ(O) can be hard to compute, and any upper bound on it can be used in Theorem 1.
- The simulation tests one attack, not the worst case.

## References

[1] M. Aliakbarpour, V. Braverman, N.-H. Chia, C.-Y. Lin, Y. Liu, A. Oufkir, Y.-C. Shen. Shadow tomography against adversaries. arXiv:2512.05451.

[2] S. Chen, W. Gong, Q. Ye. Optimal tradeoffs for estimating Pauli observables. arXiv:2404.19105.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
