# Quantum state identity testing for every ε < 1/2

2026-11-21

## Problem

Given copies of n ≥ 2 unknown pure states |ψ_1⟩, …, |ψ_n⟩ of any dimension d ≥ 2 and ε ∈ [0, 1/2), decide whether |⟨ψ_i|ψ_j⟩|² ≥ 1 − ε for all pairs i ≠ j (yes) or |⟨ψ_a|ψ_b⟩|² ≤ ε for some pair (no), with error at most δ on both sides [1, Definition 1.1]. The cost is the number m of copies of each state. The problem with an approximate promise on both sides was proposed in [4].

Previous best bounds [1]: for ε ∈ (0, 1/4), O(log(n/δ)/γ²) copies with γ = 1/2 − √ε, and lower bounds log(1/(4δ(1 − δ)))/log(1/ε) and, for δ ≤ 1/2 − c, Ω(log n/log(4/ε)) [1, Theorem 5.2, Corollary 5.5, Theorem 5.6], so Θ(log(n/δ)) for fixed ε. Whether comparable algorithms exist for ε ∈ [1/4, 1/2), and the optimal dependence on ε, are stated open in [1, Section 1.2].

## Results

**Theorem 1 (implied by [2, Corollary A.4]).** For every ε ∈ [0, 1/2), δ ∈ (0, 1/2), n ≥ 2 and d ≥ 2,

m = O(log(n/δ)/(1 − 2ε)²)

copies of each state suffice. The test is one two-outcome projective measurement on (ψ_1 ⊗ … ⊗ ψ_n)^{⊗m}, and m does not depend on d.

**Theorem 2.** For every n ≥ 2, ε ∈ (0, 1/2) and δ ∈ (0, 1/2), every test with error at most δ uses

m ≥ log(1/(4δ(1 − δ))) / log(1/(4ε(1 − ε))) ≥ 4ε(1 − ε) · log(1/(4δ(1 − δ))) / (1 − 2ε)²

copies of each state. The denominator log(1/(4ε(1 − ε))) replaces log(1/ε) in [1, Theorem 5.2]; it tends to 0 as ε → 1/2.

So for fixed n, δ ≤ 1/3 and ε ∈ [1/4, 1/2) the copy complexity is Θ(log(1/δ)/(1 − 2ε)²), and for fixed ε ∈ (0, 1/2) and δ ≤ 1/2 − c it is Θ(log(n/δ)): the argument of [1, Theorem 5.1 and Corollary 5.5] holds for every ε < 1/2 and gives m ≥ log(1 + 4n(1 − 2δ)²)/log(4/ε − 3). Since 1 − 2ε ≥ 1 − 2√ε = 2γ, Theorem 1 is at most a constant factor above the bound of [1] for every ε < 1/4, and below it by the factor (1 − 2ε)²/(1 − 2√ε)², which grows without bound as ε → 1/4.

## Proofs

*Theorem 1.* Let ρ = ψ_1 ⊗ … ⊗ ψ_n, and for i < j let A_ij = (1 − SWAP_ij)/2 be the projector onto the antisymmetric subspace of registers i and j, tensored with the identity elsewhere. Then tr(A_ij ρ) = (1 − |⟨ψ_i|ψ_j⟩|²)/2. In a no instance some tr(A_ab ρ) ≥ (1 − ε)/2 > 1/4. In a yes instance every tr(A_ij ρ) ≤ ε/2 = 1/4 − (1 − 2ε)/4. The decision version of threshold search [2, Corollary A.4], applied to the m₀ = n(n − 1)/2 events A_ij with all thresholds 1/4 and slack (1 − 2ε)/4, separates the two cases with error δ using O(log(m₀/δ)/(1 − 2ε)²) = O(log(n/δ)/(1 − 2ε)²) copies of ρ. One copy of ρ uses one copy of each state. ∎

*Theorem 2.* Let |ψ_1⟩ = … = |ψ_{n−1}⟩ = |0⟩ and |ψ_n⟩ = |φ_F⟩ = √F|0⟩ + √(1 − F)|1⟩. With F = 1 − ε every pair has fidelity 1 or 1 − ε, a yes instance. With F = ε the pair (1, n) has fidelity ε, a no instance. A test with error at most δ on both distinguishes |φ_{1−ε}⟩^{⊗m} from |φ_ε⟩^{⊗m}, with the other registers fixed, with average error at most δ. The overlap is ⟨φ_{1−ε}|φ_ε⟩ = 2√(ε(1 − ε)), so the two m-copy states have squared overlap (4ε(1 − ε))^m. The least average error of two pure states with squared overlap f is (1 − √(1 − f))/2 [3]. This is at most δ < 1/2 only if f ≤ 4δ(1 − δ), which gives the first bound on m. The second follows from log(1/a) ≤ 1/a − 1 = (1 − 2ε)²/(4ε(1 − ε)) for a = 4ε(1 − ε). ∎

## Lean

`lean/StateIdentity/Basic.lean` proves the scalar steps, with only the standard axioms (`lean/axioms.txt`):

- `threshold_gap`: threshold 1/4 and slack (1 − 2ε)/4 separate ε/2 and (1 − ε)/2 for 0 ≤ ε < 1/2.
- `overlap_sq`: the squared overlap of the two candidate states is 4ε(1 − ε).
- `helstrom_step`: error (1 − √(1 − f))/2 ≤ δ < 1/2 forces f ≤ 4δ(1 − δ).
- `copies_lower`: f^m ≤ c with 0 < f < 1 and 0 < c forces m ≥ log(1/c)/log(1/f).
- `log_le_gap` and `copies_lower_gap`: the bound m ≥ 4ε(1 − ε) log(1/(4δ(1 − δ)))/(1 − 2ε)².
- `gap_compare`: 1 − 2√ε ≤ 1 − 2ε.

Assuming: [2, Corollary A.4], tr(A_ij ρ) = (1 − |⟨ψ_i|ψ_j⟩|²)/2, and the least error (1 − √(1 − f))/2 of two pure states [3].

Not formalized: the reduction of a test for the problem to the two-state measurement in Theorem 2.

## Check

`sim/check.py` asserts tr(A ψ ⊗ φ) = (1 − |⟨ψ|φ⟩|²)/2 for random pure states in dimensions 2, 3 and 5. It checks the separation of the thresholds on a grid of ε. It computes the trace distance of the two m-copy candidates exactly on the symmetric subspace for m ≤ 40 and compares it with √(1 − (4ε(1 − ε))^m). It asserts that the smallest m with error at most δ is at least both bounds of Theorem 2, for ε from 0.01 to 0.49 and δ from 0.3 to 10⁻⁴. Output in `sim/out.txt`.

## Scope

- Theorem 1 is a direct application of [2]; the new parts are this observation, Theorem 2, and the resulting dependence on ε.
- The bounds count copies only. The measurement of [2] is not claimed to be efficient in gates.
- As ε → 1/2 with n growing, the dependence on n is not settled: the upper bound is log(n/δ)/(1 − 2ε)², the lower bounds are of order log(1/δ)/(1 − 2ε)² (Theorem 2) and, for δ ≤ 1/2 − c, log n/log(4/ε) by the argument of [1, Corollary 5.5].
- Pure input states, as in [1].

## References

[1] S.-H. Hung, M.-H. Tsai. Efficient quantum state identity testing. arXiv:2610.04597.

[2] C. Bădescu, R. O'Donnell. Improved quantum data analysis. TheoretiCS 3 (2024). arXiv:2011.10908.

[3] C. W. Helstrom. Quantum Detection and Estimation Theory. Academic Press (1976).

[4] H. Buhrman, D. Grinko, P. Verduyn Lunel, J. Weggemans. Permutation tests for quantum state identity. arXiv:2405.09626.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
