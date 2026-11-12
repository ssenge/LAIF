# Multipartite product testing with single-copy local measurements

2026-11-12

## Problem

Copies of an unknown pure state |ψ⟩ on n qudits of dimension d are given. The task is to accept if ψ is fully product, ψ = φ_1 ⊗ ⋯ ⊗ φ_n, and to reject if the trace distance from ψ to every fully product state is at least ε, each with probability at least 2/3. Every copy is measured on its own, and every measurement is local: a product of measurements on the single qudits. In [1, Theorem 5.2] a non-adaptive test of this kind is given with O(n log n √d ε⁻²) copies, for ε ≤ 1/√2. It estimates every single-qudit purity to precision ε_p = ε²(1 − ε²)/n. The question is raised in [1, Open Question 4] whether O(n √d ε⁻²) copies suffice.

## Results

**Theorem 1.** A test with two rounds of single-copy local measurements uses

N₁ + N₂ copies, N₁ = ⌈max{143 n(d − 1)/ε², 72 d ln(80 n d/ε²)}⌉, N₂ = ⌈160/ε²⌉,

which is O(d(n/ε² + log d)), and errs with probability at most 0.15 on product states and at most 0.1 on states at distance at least ε, for every ε ∈ (0, 1].

For constant d, this is O(n ε⁻²), the bound asked for in [1, Open Question 4], reached with one round of adaptivity. For qubits, the previous best bound is O(n log n ε⁻²) [1, Theorem 5.2].

**Remark 2 (the ε-dependence in [1, Theorem 5.2]).** The proof of [1, Theorem 5.2] takes the single-copy purity estimator of [2, 3] at O(log(1/δ) √d/ε_p) copies. In [3] the cost of this estimator is given as O(max{1/ε_p², √d/ε_p}). With ε_p = ε²(1 − ε²)/n, the argument then gives O(log n · max{n² ε⁻⁴, n √d ε⁻²}) copies. This hints at a possible gap in the stated bound when √d < n/ε², for instance for qubits. Theorem 1 holds for every d. For d = O(1) it gives O(n ε⁻²) copies.

## Algorithm

1. *Local tomography.* Measure each of N₁ copies with an independent, uniformly random basis on every qudit. For qudit i, let v_{i,t} be the basis vector observed on copy t, set R_i = (1/N₁) Σ_t ((d + 1)|v_{i,t}⟩⟨v_{i,t}| − I), and let v_i be a top eigenvector of R_i.
2. *Product check.* Measure each of N₂ further copies with, on every qudit i, a basis that contains v_i. Call a copy a miss if some qudit gives an outcome other than v_i. Accept if fewer than (3/4) ε² N₂ copies are misses.

## Proof

**Lemma 1.** Let φ be a unit vector, R self-adjoint, E = R − |φ⟩⟨φ| with ‖E‖_op ≤ 1/4, and v a top eigenvector of R. Then 1 − |⟨v|φ⟩|² ≤ (16/9) ‖Eφ‖².

*Proof.* The second largest eigenvalue of R is at most ‖E‖_op ≤ 1/4 by the perturbation bound for eigenvalues of self-adjoint matrices, and the largest is at least ⟨φ|R|φ⟩ ≥ 3/4. Write φ = cos θ v + sin θ w with w a unit vector orthogonal to v, so w lies in the span of the eigenvectors with eigenvalues in [−1/4, 1/4]. Then Eφ = (R − I)φ = cos θ (λ − 1) v + sin θ (R − I) w, the two parts are orthogonal, and ‖(R − I)w‖ ≥ 3/4. So ‖Eφ‖² ≥ (9/16) sin² θ = (9/16)(1 − |⟨v|φ⟩|²). ∎

**Lemma 2.** Let a qudit be in the pure state φ and let R be the estimator of step 1 from N copies. Then E[R] = |φ⟩⟨φ|, E‖(R − |φ⟩⟨φ|)φ‖² = 2(d − 1)/N, and P(‖R − |φ⟩⟨φ|‖_op > 1/4) ≤ 2d e^{−N/(72d)}.

*Proof.* Let X = (d + 1)|v⟩⟨v| − I for one copy. For a uniformly random basis, the observed vector satisfies E|v⟩⟨v| = (I + |φ⟩⟨φ|)/(d + 1), since the random basis is a 2-design. Hence E X = |φ⟩⟨φ|. With x = |⟨v|φ⟩|², ‖Xφ‖² = (d² − 1)x + 1 and E x = ⟨φ|E|v⟩⟨v||φ⟩ = 2/(d + 1), so E‖(X − |φ⟩⟨φ|)φ‖² = E‖Xφ‖² − 1 = 2(d − 1). The copies are independent with mean zero increments, which gives the second claim. For the third, ‖X − |φ⟩⟨φ|‖_op ≤ d + 1 and E(X − |φ⟩⟨φ|)² = E X² − |φ⟩⟨φ| = d I + (d − 2)|φ⟩⟨φ|, of norm at most 2d. The matrix concentration inequality for sums of bounded independent self-adjoint matrices [4, Theorem 1.4], applied to both signs with deviation N/4, gives the bound 2d exp(−(N²/32)/(2dN + (d + 1)N/12)) ≤ 2d e^{−N/(72d)}. ∎

*Proof of Theorem 1.* Let ψ be at distance at least ε from the product states. Then |⟨v_1 ⊗ ⋯ ⊗ v_n|ψ⟩|² ≤ 1 − ε² for every choice of the v_i, so each copy of step 2 is a miss with probability p ≥ ε², whatever happened in step 1. The number of misses K has mean N₂p and variance at most N₂p. So P(K < (3/4)ε²N₂) ≤ p/(N₂(p − 3ε²/4)²) ≤ 16/(N₂ε²) ≤ 0.1, as p/(p − c)² decreases for p > c.

Let ψ = φ_1 ⊗ ⋯ ⊗ φ_n. The outcomes of step 1 on qudit i are those of the single-qudit estimator for φ_i. By Lemmas 1 and 2, with F_i = |⟨v_i|φ_i⟩|², E[1 − F_i] ≤ (32/9)(d − 1)/N₁ + 2d e^{−N₁/(72d)}. The choice of N₁ makes each of the n first terms at most ε²/(40n), and each of the n second terms at most ε²/(40n). So E Σ_i (1 − F_i) ≤ ε²/20, and Σ_i (1 − F_i) ≤ ε²/2 with probability at least 0.9. In that case each copy of step 2 is a miss with probability p = 1 − Π_i F_i ≤ Σ_i (1 − F_i) ≤ ε²/2. Then P(K ≥ (3/4)ε²N₂) ≤ N₂p/(ε²N₂/4)² ≤ 8/(N₂ε²) ≤ 0.05. The total error on product states is at most 0.15. Finally, ln(80nd/ε²) ≤ ln 80 + n/ε² + ln d, so N₁ + N₂ = O(d(n/ε² + log d)). ∎

## Check

`sim/producttest.py` checks with asserts:

- the identity E‖(R − |φ⟩⟨φ|)φ‖² = 2(d − 1)/N, within five standard errors, for d = 2 and 8 and several N;
- the inequality of Lemma 1 on every sample with ‖R − |φ⟩⟨φ|‖_op ≤ 1/4;
- the full test with the constants of Theorem 1 on random product states of n qubits, and on states at distance exactly ε, built as tensor products of n/2 entangled pairs cos t|00⟩ + sin t|11⟩ with cosⁿ t = 1 − ε² and rotated by random local unitaries. Step 1 is simulated from the single-qudit outcomes, whose law does not depend on the correlations between the qudits. Step 2 is simulated exactly from the probability of a copy with no miss.

| n | ε | copies N₁ + N₂ | product states accepted | states at distance ε accepted |
|---|---|---|---|---|
| 6 | 0.4 | 5363 + 1000 | 40 of 40 | 0 of 40 |
| 10 | 0.3 | 15889 + 1778 | 20 of 20 | 0 of 20 |

Output in `sim/producttest_out.txt`.

## Scope

- **Assuming:** the matrix concentration inequality of [4, Theorem 1.4].
- **Not formalized:** the results have no Lean proof.
- The test is adaptive between its two rounds. For d ≥ (log n)², the non-adaptive bound O(n log n √d ε⁻²) of [1] has the better dependence on d.
- The constants are not optimized.

## References

[1] J. Beckey, L. Coffman, A. Shlosberg, L. Schatzki, F. Leditzky. Product testing with single-copy measurements. arXiv:2510.07820.

[2] A. Anshu, Z. Landau, Y. Liu. Distributed quantum inner product estimation. STOC 2022. arXiv:2111.03273.

[3] W. Gong, J. Haferkamp, Q. Ye, Z. Zhang. On the sample complexity of purity and inner product estimation. arXiv:2410.12712.

[4] J. A. Tropp. User-friendly tail bounds for sums of random matrices. Found. Comput. Math. 12 (2012). arXiv:1004.4389.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
