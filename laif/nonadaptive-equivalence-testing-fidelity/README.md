# Non-adaptive equivalence testing in fidelity needs Ω(d^{3/2}/ε²) copies

2026-11-26

## Problem

Two unknown states ρ and σ on C^d are given through copies, and each copy is measured on its own. The task is to decide whether ρ = σ or F(ρ, σ) ≤ 1 − ε, with success probability at least 2/3. In the trace distance, the same task needs Θ(d^{3/2}/ε²) copies, and adaptivity does not help [2, 3, 4]. In the fidelity, certification of a known σ needs only Õ(d^{3/2}/ε) copies, and adaptive equivalence testing uses Õ(min{d^{3/2}/ε², d^{9/4}/ε}) copies [1, Thms 1.1, 1.2]. For non-adaptive measurements, Ω̃(1/ε²) copies are needed already for qubits [1, Thm 1.4]. It is asked in [1, Sec. 1.2] whether non-adaptive equivalence testing in the fidelity has an asymptotic advantage over the trace distance, and conjectured there that it needs Ω̃(d^{3/2}/ε²) copies.

| | copies of σ |
|---|---|
| Previous best bound, non-adaptive, upper [2, 3] | O(d^{3/2}/ε²), from the trace-distance tester |
| Previous best bound, non-adaptive, lower [1, Thm 1.4] | Ω̃(1/ε²) |
| Theorem 1, non-adaptive, lower | Ω(d^{3/2}/ε²) for ε ≤ 1/3400 and d ≥ 120 + 8 ln(1/ε) |

So, to our knowledge, the fidelity gives no asymptotic advantage over the trace distance for non-adaptive equivalence testing, which answers the first open question of [1, Sec. 1.2] in this range of d.

## Result

F(ρ, σ) = ‖√ρ√σ‖₁ is the fidelity of [1]. Since 1 − F² ≥ 1 − F, everything below holds for the squared fidelity too.

**Theorem 1.** Let 0 < ε ≤ 1/2, d = 2D and D ≥ 60 + 4 ln(1/ε). Consider a tester that measures copies of ρ and σ one at a time, where the measurements on the copies of σ are fixed in advance (random choices are allowed if they are independent of the states). The copies of ρ may be measured in any way, even adaptively among themselves. If the tester accepts with probability at least 2/3 when ρ = σ and rejects with probability at least 2/3 when F(ρ, σ) ≤ 1 − ε/1700, then it uses more than

N = 3D^{3/2}/ε² = 3d^{3/2}/(2√2 ε²)

copies of σ. In terms of ε_F = ε/1700: N > 3.6·10⁻⁷ · d^{3/2}/ε_F² for ε_F ≤ 1/3400 and d ≥ 120 + 8 ln(1/(1700 ε_F)). For odd d, use d − 1. The constants are not optimized.

Together with the trace-distance tester [2, 3] the copy count is Θ(d^{3/2}/ε²) in this range.

*Non-vacuity.* Both hypotheses of the two-point argument are realized by explicit states. Every alternative σ_G is a state at fidelity at most 1 − ε/1700 from ρ (Lemma 1), and the good event E of the random perturbation has probability at least 1 − 10⁻²⁸ for D ≥ 60 (Lemma 2). The instance is solvable: its trace distance is of order ε, so the tester of [2, 3] decides it with O(d^{3/2}/ε²) copies, and the bound is tight on it. `sim/check.py` asserts Lemma 1 on random draws for D = 8, 16, 32, the tail and dimension bounds of Section 4, and the identities of Lemmas 3 to 5 on small cases.

## Instance

Let c₀ = 3/20, ρ₀ = ((1 − ε)/D) I_D ⊕ (ε/D) I_D, W a Haar-random unitary on C^d and ρ = Wρ₀W†. The second block is the light block. Let g be a standard Gaussian vector in the real space of Hermitian D × D matrices (inner product tr(AB)), H = g/√D, and G = H − (tr H/D) I, the projection to traceless matrices. Let E be the event that ‖G‖_op ≤ 5 and ‖G‖_F² ≥ D/2, and μ_E the law of G given E.

- Null: σ = ρ.
- Alternative: σ_G = W(ρ₀ + (εc₀/D)(0 ⊕ G))W†, with G ~ μ_E independent of W.

**Lemma 1.** For G ∈ E, σ_G is a state, σ_G ≥ ε/(4D) on the light block, F(ρ, σ_G) ≤ 1 − εc₀²‖G‖_F²/(8(7/4)^{3/2}D) ≤ 1 − ε/1700, and ½‖ρ − σ_G‖₁ = (εc₀/(2D))‖G‖₁.

*Proof.* tr G = 0 gives tr σ_G = 1. On the light block σ_G = (ε/D)(I + c₀G) ≥ (ε/D)(1 − 5c₀) = ε/(4D). The states commute, so with g_k the eigenvalues of G, F = (1 − ε) + (ε/D) Σ_k √(1 + c₀g_k). For |x| ≤ 3/4, √(1 + x) ≤ 1 + x/2 − x²/(8(7/4)^{3/2}) by the Taylor remainder. With Σ g_k = 0 and Σ g_k² ≥ D/2 this gives 1 − F ≥ εc₀²/(16(7/4)^{3/2}) = ε/1646. ∎

**Lemma 2.** P(E^c) ≤ 2e^{−1.13D} + 2e^{−D²/32} + e^{−(D²−1)/36}.

*Proof.* For a unit vector x, ⟨x|H|x⟩ = tr(xx†g)/√D is Gaussian with variance 1/D. A 1/10-net of the unit sphere of C^D = R^{2D} has at most 21^{2D} points, and for Hermitian H, ‖H‖_op ≤ 1.25 max over the net of |⟨y|H|y⟩|. So P(‖H‖_op > 4.75) ≤ 2·21^{2D}e^{−D·3.8²/2} ≤ 2e^{−1.13D}. Next, tr H/D is Gaussian with variance 1/D², so |tr H|/D ≤ 1/4 except with probability 2e^{−D²/32}, and then ‖G‖_op ≤ 5. Finally D‖G‖_F² has the chi-square distribution with k = D² − 1 degrees of freedom, and the lower tail bound P(χ²_k ≤ k − 2√(kx)) ≤ e^{−x} with x = k/36 gives ‖G‖_F² ≥ D/2. ∎

## Proof

**Reduction to a fixed W.** Fix the measurements on the copies of σ, rank-one without loss of generality: in step i a measurement {c_ij|v_ij⟩⟨v_ij|}_j with Σ_j c_ij|v_ij⟩⟨v_ij| = I. Given W, the outcomes on the copies of ρ have the same law under both hypotheses and are independent of the outcomes on the copies of σ. Hence the total variation distance between the two hypotheses is at most E_W of the distance between the laws of the σ-outcomes, Q₀ under the null and the mixture E_{μ_E}Q_G under the alternative [1, Sec. 7]. From here W is fixed, and we may take W = I after replacing v_ij by W†v_ij.

Let u_ij be the light-block part of v_ij, t_ij = ‖u_ij‖², û_ij = u_ij/√t_ij and φ(t) = t/((1 − ε)(1 − t) + εt). In step i the null probability of outcome j is q_i(j) = (c_ij/D) t_ij/φ(t_ij), and under σ_G it is q_i(j)(1 + g_ij) with g_ij = εc₀φ(t_ij)⟨û_ij|G|û_ij⟩. Since Σ_j c_ij|u_ij⟩⟨u_ij| = I_D and tr G = 0, Σ_j q_i(j)g_ij = 0. On E, |g_ij| ≤ 3/4.

**Lemma 3.** Let λ_ij = c_ij t_ij φ(t_ij), γ = ε²c₀²/D, and T the linear map T(Y) = Σ_ij λ_ij ⟨û_ij|Y|û_ij⟩ |û_ij⟩⟨û_ij| on Hermitian matrices. Then 1 + χ²(E_{μ_E}Q_G ‖ Q₀) ≤ P(E)⁻² E exp(γ tr(G T(G′))), with G and G′ independent and not conditioned on E.

*Proof.* The second-moment identity for a mixture against a product law gives 1 + χ² = E_{G,G′~μ_E} Π_i (1 + h_i), with h_i = Σ_j q_i(j)g_ij(G)g_ij(G′) = γ Σ_j λ_ij⟨û_ij|G|û_ij⟩⟨û_ij|G′|û_ij⟩. For G, G′ ∈ E each factor 1 + h_i = Σ_j q_i(j)(1 + g_ij(G))(1 + g_ij(G′)) is nonnegative and at most e^{h_i}, so the product is at most exp(γ tr(G T(G′))). This bound is positive everywhere, so the conditioning on E × E costs at most the factor P(E)⁻². ∎

**Lemma 4.** Let A = Σ_ij c_ij φ(t_ij)|u_ij⟩⟨u_ij|. Then T is positive semidefinite, tr T = tr A and ‖T‖ ≤ ‖A‖_op.

*Proof.* T is a sum of the rank-one maps λ_ij|B⟩⟨B| with B = |û_ij⟩⟨û_ij| and ‖B‖_F = 1, so tr T = Σ λ_ij = tr A. By Cauchy-Schwarz ⟨û|Y|û⟩² ≤ ⟨û|Y²|û⟩, so tr(Y T(Y)) ≤ tr(AY²) ≤ ‖A‖_op‖Y‖_F². ∎

**Lemma 5.** If γ²‖A‖_op² ≤ D²/2, then E exp(γ tr(G T(G′))) ≤ exp(γ²‖A‖_op tr A/D²).

*Proof.* Write G = Pg/√D with P the projection to traceless matrices, and S = PTP, with eigenvalues τ_k ≤ ‖A‖_op and Σ τ_k² ≤ tr T² ≤ ‖A‖_op tr A. The Gaussian moment generating function gives E_g exp((γ/D)⟨g, Sg′⟩) = exp(γ²‖Sg′‖²/(2D²)) and E_{g′} exp(γ²⟨g′, S²g′⟩/(2D²)) = Π_k (1 − γ²τ_k²/D²)^{−1/2} ≤ exp(γ² Σ τ_k²/D²), using −½ ln(1 − x) ≤ x for 0 ≤ x ≤ 1/2. ∎

**Aligned measurement elements.** Call (i, j) aligned if t_ij > 3/4. On the other elements φ ≤ 3, so their part of A is at most 3N·I_D. The aligned part has trace at most β_W/ε, with β_W the total weight c_ij of aligned elements, since φ ≤ 1/ε. For a fixed unit vector v and Haar-random W, t = ‖light part of W†v‖² has the Beta(D, D) distribution, so P(t > 3/4) ≤ (D/2)(3/4)^{D−1}. The measurements are fixed before W, so E_W β_W ≤ ND²(3/4)^{D−1}. By the Markov inequality, with probability at least 19/20 over W, β_W ≤ 20ND²(3/4)^{D−1} ≤ εN, where the last step uses D ≥ 60 + 4 ln(1/ε). For such W, ‖A‖_op ≤ 7N and tr A ≤ 7ND.

**Count.** For such W and N ≤ 3D^{3/2}/ε², the condition of Lemma 5 holds, and 1 + χ² ≤ P(E)⁻² exp(49c₀⁴ε⁴N²/D³) ≤ P(E)⁻² e^{0.2233}. So the total variation distance is at most 1/20 + ½√(e^{0.2233}/P(E)² − 1) ≤ 0.30 < 1/3, and no tester succeeds with probability 2/3 on both hypotheses. ∎

The bound needs the measurements on σ to be fixed before W is drawn. If the measurement basis is aligned with the two blocks, then t ∈ {0, 1}, A = (N/ε)I, and the exponent becomes of order ε²N²/D³, which only gives Ω(D^{3/2}/ε). This is the copy count of certification with a known σ [1, Thm 1.1].

## Check

`sim/check.py` (output `sim/out_check.txt`, about a minute on one core) asserts:
- Lemma 1 on random draws for D = 8, 16, 32 and ε = 0.3, 10⁻², 10⁻⁴: the states, the fidelity formula and bound, and the trace distance;
- the Beta tail for D < 400 and the dimension condition for ln(1/ε) up to 200;
- the constants of Lemma 2, with random draws in E for D ≥ 16;
- for D = 3, 4 with random and nearly aligned bases, the χ² identity and Lemma 4. It also checks the exact product formula of Lemma 5 against Monte Carlo;
- the final constants.

## Scope

- The measurements on the copies of σ are single-copy and fixed in advance. Measurements acting jointly on a copy of ρ and a copy of σ are not covered, as in [1].
- The dimension condition d ≥ 120 + 8 ln(1/ε) is used in the Markov step. For smaller d, the qubit bound of [1, Thm 1.4] applies.
- The constants are far from optimal: the alternative is at infidelity ε/1700, and the instance has trace distance about 0.06ε.

## References

1. J. Seyfried, S. Sen, M. Tomamichel. On the power of adaptivity in testing quantum states in fidelity. arXiv:2609.08733 (2026).
2. S. Bubeck, S. Chen, J. Li. Entanglement is necessary for optimal quantum property testing. FOCS 2020.
3. S. Chen, J. Li, R. O'Donnell. Toward instance-optimal state certification with incoherent measurements. COLT 2022.
4. S. Chen, J. Li, B. Huang, A. Liu. Tight bounds for quantum state certification with incoherent measurements. FOCS 2022.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
