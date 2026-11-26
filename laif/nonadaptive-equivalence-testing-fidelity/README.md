# Non-adaptive equivalence and independence testing in fidelity need Ω(d^{3/2}/ε²) copies

2026-11-26

## Problem

Two unknown states ρ and σ on C^d are given through copies, and each copy is measured on its own. The task is to decide whether ρ = σ or F(ρ, σ) ≤ 1 − ε, with success probability at least 2/3. In the trace distance, the same task needs Θ̃(d^{3/2}/ε²) copies, and adaptivity does not help [2, 3, 4]. In the fidelity, certification of a known σ needs only Õ(d^{3/2}/ε) copies, and adaptive equivalence testing uses Õ(min{d^{3/2}/ε², d^{9/4}/ε}) copies [1, Thms 1.1, 1.2]. For non-adaptive measurements, Ω̃(1/ε²) copies are needed already for qubits [1, Thm 1.4]. It is asked in [1, Sec. 1.2] whether non-adaptive equivalence testing in the fidelity has an asymptotic advantage over the trace distance, and conjectured there that it needs Ω̃(d^{3/2}/ε²) copies. The same question is asked for independence testing: given copies of a state ρ_AC on C^{d_A} ⊗ C^{d_C}, decide whether ρ_AC = ρ_A ⊗ ρ_C or F(ρ_AC, ρ_A ⊗ ρ_C) ≤ 1 − ε. There the trace-distance tester uses Õ((d_A d_C)^{3/2}/ε²) copies [2, 3], which is optimal in the trace distance [5], and an adaptive tester in the fidelity is given in [1].

| | copies of σ |
|---|---|
| Previous best bound, non-adaptive, upper [2, 3, 4] | Õ(d^{3/2}/ε²), from the trace-distance tester, since ½‖ρ − σ‖₁ ≥ 1 − F ≥ ε |
| Previous best bound, non-adaptive, lower [1, Thm 1.4] | Ω̃(1/ε²) |
| Theorem 1, non-adaptive, lower | Ω(d^{3/2}/ε²) for ε ≤ 1/3400 and d ≥ 120 + 8 ln(1/ε) |

So, to our knowledge, the fidelity gives no asymptotic advantage over the trace distance for non-adaptive equivalence testing, which settles the equivalence-testing part of the first open question of [1, Sec. 1.2] in this range of d. Theorem 2 below settles the independence-testing part in the same way.

| | copies of ρ_AC, independence testing |
|---|---|
| Previous best bound, non-adaptive, upper [2, 3, 5] | Õ((d_A d_C)^{3/2}/ε²), from the trace-distance tester |
| Theorem 2, non-adaptive, lower | Ω((d_A d_C)^{3/2}/ε²) for d_A ≥ 112 and d_A ≥ 2 + 8 ln(21 d_A d_C/ε) |

## Result

F(ρ, σ) = ‖√ρ√σ‖₁ is the (root) fidelity, as in [1]. Theorem 1 also holds for the squared fidelity F², since 1 − F² ≥ 1 − F. For F² the matching upper bound below loses a factor 2 in the gap, since ½‖ρ − σ‖₁ ≥ 1 − F ≥ (1 − F²)/2.

**Theorem 1.** Let 0 < ε ≤ 1/2, d = 2D and D ≥ 60 + 4 ln(1/ε). Consider a tester that measures copies of ρ and σ one at a time, where the measurements on the copies of σ are fixed in advance (random choices are allowed if they are independent of the states). The number of copies of σ is fixed too. The copies of ρ may be measured in any way, even adaptively, depending on all earlier outcomes. If the tester accepts with probability at least 2/3 when ρ = σ and rejects with probability at least 2/3 when F(ρ, σ) ≤ 1 − ε/1700, then it uses more than

N = 3D^{3/2}/ε² = 3d^{3/2}/(2√2 ε²)

copies of σ. In terms of ε_F = ε/1700: N > 3.6·10⁻⁷ · d^{3/2}/ε_F² for ε_F ≤ 1/3400 and d ≥ 120 + 8 ln(1/(1700 ε_F)). For odd d, use d − 1. The constants are not optimized.

Both bounds refer to the same problem. If F(ρ, σ) ≤ 1 − ε_F, then ½‖ρ − σ‖₁ ≥ 1 − F ≥ ε_F, so the trace-distance tester [2, 3, 4] decides ρ = σ against F ≤ 1 − ε_F with Õ(d^{3/2}/ε_F²) copies. Theorem 1 matches this up to logarithmic factors for ε_F ≤ 1/3400 and d ≥ 120 + 8 ln(1/ε_F), with the absolute constant 3.6·10⁻⁷ in the lower bound.

*Non-vacuity.* Both hypotheses of the two-point argument are realized by explicit states. Every alternative σ_G is a state at fidelity at most 1 − ε/1700 from ρ (Lemma 1), and the good event E of the random perturbation has probability at least 1 − 10⁻²⁸ for D ≥ 60 (Lemma 2). The instance is solvable: its trace distance is of order ε, so the tester of [2, 3, 4] decides it with Õ(d^{3/2}/ε²) copies, and the bound is tight on it up to logarithmic factors. `sim/check.py` asserts Lemma 1 on random draws for D = 8, 16, 32, the tail and dimension bounds of Section 4, and the identities of Lemmas 3 to 5 on small cases.

## Instance

Let c₀ = 3/20, ρ₀ = ((1 − ε)/D) I_D ⊕ (ε/D) I_D, W a Haar-random unitary on C^d and ρ = Wρ₀W†. The second block is the light block. Let g be a standard Gaussian vector in the real space of Hermitian D × D matrices (inner product tr(AB)), H = g/√D, and G = H − (tr H/D) I, the projection to traceless matrices. Let E be the event that ‖G‖_op ≤ 5 and ‖G‖_F² ≥ D/2, and μ_E the law of G given E.

- Null: σ = ρ.
- Alternative: σ_G = W(ρ₀ + (εc₀/D)(0 ⊕ G))W†, with G ~ μ_E independent of W.

**Lemma 1.** For G ∈ E, σ_G is a state, σ_G ≥ ε/(4D) on the light block, F(ρ, σ_G) ≤ 1 − εc₀²‖G‖_F²/(8(7/4)^{3/2}D) ≤ 1 − ε/1700, and ½‖ρ − σ_G‖₁ = (εc₀/(2D))‖G‖₁.

*Proof.* tr G = 0 gives tr σ_G = 1. On the light block σ_G = (ε/D)(I + c₀G) ≥ (ε/D)(1 − 5c₀) = ε/(4D). The states commute, so with g_k the eigenvalues of G, F = (1 − ε) + (ε/D) Σ_k √(1 + c₀g_k). For |x| ≤ 3/4, √(1 + x) ≤ 1 + x/2 − x²/(8(7/4)^{3/2}) by the Taylor remainder. With Σ g_k = 0 and Σ g_k² ≥ D/2 this gives 1 − F ≥ εc₀²/(16(7/4)^{3/2}) ≥ ε/1647. ∎

**Lemma 2.** P(E^c) ≤ 2e^{−1.13D} + 2e^{−D²/32} + e^{−(D²−1)/36}.

*Proof.* For a unit vector x, ⟨x|H|x⟩ = tr(xx†g)/√D is Gaussian with variance 1/D. A 1/10-net of the unit sphere of C^D = R^{2D} has at most 21^{2D} points, and for Hermitian H, ‖H‖_op ≤ 1.25 max over the net of |⟨y|H|y⟩|. So P(‖H‖_op > 4.75) ≤ 2·21^{2D}e^{−D·3.8²/2} ≤ 2e^{−1.13D}. Next, tr H/D is Gaussian with variance 1/D², so |tr H|/D ≤ 1/4 except with probability 2e^{−D²/32}, and then ‖G‖_op ≤ 5. Finally D‖G‖_F² has the chi-square distribution with k = D² − 1 degrees of freedom, and the lower tail bound P(χ²_k ≤ k − 2√(kx)) ≤ e^{−x} with x = k/36 gives ‖G‖_F² ≥ D/2. ∎

## Proof

**Reduction to a fixed W.** Fix the measurements on the copies of σ, rank-one without loss of generality: in step i a measurement {c_ij|v_ij⟩⟨v_ij|}_j with Σ_j c_ij|v_ij⟩⟨v_ij| = I. Given W and the outcomes on the copies of σ, the outcomes on the copies of ρ have the same conditional law under both hypotheses, since ρ is the same. Hence, by data processing, the total variation distance between the two hypotheses is at most E_W of the distance between the laws of the σ-outcomes, Q₀ under the null and the mixture E_{μ_E}Q_G under the alternative [1, Sec. 7]. From here W is fixed, and we may take W = I after replacing v_ij by W†v_ij. Elements with t_ij = 0 do not depend on G and are dropped below.

Let u_ij be the light-block part of v_ij, t_ij = ‖u_ij‖², û_ij = u_ij/√t_ij and φ(t) = t/((1 − ε)(1 − t) + εt). In step i the null probability of outcome j is q_i(j) = (c_ij/D) t_ij/φ(t_ij), and under σ_G it is q_i(j)(1 + g_ij) with g_ij = εc₀φ(t_ij)⟨û_ij|G|û_ij⟩. Since Σ_j c_ij|u_ij⟩⟨u_ij| = I_D and tr G = 0, Σ_j q_i(j)g_ij = 0. On E, |g_ij| ≤ 3/4.

**Lemma 3.** Let λ_ij = c_ij t_ij φ(t_ij), γ = ε²c₀²/D, and T the linear map T(Y) = Σ_ij λ_ij ⟨û_ij|Y|û_ij⟩ |û_ij⟩⟨û_ij| on Hermitian matrices. Then 1 + χ²(E_{μ_E}Q_G ‖ Q₀) ≤ P(E)⁻² E exp(γ tr(G T(G′))), with G and G′ independent and not conditioned on E.

*Proof.* The second-moment identity for a mixture against a product law gives 1 + χ² = E_{G,G′~μ_E} Π_i (1 + h_i), with h_i = Σ_j q_i(j)g_ij(G)g_ij(G′) = γ Σ_j λ_ij⟨û_ij|G|û_ij⟩⟨û_ij|G′|û_ij⟩. For G, G′ ∈ E each factor 1 + h_i = Σ_j q_i(j)(1 + g_ij(G))(1 + g_ij(G′)) is nonnegative and at most e^{h_i}, so the product is at most exp(γ tr(G T(G′))). This bound is positive everywhere, so the conditioning on E × E costs at most the factor P(E)⁻². ∎

**Lemma 4.** Let A = Σ_ij c_ij φ(t_ij)|u_ij⟩⟨u_ij|. Then T is positive semidefinite, tr T = tr A and ‖T‖ ≤ ‖A‖_op.

*Proof.* T is a sum of the rank-one maps λ_ij|B⟩⟨B| with B = |û_ij⟩⟨û_ij| and ‖B‖_F = 1, so tr T = Σ λ_ij = tr A. By Cauchy-Schwarz ⟨û|Y|û⟩² ≤ ⟨û|Y²|û⟩, so tr(Y T(Y)) ≤ tr(AY²) ≤ ‖A‖_op‖Y‖_F². ∎

**Lemma 5.** If γ²‖A‖_op² ≤ D²/2, then E exp(γ tr(G T(G′))) ≤ exp(γ²‖A‖_op tr A/D²).

*Proof.* Write G = Pg/√D with P the projection to traceless matrices, and S = PTP, with eigenvalues τ_k ≤ ‖A‖_op and Σ τ_k² ≤ tr T² ≤ ‖A‖_op tr A. The Gaussian moment generating function gives E_g exp((γ/D)⟨g, Sg′⟩) = exp(γ²‖Sg′‖²/(2D²)) and E_{g′} exp(γ²⟨g′, S²g′⟩/(2D²)) = Π_k (1 − γ²τ_k²/D²)^{−1/2} ≤ exp(γ² Σ τ_k²/D²), using −½ ln(1 − x) ≤ x for 0 ≤ x ≤ 1/2. ∎

**Aligned measurement elements.** Call (i, j) aligned if t_ij > 3/4. On the other elements φ ≤ 3, so their part of A is at most 3N·I_D. The aligned part has trace at most β_W/ε, with β_W the total weight c_ij of aligned elements, since φ ≤ 1/ε. For a fixed unit vector v and Haar-random W, t = ‖light part of W†v‖² has the Beta(D, D) distribution, so P(t > 3/4) ≤ (D/2)(3/4)^{D−1}. The measurements are fixed before W, so E_W β_W ≤ ND²(3/4)^{D−1}. By the Markov inequality, with probability at least 19/20 over W, β_W ≤ 20ND²(3/4)^{D−1} ≤ εN, where the last step uses D ≥ 60 + 4 ln(1/ε). For such W, ‖A‖_op ≤ 7N and tr A ≤ 7ND.

**Count.** For such W and N ≤ 3D^{3/2}/ε², the condition of Lemma 5 holds, and 1 + χ² ≤ P(E)⁻² exp(49c₀⁴ε⁴N²/D³) ≤ P(E)⁻² e^{0.2233}. So the total variation distance is at most 1/20 + ½√(e^{0.2233}/P(E)² − 1) ≤ 0.30 < 1/3, and no tester succeeds with probability 2/3 on both hypotheses. ∎

The bound needs the measurements on σ to be fixed before W is drawn. That a fixed schedule rarely aligns with a random hidden direction is also the mechanism of the qubit bound [1, Lemma 7.2]. If the measurement basis is aligned with the two blocks, then t ∈ {0, 1}, A = (N/ε)I, and the exponent becomes of order ε²N²/D³, which only gives Ω(D^{3/2}/ε). This is the copy count of certification with a known σ [1, Thm 1.1].

## Independence testing

**Theorem 2.** Let 0 < ε ≤ 1/2, d_A = 2D_A, d_C ≥ 2 and D = D_A d_C, with D_A ≥ 56 and D_A ≥ 1 + 4 ln(41 D_A d_C/ε). Consider a tester that measures copies of ρ_AC one at a time, with the measurements and the number of copies fixed in advance (random choices are allowed if they are independent of the state). It may also use any number of copies of ρ_A ⊗ ρ_C, measured in any way, as in [1]. If it accepts with probability at least 2/3 when ρ_AC = ρ_A ⊗ ρ_C and rejects with probability at least 2/3 when F(ρ_AC, ρ_A ⊗ ρ_C) ≤ 1 − ε/3800, then it uses more than

N = 13D^{3/2}/ε² = 13(d_A d_C)^{3/2}/(2√2 ε²)

copies of ρ_AC. In terms of ε_F = ε/3800: N > 9.0·10⁻⁷ · (d_A d_C/2)^{3/2}/ε_F². For odd d_A, use d_A − 1.

**Corollary 3** (mutual information). The relative entropy is at least the order-1/2 sandwiched divergence, so D(ρ‖σ) ≥ −2 ln F(ρ, σ) ≥ 2(1 − F). Every alternative of Theorem 2 therefore has I(A:C) = D(ρ_AC‖ρ_A ⊗ ρ_C) ≥ ε/1900. Hence testing I(A:C) = 0 against I(A:C) ≥ ε/1900 with the same kind of tester needs more than 13D^{3/2}/ε² copies.

*Non-vacuity.* Every alternative is a state whose two marginals are those of the null state, at fidelity at most 1 − ε/3705 from it, and the good event has probability at least 1 − 2·10⁻³. `sim/check_indep.py` asserts both on random draws (D_A = 3, d_C = 2). Its trace distance is of order ε, so the tester of [2, 3] decides the instance with Õ((d_A d_C)^{3/2}/ε²) copies.

*Instance.* Let c₀ = 1/10, ρ_A = W[((1 − ε)/D_A)I ⊕ (ε/D_A)I]W† with W Haar-random on C^{d_A}, and null ρ_AC = ρ_A ⊗ I/d_C. The light block is now L = (light block of A) ⊗ C^{d_C}, of dimension D. Let H = g/√D be Gaussian on the Hermitian matrices on L as before, and G = H − tr_C H ⊗ I/d_C − I ⊗ tr_A H/D_A + (tr H)I/D, the orthogonal projection of H to the matrices with tr_A G = 0 and tr_C G = 0. Let E be the event that ‖G‖_op ≤ 15/2 and ‖G‖_F² ≥ D/2. The alternative is σ_G = ρ_AC + (εc₀/D)(W ⊗ I)(0 ⊕ G)(W ⊗ I)†, with G drawn from the law of G given E. Its marginals are ρ_A and I/d_C, so the product of its marginals is the null state, and Lemma 1 gives F ≤ 1 − εc₀²/(16(7/4)^{3/2}) ≤ 1 − ε/3705.

*Proof.* The changes against Theorem 1 are as follows.
- The good event. tr_C H and tr_A H are Gaussian on the Hermitian matrices of dimension D_A and d_C, with entries of variance 1/D_A and 1/d_C. The net bound gives ‖H‖_op ≤ 4.75, ‖tr_C H‖_op ≤ 4.75 and ‖tr_A H‖_op ≤ 5.6, except with probabilities 2e^{−1.13D}, 2e^{−1.13D_A} and 2·21^{2d_C}e^{−d_C·4.48²/2} ≤ 7.6·10⁻⁴. So ‖G‖_op ≤ 4.75 + 4.75/2 + 5.6/56 + 1/4 ≤ 7.5, and c₀‖G‖_op ≤ 3/4. The projection has rank k = (D_A² − 1)(d_C² − 1) ≥ 0.75(1 − D_A⁻²)D², and the chi-square lower tail at x = k/64 gives ‖G‖_F² ≥ D/2.
- Reduction to a fixed W. The copies of ρ_A ⊗ ρ_C have the null state under both hypotheses, so the argument of Theorem 1 applies.
- Lemmas 3 to 5 hold as stated, with u_ij the part of v_ij in L. Lemma 5 uses only that P is an orthogonal projection.
- Aligned elements. A measurement vector v may be entangled between A and C. With its Schmidt form v = Σ_k s_k a_k ⊗ b_k, which is fixed before W, t = Σ_k s_k² t_k, where each t_k = ⟨a_k|W Π W†|a_k⟩ has the Beta(D_A, D_A) distribution. With x = t_k − 1/2, the density satisfies (t_k(1 − t_k))^{D_A−1}/B(D_A, D_A) ≤ 2√(D_A/π) e^{−4(D_A−1)x²}, since 1/B(D, D) ≤ 2√(D/π) 4^{D−1}. So E e^{λ(t_k − 1/2)} ≤ √(D_A/(D_A − 1)) e^{λ²/(16(D_A−1))}. By convexity of the exponential the same bound holds for t, and λ = 2(D_A − 1) gives P(t > 3/4) ≤ √(D_A/(D_A − 1)) e^{−(D_A−1)/4}. The measurement weights sum to 2ND, so by the Markov inequality, with probability at least 19/20 over W, the aligned weight is at most εN under the dimension condition. Then ‖A‖_op ≤ 4N and tr A ≤ 4ND.
- Count. For N ≤ 13D^{3/2}/ε² the exponent is at most 16·169c₀⁴ = 0.2704, and the total variation distance is at most 1/20 + ½√(e^{0.2704}/(1 − 2·10⁻³)² − 1) < 1/3. ∎

## Check

`sim/check.py` (output `sim/out_check.txt`, about a minute on one core) asserts:
- Lemma 1 on random draws for D = 8, 16, 32 and ε = 0.3, 10⁻², 10⁻⁴: the states, the fidelity formula and bound, and the trace distance;
- the Beta tail for D < 400 and the dimension condition for ln(1/ε) up to 200;
- the constants of Lemma 2, with random draws in E for D ≥ 16;
- for D = 3, 4 with random and nearly aligned bases, the χ² identity and Lemma 4. It also checks the exact product formula of Lemma 5 against Monte Carlo;
- the final constants.

`sim/check_indep.py` (output `sim/out_check_indep.txt`) asserts the constants of Theorem 2, the Beta tail bound for D < 400 and the bound on the binomial coefficient, the tail bound for entangled vectors by Monte Carlo, the norms of the projected Gaussian, and, at D_A = 3 and d_C = 2, that the projection is orthogonal with the stated rank, that the product of the marginals of every alternative is the null state, and the fidelity gap.

`sim/constants_iv.py` (output `sim/out_constants_iv.txt`) recomputes the final constants of both theorems with exact rationals and interval arithmetic with outward rounding: the fidelity gaps ε/1647 and ε/3705, the probabilities of the good events, and the final total variation bounds 0.3001 and 0.3295, both below 1/3.

## Scope

- The measurements on the copies of σ are single-copy and fixed in advance. Measurements acting jointly on a copy of ρ and a copy of σ are not covered, as in [1].
- The dimension condition d ≥ 120 + 8 ln(1/ε) is used in the Markov step. For smaller d, the qubit bound Ω̃(1/ε²) of [1, Thm 1.4] applies, for testers whose measurements on both states are fixed in advance.
- Theorem 2 needs d_C ≥ 2 and the dimension condition on d_A (the roles of A and C can be swapped). When both dimensions are of order ln(1/ε) or smaller, it gives nothing.
- The constants are far from optimal: the alternative is at infidelity ε/1700, and the instance has trace distance about 0.06ε.

## References

1. J. Seyfried, S. Sen, M. Tomamichel. On the power of adaptivity in testing quantum states in fidelity. arXiv:2609.08733 (2026).
2. S. Bubeck, S. Chen, J. Li. Entanglement is necessary for optimal quantum property testing. FOCS 2020.
3. S. Chen, J. Li, R. O'Donnell. Toward instance-optimal state certification with incoherent measurements. COLT 2022.
4. S. Chen, J. Li, B. Huang, A. Liu. Tight bounds for quantum state certification with incoherent measurements. FOCS 2022.
5. N. Yu. Sample efficient identity testing and independence testing of quantum states. ITCS 2021.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
