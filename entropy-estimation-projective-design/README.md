# Entropy estimation near the maximally mixed state from a projective 2-design measurement

2026-11-12

## Problem

A d-dimensional state ρ is measured n times with a fixed rank-one measurement that is an exact projective 2-design, for example uniformly random pure states, or uniformly random stabilizer states of qubits. Each outcome is a rank-one projector P_Z with density p_ρ(z) = d tr(ρ P_z) relative to the design measure [1, Section 2]. The task is to estimate the entropy S(ρ) = −tr ρ log ρ in mean squared error, uniformly over the ball Θ_loc(r) = {ρ : ‖ρ − I/d‖_op ≤ r}.

In [1] a quadratic estimator, built from the complete degree-two U-statistic of the shadows X = (d + 1)P_Z − I, has risk O(d³r²/n + d⁴/n² + d⁶r⁶) for r ≤ 1/(4d) [1, Theorem 3.1(i)]. Every estimator has risk Ω(d³r²/n + d⁴/n²) for n^{−1/2} ≤ r ≤ 1/(4d) [1, Theorem 3.1(ii)]. The two bounds match for r ≤ c₀ max{(dn)^{−1/3}, (d³n)^{−1/4}} and n ≥ Cd² [1, Corollary 3.2].

## Results

Write H = ρ − I/d, Y_i = X_i − I/d for the i-th shadow, and a_k = (−1)^k/(k(k − 1)). For k = 2, …, K, split the sample into k consecutive blocks of ⌊n/k⌋ outcomes, and let Ĥ_{k,1}, …, Ĥ_{k,k} be the means of Y over these blocks. The estimator is

Ŝ_K = Π_[0, log d] ( log d − Σ_{k=2}^{K} a_k d^{k−1} Re tr(Ĥ_{k,1} Ĥ_{k,2} ⋯ Ĥ_{k,k}) ),

where Π_[0, log d] clips to the interval [0, log d]. Products of independent batch means of shadows are used for higher-order trace functionals in [3], and polynomial approximations of the entropy were estimated with batch shadows in [4]. The estimator here differs from the batched estimators of [2], which average products of single shadows over disjoint tuples: its component of order c carries the factor (k/n)^c. Computed directly, the estimator takes O(Knd² + K²d³) time, and it does not depend on r.

**Theorem 1.** Let the measurement be an exact projective 2-design, d ≥ 2, K ≥ 2 and n ≥ 30Kd³. For every 0 < r ≤ 1/(4d) and every state ρ with ‖ρ − I/d‖_op ≤ r,

E(Ŝ_K − S(ρ))² ≤ 50 (d³r²/n + d⁴/n²) + (32/9) (dr)^{2(K+1)} / (K(K + 1))².

**Corollary 2.** Let the measurement be an exact projective 2-design, K = max{2, ⌈log₁₆(n/d)⌉} and n ≥ 30Kd³, which holds for n ≥ 130 d³ ln d. Then the risk of Ŝ_K is at most 51 (d³r²/n + d⁴/n²) on Θ_loc(r) for every 0 < r ≤ 1/(4d). Together with [1, Theorem 3.1(ii)], for n ≥ 130 d³ ln d the local minimax risk is of order d³r²/n + d⁴/n² for all n^{−1/2} ≤ r ≤ 1/(4d), so on the whole range of [1, Theorem 3.1(ii)]. Previous best range: r ≤ c₀ max{(dn)^{−1/3}, (d³n)^{−1/4}} [1, Corollary 3.2].

The variance bound rests on a chain inequality for products of centred shadows.

**Lemma 3 (one shadow).** Under the design measure, that is, the outcome law of I/d, E tr(YA) tr(YB) = (1 + 1/d)(tr(AB) − tr A tr B / d) for all d × d matrices A, B, and E[YCY] = (1 + 1/d)(tr(C) I − C/d) ⪯ (1 + 1/d) tr(C) I for C ⪰ 0.

**Lemma 4 (products of centred batch means).** Let r ≤ 1/(4d) and ρ ∈ Θ_loc(r). Let E_1, …, E_j be independent, each the mean of m independent copies of Y − H under ρ. For all d × d matrices B_1, …, B_j,

E |tr(E_1 B_1 E_2 B_2 ⋯ E_j B_j)|² ≤ (β/m)^j ∏_i ‖B_i‖₂²,   β = (5/4)(1 + 1/d),

where ‖B‖₂² = tr B†B.

In a different setting, for the complete U-statistics of products of shadows with global shadows, [2, Theorem 6.1] bounds the canonical component of order j with a factor (d + 1)^{2(j−1)}. On the local ball, Lemma 4 gives the factor β^j d^j for the corresponding terms, and this permits degrees growing like log(n/d).

## Proofs

*Lemma 3.* For a projective 2-design, E P_Z = I/d and E P_Z ⊗ P_Z = (I ⊗ I + F)/(d(d + 1)), with F the swap of the two factors. Hence E Y ⊗ Y = (1 + 1/d)(F − I ⊗ I/d). Contracting with A ⊗ B gives the first identity, and inserting C between the two factors gives the second. Since C/d ⪰ 0, the operator inequality follows. ∎

*Lemma 4.* On Θ_loc(r) with dr ≤ 1/4, the density d tr(ρ P_z) = 1 + d tr(H P_z) lies in [3/4, 5/4], since |tr(H P_z)| ≤ ‖H‖_op for a rank-one projector [1, Lemma A.1]. So E_ρ f ≤ (5/4) E f under the design measure for every f ≥ 0, and also for operator-valued f ⪰ 0.

For a matrix M independent of E_1, E|tr(E_1 M)|² = (1/m)(E_ρ|tr(YM)|² − |tr(HM)|²). By Lemma 3 with A = M and B = M†, this is at most (5/(4m))(1 + 1/d)‖M‖₂² = (β/m)‖M‖₂². Apply this with M = B_1 E_2 B_2 ⋯ E_j B_j.

For W independent of E_2 and C = B_1†B_1, E‖B_1 E_2 W‖₂² = E tr(W† E_2 C E_2 W). Moreover E[E_2 C E_2] = (1/m) E_ρ[(Y − H)C(Y − H)] ⪯ (1/m) E_ρ[YCY] ⪯ (β/m) tr(C) I by Lemma 3. Hence E‖B_1 E_2 W‖₂² ≤ (β/m)‖B_1‖₂² E‖W‖₂². Repeating this with W = B_2 E_3 ⋯ E_j B_j, and so on, ends at ‖B_j‖₂². ∎

*Theorem 1.* Write ρ = (I + A)/d with A = dH, so ‖A‖_op ≤ 1/4. Then S(ρ) = log d − (1/d) tr (I + A) log(I + A). For |x| < 1, (1 + x) log(1 + x) = x + Σ_{k≥2} (−1)^k x^k/(k(k − 1)). Since tr A = 0, S(ρ) = log d − Σ_{k≥2} a_k d^{k−1} tr H^k. With |tr H^k| ≤ d r^k, the terms with k > K add up to at most R = (4/3)(dr)^{K+1}/(K(K + 1)).

Let T_k = Re tr(Ĥ_{k,1} ⋯ Ĥ_{k,k}). The blocks are independent, so E T_k = tr H^k. Write Ĥ_{k,b} = H + E_b and expand: tr ∏_b (H + E_b) − tr H^k = Σ_{J} t_J, over nonempty J ⊆ {1, …, k}, where t_J has E_b in the positions b ∈ J and H elsewhere. For J ≠ J′ the terms are orthogonal, E t_J conj(t_{J′}) = 0, since some E_b occurs in only one of them and has mean zero. After a cyclic rotation, t_J = tr(E_{b_1} H^{e_1} ⋯ E_{b_c} H^{e_c}) with c = |J| and e_1 + ⋯ + e_c = k − c, and ‖H^e‖₂² ≤ d r^{2e}, also for e = 0. The blocks have ⌊n/k⌋ ≥ (29/30) n/k outcomes, since n ≥ 30k, so Lemma 4 applies with β/⌊n/k⌋ ≤ (5/4)(3/2)(30/29) k/n ≤ 2k/n and gives

Var T_k ≤ Σ_{c=1}^{k} C(k, c) (2k/n)^c d^c r^{2(k−c)}.

Multiply by a_k² d^{2(k−1)} and write Q = d³r²/n + d⁴/n².

- The term c = 1 equals 2(dr)^{2(k−2)}(k − 1)^{−2} d³r²/n.
- For c ≥ 2, the term equals C(k, c)(2k)² (2kd³/n)^{c−2} (dr)^{2(k−c)} (k(k − 1))^{−2} d⁴/n². Here 2kd³/n ≤ 1/15 and dr ≤ 1/4, so it is at most 4 C(k, c) 15^{−(k−2)} (k − 1)^{−2} d⁴/n².
- Summing over c, a_k² d^{2(k−1)} Var T_k ≤ 16 (2/15)^{k−2} (k − 1)^{−2} Q.

By the triangle inequality in L², the unclipped estimator has error at most

Σ_{k≥2} 4 (2/15)^{(k−2)/2} (k − 1)^{−1} √Q + R ≤ 5√Q + R,

since Σ_{j≥0} x^j/(j + 1) = −log(1 − x)/x ≤ 1.245 at x = (2/15)^{1/2}. Squaring gives a risk of at most 50Q + 2R², and clipping to [0, log d] does not increase the error, since S(ρ) ∈ [0, log d]. ∎

*Corollary 2.* With K ≥ log₁₆(n/d) and dr ≤ 1/4, (dr)^{2(K+1)} ≤ (dr)² 16^{−K} ≤ d³r²/n, and (32/9)/(K(K + 1))² < 1. For the condition n ≥ 30Kd³: if K = 2, it reads n ≥ 60d³, and otherwise K < log₁₆(n/d) + 1. In both cases n ≥ 130 d³ ln d suffices for every d ≥ 2, as a direct computation over the ranges of K shows (the worst case is d = 2, K = 3). ∎

## Check

`sim/entropy_series.py` checks, with asserts:

- Lemma 3 exactly for the stabilizer 2-designs on one and two qubits, by enumeration of all stabilizer states.
- The chain bound under the design measure, and Lemma 4 with m = 1 (centred shadows Y − H under ρ), exactly for j ≤ 3 on these designs, over all tuples of outcomes, with random matrices B_i and random states of the ball, together with the density bound 3/4 ≤ d tr(ρP) ≤ 5/4.
- The estimator with uniformly random pure-state measurements, d = 4 and 8, n up to 10⁶, K = ⌈log₁₆(n/d)⌉ + 1, at the boundary dr = 1/4: its empirical risk stays within the intermediate bound (5√Q + R)² of the proof, which is below the stated bound of Theorem 1. At n = 10⁶, d = 4, it is 1.1 × 10⁻⁷, against 6.3 × 10⁻⁷ for the quadratic estimator, whose squared bias is 4.6 × 10⁻⁷ at this state.

Output in `sim/entropy_series_out.txt`.

## Scope

- Written proofs. The numerical checks cover the identities and the chain bound for small stabilizer designs and the risk for a few states.
- Exact projective 2-designs. The frame-ε designs of [1] are not covered, since Lemma 3 uses the exact second moment.
- Corollary 2 needs n ≥ 130 d³ ln d. For Cd² ≤ n ≤ 130 d³ ln d, the range of [1, Corollary 3.2] is the known one.
- The global question of [1, Section 6], an upper bound over all states, stays open.
- **Not formalized:** the results have no Lean proof.

## References

[1] X. Song. Local and Global Risk Bounds for Quantum Entropy Estimation under Projective-Design Measurements. arXiv:2609.29485.

[2] X. Song. Batched and Complete U-Statistics for Trace-Polynomial Estimation from Classical Shadows. arXiv:2608.22962.

[3] A. Rath, V. Vitale, S. Murciano, M. Votto, J. Dubail, R. Kueng, C. Branciard, P. Calabrese, B. Vermersch. Entanglement barrier and its symmetry resolution: theory and experiment. arXiv:2209.04393.

[4] B. Vermersch, A. Rath, B. Sundar, C. Branciard, J. Preskill, A. Elben. Enhanced estimation of quantum properties with common randomized measurements. PRX Quantum 5, 010352 (2024). arXiv:2304.12292.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
