# Quantum reservoir complexity bounds polynomial in the number of qubits

2026-11-22

## Problem

A quantum reservoir on n qubits processes an input sequence v = (…, v_{−1}, v_0) by a family of channels T^θ(v_t, ·). Its state after the sequence is the limit H^θ(v) of the composed channels, which exists when every T^θ(v, ·) contracts the entrywise 2-norm ‖·‖₂ on density matrices with a constant r < 1 (condition (AT2) of [1]). A readout h_ω maps the state to a real number. In [1] the generalization error of the class {h_ω ∘ H^θ} is bounded through its random-sign complexity

R_k = E sup_{θ,ω} |(1/k) Σ_{j<k} ε_j h_ω(H^θ(v^{(j)}))|,

with independent uniform signs ε_j, for k input sequences. The bound of [1, Theorem 4] is

R_k ≤ 48 · 0.89 (√dim Θ + √dim Ω) A/√k,  A = max{L̄_h L′_Θ D_Θ, L_Ω D_Ω},

where D_Θ, D_Ω are the diameters of the parameter sets, L̄_h is a slope bound of the readouts in the state, L′_Θ = L_Θ/(1 − r) a slope bound of H^θ in θ, and L_Ω one of h_ω in ω. For the readouts of [1] the slope bound L̄_h grows like 2^{n/2} or faster, because the entrywise 2-norm of an n-qubit observable carries a factor 2^{n/2}. Hence the bounds of [1, Propositions 8 and 9, Corollary 11, Theorems 17 and 18] are exponential in n, and for the linear readout [1, Section 4.2.1] states that this "cannot be improved upon simply by replacing the polynomial readout through a linear one".

| | random-sign complexity R_k, linear readout, under (AT2) with constant r |
|---|---|
| Previous bound [1, Corollary 11] | exponential in n, times 1/√k |
| Theorem 1, partial-trace reservoir of [1] | O((C_max + n) n √((n + ln(1/(1 − r)) + ln(1 + ΔJ + Δγ) + ln n)/k)) |

## Results

**Theorem 1.** Assume the conditions of [1, Theorem 4], let B ≥ sup_{θ,ω,v} |h_ω(H^θ(v))| and d = dim Θ + dim Ω. Then

R_k ≤ 24 B √(d (1 + ln(1 + 4A/B)) / k).

The slope bounds enter only through ln(1 + 4A/B). For A ≲ B the bound is of the same order as that of [1].

**Corollary 2.** Assume (AT2) with constant r < 1 on the parameter set. For the partial-trace reservoir of [1, Section 5.1], with slope bound L_Θ = 2^{n+1}√(n(4n − 3)) [1, Lemma 15] and at most n² + 1 parameters (the couplings of all pairs of the n + 1 qubits in [1, eq. (13)] and the field γ):

- linear readout h(ρ) = C + Σ_i w_i tr(Z_i ρ), |C| ≤ C_max, w ∈ [0, 1]^n: B ≤ C_max + n and d ≤ n² + n + 2, so R_k = O((C_max + n) n √(L/k)) with L = 1 + ln(1 + 4A/B) = O(n + ln(1/(1 − r)) + ln(1 + ΔJ + Δγ) + ln n), where ΔJ = J_max − J_min and Δγ = γ_max − γ_min;
- polynomial readout of degree at most R_max [1, eq. (7)] with N_poly weights in [0, 1]: B ≤ C_max + N_poly and d ≤ n² + N_poly + 2, with N_poly polynomial in n for fixed R_max.

Both are polynomial in n for fixed r, parameter ranges and C_max. The same holds for every class to which [1, Theorem 4] applies with readouts bounded by a polynomial in n, and the third term of the risk bound [1, eq. (27)], adapted there from [2, Theorem 14], which is the term that contains the random-sign complexity, becomes polynomial in n accordingly.

**Proposition 3 (contraction of the partial-trace reservoir).**

- The contraction argument of [1, Appendix H] gives ‖T(v, A)‖₂ ≤ √2 √(v² + (1 − v)²) ‖A‖₂ for traceless A. Since v² + (1 − v)² ≥ 1/2, this factor is at least 1 for every input v. The stated constant r_PTR(ε) = 2√2(ε² − ε√(√2 − 1)) + 1 equals √2 (v² + (1 − v)²) at the end of the input interval, so it lacks the square root.
- If n ≥ 2 and all couplings are equal, J_ij = c for all pairs, then for every c, γ and v the map T(v, ·) has two different fixed states. Their difference A is traceless with T(v, A) = A, so no r < 1 satisfies (AT2). Uniform couplings lie in every parameter box Θ_PTR of [1], so for n ≥ 2 (AT2) fails on every such box.
- If J_ij = π for all pairs and γ is arbitrary, then e^{−iH(J,γ)} = e^{−iγ Σ_i Z_i}, and T(v, ·) is a unitary channel on the reservoir, also for n = 1.

This hints at a possible gap in [1, Lemma 15], and the results of [1] for this class, like Corollary 2, apply to parameter sets on which (AT2) is verified separately. For inputs v ≠ 1/2 the map is not unital, and its contraction coefficient can exceed 1: at uniform couplings c = 0.5, γ = 0.7 and v ∈ {0.3, 0.7} it is 1.016 for n = 2 and 1.043 for n = 3.

## Proof

**Theorem 1.** Condition on the input sequences and write h_t for the function with parameter t = (θ, ω). As in [1, Appendix B], R_k ≤ (2/k) E sup_t Z_t with Z_t = Σ_j ε_j h_t(ρ_t^{(j)}), E Z_{t₀} = 0, and Z_t − Z_{t′} is sub-Gaussian for the metric

d(t, t′) = (Σ_j (h_t(ρ_t^{(j)}) − h_{t′}(ρ_{t′}^{(j)}))²)^{1/2}.

Two facts bound this metric.

- d(t, t′) ≤ √k (L̄_h L′_Θ ‖θ − θ′‖ + L_Ω ‖ω − ω′‖). A maximal ε-separated subset of a set of diameter D in ℝ^m is an ε-cover with centres in the set, of size at most (1 + 2D/ε)^m by comparing volumes. Covering Θ at ε = κ/(2√k L̄_h L′_Θ) and Ω at ε = κ/(2√k L_Ω) gives log N(κ) ≤ d log(1 + 4A√k/κ).
- Every term is at most 2B in absolute value, so sup_t d(t, t₀) ≤ 2B√k.

The chaining bound [3, Corollary 13.2] used in [1] integrates up to half of this diameter:

E sup_t Z_t ≤ 12 ∫₀^{B√k} √(d log(1 + 4A√k/κ)) dκ = 12 B √k ∫₀¹ √(d log(1 + c/u)) du,  c = 4A/B.

By the inequality between the mean and the root mean square, ∫₀¹ √(log(1 + c/u)) du ≤ (∫₀¹ log(1 + c/u) du)^{1/2}, and ∫₀¹ log(1 + c/u) du = log(1 + c) + c log(1 + 1/c) ≤ log(1 + c) + 1. Hence E sup_t Z_t ≤ 12 B √(k d (1 + ln(1 + 4A/B))), and R_k ≤ 24 B √(d (1 + ln(1 + 4A/B))/k). In [1, Appendix B] the integral runs up to √k (L̄_h L′_Θ D_Θ + L_Ω D_Ω)/2, which is where A enters linearly.

**Corollary 2.** For the linear readout, |tr(Z_i ρ)| ≤ 1 gives B ≤ C_max + n. By [1, Lemma 15 and Corollary 11], A is bounded by a product of powers of 2^n, n, 1/(1 − r) and the parameter ranges (in particular L̄_h = n 2^{n/2} and L_Ω = √(n + 1)), so ln(1 + 4A/B) = O(n + ln(1/(1 − r)) + ln(1 + ΔJ + Δγ) + ln n). The polynomial readout is the same with B ≤ C_max + N_poly, since every monomial in the values tr(Z_i ρ) has absolute value at most 1.

**Proposition 3, constant.** v² + (1 − v)² = 1/2 + 2(v − 1/2)² ≥ 1/2. At v = (1 + s)/2 − ε with s = √(√2 − 1), √2(v² + (1 − v)²) = √2(1/2 + 2(s/2 − ε)²) = 1 + 2√2(ε² − εs), the stated constant.

**Proposition 3, uniform couplings.** Label the ancilla 0 and the reservoir qubits 1, …, n, and let |s⟩ be the antisymmetric state of qubits 1 and 2. Then (X_1X_2 + Y_1Y_2)|s⟩ = −2|s⟩, and (X_1 + X_2)|s⟩ = (Y_1 + Y_2)|s⟩ = (Z_1 + Z_2)|s⟩ = 0. With equal couplings every term of H that involves qubit 1 or 2 and another qubit j is c(X_j(X_1 + X_2) + Y_j(Y_1 + Y_2)), so H(|s⟩ ⊗ |φ⟩) = |s⟩ ⊗ (H′ − 2c)|φ⟩, where H′ acts on the ancilla and qubits 3, …, n. Hence the subspace |s⟩ ⊗ (rest) is invariant under e^{−iH}, and so is its orthogonal complement. Both reservoir subspaces V = |s⟩ ⊗ ℂ^{2^{n−2}} and V^⊥ are therefore invariant under T(v, ·): a state supported on V (or V^⊥), tensored with the ancilla state, stays in the invariant subspace, and the partial trace over the ancilla stays supported on V (or V^⊥). A channel on the states of a subspace has a fixed state, so T(v, ·) has a fixed state on V and one on V^⊥, and they differ.

**Proposition 3, J ≡ π.** Let q = n + 1 and S_α = (1/2)Σ_i σ_α^{(i)}. Then Σ_{i<j}(X_iX_j + Y_iY_j) = 2(S_x² + S_y²) − q = 2(S² − S_z²) − q. On a joint eigenspace with S² = s(s + 1) and S_z = m, s − m = t is an integer and 2m ≡ q (mod 2), so 2(s(s + 1) − m²) − q = 4tm + 2t² + 2s − q, which is even, because 2s ≡ q (mod 2). Hence e^{−iπΣ_{i<j}(X_iX_j+Y_iY_j)} = I. This sum commutes with S_z, so e^{−iH} = e^{−iγΣ_iZ_i}, a product of single-qubit rotations. The rotation of the ancilla commutes with its diagonal input state, so the partial trace leaves the rotated reservoir state.

## Check

`sim/contraction.py`, output in `sim/out_contraction.txt`. The contraction coefficient of T(v, ·) on traceless operators is computed exactly as an operator norm.

- The stated constant equals √2(v² + (1 − v)²) at the end of the input interval, and √2√(v² + (1 − v)²) ≥ 1, for several ε.
- For J ≡ π the coefficient is 1 to 10⁻⁹ for n = 1, 2, 3, three values of γ and three inputs v.
- For uniform couplings c ∈ {0.2, 0.5, 1, 2}, γ ∈ {0, 0.7}, v ∈ {0.3, 0.5, 0.7} and n = 2, 3, the fixed states on V and V^⊥ are computed by iteration, their difference A satisfies T(v, A) = A, and the coefficient is at least 1.

`sim/bound.py`, output in `sim/out_bound.txt`: the integral identity of the proof by quadrature, and Theorem 1 against [1, Corollary 11] for the linear readout, n = 2 to 30, with the constants of [1] and r = 0.9. At n = 10 Theorem 1 gives about 1.3 · 10⁴ against about 10^{11.8} for [1, Corollary 11], both times 1/√k.

## Lean

`lean/ReservoirSinglet/Basic.lean` proves the two-qubit identities of the uniform-coupling part of Proposition 3: the 4 × 4 matrices are the stated tensor products (`XXYY_eq`, `Xsum_eq`, `Ysum_eq`, `Zsum_eq`), and for s = |01⟩ − |10⟩, (X⊗X + Y⊗Y)s = −2s and (X⊗I + I⊗X)s = (Y⊗I + I⊗Y)s = (Z⊗I + I⊗Z)s = 0 (`XXYY_s`, `Xsum_s`, `Ysum_s`, `Zsum_s`). `lean/axioms.txt` lists the axioms of every named theorem: only `propext`, `Classical.choice` and `Quot.sound`. The rest of the proofs is a Claim.

## Scope

- Theorem 1 improves the random-sign complexity term. The other constants of the risk bound [1, eq. (27)] contain L̄_h directly and are not changed here.
- Corollary 2 assumes (AT2) with some r < 1 on the parameter set. By Proposition 3 this fails on every box Θ_PTR for n ≥ 2, so it applies to parameter sets on which (AT2) is checked separately.
- The random reinitialization reservoir of [1, Section 5.2] has a parameter set of dimension of order 4^n (the reset state), and Theorem 1 does not make its bound polynomial.
- Single-output readouts only. The statements are Claims with the listed checks. Lean covers only the steps listed in the Lean section.

## References

1. N. M. Chmielewski, N. Amini, J. Mikael. Quantum reservoir computing and risk bounds. arXiv:2501.08640.
2. L. Gonon, L. Grigoryeva, J.-P. Ortega. Risk bounds for reservoir computing. Journal of Machine Learning Research 21 (2020).
3. S. Boucheron, G. Lugosi, P. Massart. Concentration inequalities: a nonasymptotic theory of independence. Oxford University Press, 2013.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
