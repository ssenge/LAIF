# Rank-sensitive bounds for complete U-statistics of projected classical shadows

2026-11-12

## Problem

An unknown d-dimensional state ρ is measured N times with global classical shadows: a uniformly random Clifford unitary U, readout in the computational basis with outcome b, and the shadow X = (d + 1)U†|b⟩⟨b|U − I [1, eq. (1)]. For a fixed projector P of rank s, put A = PρP and Y_t = P X_t P, so that E Y_t = A. The complete U-statistic T̂_{k,N}^U averages the symmetrized trace kernel h_k(Z_1, …, Z_k) = (1/k!) Σ_π tr(Z_{π(1)} ⋯ Z_{π(k)}) over all k-subsets of the shadows, and estimates tr(A^k) without bias [1, Section 2].

Write Y = A + E. The variance of polynomial estimators Σ_k a_k T̂_{k,N}^U is governed by the order-j components ζ_{j,k} = E ψ_{j,k}², where ψ_{j,k}(E_1, …, E_j) = h_k(E_1, …, E_j, A, …, A) for independent centred projected shadows E_i [1, Theorem 6.1]. If A ⪯ ΔP, it is shown in [1, Theorem 6.1] that ζ_{j,k} ≤ 3s(d + 1)^{2(j−1)} Δ^{2(k−j)}. Since the factor (d + 1)^{2(j−1)} grows with the dimension, the growing-dimension entropy bound [1, Corollary 7.2] needs 2L(d + 1)² ≤ ηNΔ² for polynomials of degree L. Whether the dimension factors can be replaced by rank-sensitive constants at every order is stated as open in [1, Section 7].

## Results

Let c_d = (3d + 4)/(d + 2) < 3. The results hold for every projective 3-design measurement, for example global Clifford shadows of qubits or uniformly random pure states, for every state ρ and every fixed projector P.

**Theorem 1 (chain bound).** Let E_1, …, E_j be independent, each the mean of m independent copies of PXP − A. For all d × d matrices B_1, …, B_j,

E |tr(E_1 B_1 E_2 B_2 ⋯ E_j B_j)|² ≤ (c_d/m)^j ∏_i ‖B_i‖₂²,

where ‖B‖₂² = tr B†B.

**Theorem 2 (every order).** If A ⪯ ΔP, then for all 1 ≤ j ≤ k,

ζ_{j,k} ≤ (c_d s)^j Δ^{2(k−j)}.

Previous best bound: 3s(d + 1)^{2(j−1)} Δ^{2(k−j)} [1, Theorem 6.1]. The ratio of the two bounds is (c_d/3)(c_d s/(d + 1)²)^{j−1} ≤ (3/(d + 1))^{j−1}, since s ≤ d. The bound of Theorem 2 depends on the rank s and not on d.

**Corollary 3 (polynomial estimators).** For deterministic a_1, …, a_L,

Var(Σ_k a_k T̂_{k,N}^U) ≤ Σ_{j=1}^{L} C(N, j)^{−1} (c_d s)^j (Σ_{k=j}^{L} |a_k| C(k, j) Δ^{k−j})².

**Corollary 4 (entropy functional in any dimension).** Let p_{L,∆} be the polynomial of [1, eq. (18)], fix 2 ≤ L and η ∈ (0, 1), and let 0 ⪯ A ⪯ ΔP with 0 < Δ ≤ e^{−1}. If

6Ls ≤ ηNΔ²,

then E(Φ̂_p^U − H_P(ρ))² ≤ C_{L,η} (s²Δ²/L⁴ + s log²(1/Δ)/N), where H_P(ρ) = −tr(A log A). Previous condition: 2L(d + 1)² ≤ ηNΔ² [1, Corollary 7.2, eq. (29)].

The condition of Corollary 4 does not involve d, so the bound holds uniformly over all dimensions, for instance for every d at fixed rank s. At Δ = N^{−α} with 0 < α < 1/2, the regime given after [1, Corollary 7.2] has d = O(N^β) with β < min{α, (1 − 2α)/2}; Corollary 4 needs only s ≤ ηN^{1−2α}/(6L), and then its bound tends to zero whenever sN^{−α} → 0.

## Proofs

**Lemma 5 (one shadow under a 3-design).** Let the outcome φ have density d⟨φ|ρ|φ⟩ with respect to a projective 3-design and X = (d + 1)|φ⟩⟨φ| − I. For all d × d matrices C, A, B,

E[XCX] = ((d + 1)/(d + 2)) (tr C (I + ρ) + tr(Cρ) I) − (C + Cρ + ρC)/(d + 2),

E tr(XA) tr(XB) = ((d + 1)/(d + 2)) (tr A tr B + tr(AB) + tr A tr(Bρ) + tr B tr(Aρ) + tr(ABρ) + tr(BAρ)) − tr A tr B − tr(Aρ) tr B − tr A tr(Bρ).

Hence E[XCX] ⪯ c_d tr(C) I for C ⪰ 0, and E|tr(XM)|² ≤ c_d ‖M‖₂² for every M.

*Proof.* For a 3-design, E(|φ⟩⟨φ|)^{⊗3} = Σ_{π∈S₃} W_π/(d(d + 1)(d + 2)), with W_π the permutation operators. Contracting with I ⊗ C ⊗ ρ, and with A ⊗ B ⊗ ρ, gives

E_ρ[⟨φ|C|φ⟩ |φ⟩⟨φ|] = (tr C I + C + tr C ρ + tr(Cρ) I + Cρ + ρC)/((d + 1)(d + 2)),

E_ρ[⟨φ|A|φ⟩⟨φ|B|φ⟩] = (tr A tr B + tr(AB) + tr A tr(Bρ) + tr B tr(Aρ) + tr(ABρ) + tr(BAρ))/((d + 1)(d + 2)),

where E_ρ includes the density d⟨φ|ρ|φ⟩. With E_ρ|φ⟩⟨φ| = (I + ρ)/(d + 1), expanding X = (d + 1)|φ⟩⟨φ| − I gives the two identities.

For C ⪰ 0, (I + ρ)C(I + ρ) ⪰ 0 gives −(C + Cρ + ρC) ⪯ ρCρ ⪯ tr(C) I. Also ρ ⪯ I and tr(Cρ) ≤ tr C. So E[XCX] ⪯ (3(d + 1) + 1)/(d + 2) tr(C) I = c_d tr(C) I.

For M, take A = M and B = M†, and write t = tr M, u = tr(Mρ). The second identity becomes ((d + 1)/(d + 2))(‖M‖₂² + tr((MM† + M†M)ρ)) − (|t|² + 2 Re(t ū))/(d + 2). Here tr((MM† + M†M)ρ) ≤ 2‖M‖₂², and |t|² + 2 Re(t ū) = |t + u|² − |u|² ≥ −|u|² ≥ −‖M‖₂², since |tr(Mρ)| ≤ ‖M‖₂ ‖ρ‖₂ ≤ ‖M‖₂. So E|tr(XM)|² ≤ c_d ‖M‖₂². ∎

*Theorem 1.* For a matrix M independent of E_1, E|tr(E_1 M)|² = (1/m)(E|tr(PXP M)|² − |tr(AM)|²) ≤ (1/m) E|tr(X PMP)|² ≤ (c_d/m)‖PMP‖₂² ≤ (c_d/m)‖M‖₂², by Lemma 5. Apply this with M = B_1 E_2 B_2 ⋯ E_j B_j.

For W independent of E_2 and C = B_1†B_1 ⪰ 0, E‖B_1 E_2 W‖₂² = E tr(W† E_2 C E_2 W). Moreover E[E_2 C E_2] = (1/m)(E[PXP C PXP] − ACA) ⪯ (1/m) P E[X (PCP) X] P ⪯ (c_d/m) tr(C) I by Lemma 5. Hence E‖B_1 E_2 W‖₂² ≤ (c_d/m)‖B_1‖₂² E‖W‖₂². Repeating this with W = B_2 E_3 ⋯ E_j B_j, and so on, ends at ‖B_j‖₂². ∎

*Theorem 2.* The kernel ψ_{j,k}(E_1, …, E_j) = h_k(E_1, …, E_j, A, …, A) is the average over the k! orderings of the trace of a product of E_1, …, E_j, each once, and k − j copies of A. After a cyclic rotation each such trace is tr(E_{σ(1)} B_1 ⋯ E_{σ(j)} B_j), with B_i = A^{e_i} for exponents e_1 + ⋯ + e_j = k − j, where B_i = P if e_i = 0 (since E = PEP). Then ‖B_i‖₂² = tr A^{2e_i} ≤ s Δ^{2e_i}, also for e_i = 0. By convexity, the mean square of the average is at most the average of the mean squares, and Theorem 1 with m = 1 bounds each by c_d^j s^j Δ^{2(k−j)}. ∎

*Corollary 3.* This is [1, eq. (24)] with |ζ_{j,k,ℓ}| ≤ (ζ_{j,k} ζ_{j,ℓ})^{1/2} and the triangle inequality within each order, as in the proof of [1, eq. (25)], with Theorem 2 in place of [1, eq. (21)]. ∎

*Corollary 4.* The proof of [1, Corollary 7.2] goes through with Theorem 2 in place of [1, eq. (21)]. The monomial coefficients satisfy |a_1| ≤ log(1/Δ) + c_L and |a_k| ≤ c_L Δ^{1−k} for k ≥ 2, so S_j = Σ_{k≥j} |a_k| C(k, j) Δ^{k−j} satisfies S_1 ≤ log(1/Δ) + c′_L and S_j ≤ c′_L Δ^{1−j} for j ≥ 2. In Corollary 3, the order j = 1 contributes at most c_d s S_1²/N ≤ C_L s log²(1/Δ)/N. For j ≥ 2, C(N, j) ≥ (N/L)^j gives

(c_d s)^j S_j² / C(N, j) ≤ c′_L² (c_d s L/N) β^{j−1},   β = c_d s L/(NΔ²) ≤ η/2 < 1/2,

and the sum over j ≥ 2 is at most c′_L² c_d s L/N, since β/(1 − β) ≤ 1. Here N ≥ 6Ls/(ηΔ²) ≥ 2L, so the binomial bound applies. The squared bias is at most C s²Δ²/L⁴ by the approximation bound after [1, eq. (18)]. ∎

## Check

`sim/chain3.py` checks with asserts, by exact enumeration over the stabilizer states on one and two qubits, which form projective 3-designs:

- the identities of Lemma 5 and its two bounds, for random states of every rank and random matrices;
- Theorem 1 with m = 1 and the constant 3 ≥ c_d, for j ≤ 4 (d = 2) and j ≤ 3 (d = 4), every rank s of P, random states, and both random matrices B_i and powers of A;
- Theorem 2 for k ≤ 4 and all j ≤ k with 60^j ≤ 3 × 10⁵ outcomes, with the exact symmetrized kernel, against (3s)^j Δ^{2(k−j)} with Δ = ‖A‖_op; the output lists the previous bound 3s(d + 1)^{2(j−1)} Δ^{2(k−j)} next to it.

Output in `sim/chain3_out.txt`.

## Scope

- Written proofs, with the numerical checks for d = 2 and 4.
- Exact projective 3-designs, as for global Clifford shadows of qubits. The bounds hold for every state ρ and every fixed projector P.
- Corollary 4 keeps the constants C_{L,η} of [1, Corollary 7.2], which grow with L, so polynomial degrees that grow with N are not covered.
- **Not formalized:** the results have no Lean proof.

## References

[1] X. Song. Batched and Complete U-Statistics for Trace-Polynomial Estimation from Classical Shadows. arXiv:2608.22962.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
