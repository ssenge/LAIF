# Learning Gaussian unitaries with 1/ε² queries by chain doubling

2026-11-12

## Problem

An m-mode Gaussian unitary G = D_r U_S is fixed by a displacement r ∈ ℝ^{2m} and a symplectic matrix S ∈ Sp(2m, ℝ). A coherent state |x⟩ has mean x and covariance 1, and a Gaussian state with mean μ and covariance V has mean photon number tr(V − 1)/4 + ‖μ‖²/2. The task of [1, Problem 1]: with black-box queries to G, where ‖S‖ ≤ z and every state fed into G has mean photon number at most n̄_in, output r̃ and S̃ ∈ Sp(2m, ℝ) such that G̃ = D_{r̃} U_{S̃} satisfies ½‖G̃ − G‖_{⋄,n̄} ≤ ε with probability at least 1 − δ, in the diamond norm restricted to inputs with mean photon number at most n̄.

Previous best bound: the algorithm of [1, Theorem 6.1, Remark 6.1] uses

Θ( m⁴ z⁸ (n̄ + 1)² (n̄_in + 1)^{1/2} (m + log(m/δ)) / (n̄_in ε⁴) ) + Θ( (z²n̄ + 1)(m + log(1/δ)) / ((n̄_in + 1)^{1/4} ε²) )

queries for n̄_in ≥ (2m)^{4/3}, with coherent and squeezed probes, heterodyne detection and parallel queries; as n̄_in → ∞ it needs only 2m + 2 queries [1, Remark 6.1]. Matching upper and lower bounds are stated as an open problem in [1, Section 1.4], where the 1/ε⁴ is traced to the continuity bound of [2] for the energy-constrained diamond distance, and it is remarked that sharper bounds on this distance could reduce the scaling to 1/ε².

## Results

The algorithm below uses sequential, adaptive queries: chains of queries with known operations in between, chosen from earlier outcomes. The previous best bound above is for independent, parallel queries. The two bounds are therefore for different access models, and the comparison below is not between algorithms of the same kind.

**Theorem 1.** Let m ≥ 1, z ≥ 1, n̄ ≥ 0, n̄_in > 0 and ε, δ ∈ (0, 1). There is an algorithm with sequential queries that uses only coherent probes, known Gaussian unitaries and displacements between queries, and heterodyne detection, feeds G only states with mean photon number at most n̄_in, and solves the task above with

N_tot = O( (m + log(L/δ)) · [ m² (n̄ + 1) / (ñ γ ε²) + m z² (n̄ + m)^{1/2} / (ñ^{1/2} γ² ε) + m z⁸ / (ñ γ²) ] )

queries, where t² = Θ(m + log(L/δ)) is defined below, ñ = min{n̄_in, 32t²}, γ = min{1/4, ñ/(5m)} and L = O(log(m z (n̄ + 1) / ε)). For n̄_in ≥ 5m/4 the leading term is O(m² (m + log(L/δ)) (n̄ + 1) / (ñ ε²)), which is O(m² (n̄ + 1)/ε²) once n̄_in ≥ 32t². Explicit constants are given in the proof.

So the dependence on ε drops from 1/ε⁴ to 1/ε². For (2m)^{4/3} ≤ n̄_in ≤ 32t², the 1/ε² term is smaller than the 1/ε⁴ term of [1] by a factor of order z⁸ m² (n̄ + 1)(n̄_in + 1)^{1/2}/ε². Above 32t² the bound here no longer improves with n̄_in, while the bound of [1] keeps decreasing towards 2m + 2, so at very large input energy the bound of [1] is the smaller one. The queries are sequential: chains of up to 2^L uses of G, interleaved with known Gaussian operations, are fed coherent states and measured at the end. Similar amplification along sequential queries gives inverse-accuracy scaling for fermionic linear optics [3] and for bosonic Hamiltonians with time-evolution access [4].

The continuity bound itself cannot be sharpened in its dependence on the error of the symplectic matrix. A version of the following bound is [2, Lemma S4]; we include the short computation in the form used here.

**Proposition 2.** For n̄ ≥ 1 and 0 < θ ≤ π/(2n̄ + 1), the single-mode phase rotation U_θ = e^{−iθ a†a}, with symplectic matrix S_θ, satisfies ½‖U_θ − id‖_{⋄,n̄} ≥ (n̄θ/π)^{1/2} ≥ (n̄ ‖S_θ − 1‖ / π)^{1/2}.

So the square root in the continuity bound [1, Proposition 2.2], [2] is attained up to a constant: an estimate of S with error θ guarantees only ε of order (n̄θ)^{1/2}, and S has to be known to precision of order ε²/n̄. Theorem 1 reaches this precision with 1/ε² queries by amplifying the residual error along chains of queries.

## Algorithm

Write Ω for the symplectic form, sp(2m) = {K : KᵀΩ + ΩK = 0}, ‖·‖ for the operator norm, ‖·‖₂ for the entrywise 2-norm, and P(K) = (K + ΩKᵀΩ)/2. Let t = 2(2m)^{1/2} + (2 ln(1/δ′))^{1/2} with δ′ = δ/(2L + 3), and fix ñ = min{n̄_in, 32t²}, the probe amplitude η = (ñ/2)^{1/2}, the step size γ = min{1/4, ñ/(5m)}, n̄′ = z²(n̄ + m/2),

k_A = 112 m (n̄ + 1) γ / ε²,   k_B = z η (n̄′ + 1)^{1/2} / (2√2 ε),   L = ⌈log₂ max{k_A, k_B, 1}⌉.

Since t depends on L only through log L, L is the least integer with 2^L ≥ max{k_A, k_B, 1} for these values; it is O(log(m z (n̄ + 1)/ε)) because η ≤ 4t.

1. **Coarse stage.** Run the symmetric-probe estimator of [1, Lemma 4.2] with probes |±ηe_i⟩ and N_c = ⌈800 z⁸ t² / (η²γ²)⌉ samples per probe, so that ‖Ŝ − S‖ ≤ ε₀ = γ/(40z³), and round Ŝ to the symplectic matrix T = ŜQ⁻¹, Q = (−ΩŜᵀΩŜ)^{1/2}, of [1, Lemma 4.3]. Set ĉ = 0.
2. **Doubling stages** k = 1, 2, 4, …, 2^L. For each i ∈ [2m] and each sign, prepare |±ηe_i⟩ N times and apply k times the step "query G, then the known U_T^{−1}, then the known displacement D_{−ĉ}"; measure the output by heterodyne detection. Let Ȳ_i^± be the empirical means, and set
   - Â = [(Ȳ_i^+ − Ȳ_i^−)/(2η)]_i (a 2m × 2m matrix) and v̂ = (1/2m) Σ_i (Ȳ_i^+ + Ȳ_i^−)/2;
   - K̂ = P(log Â)/k, with the principal matrix logarithm;
   - T ← T e^{K̂} and ĉ ← e^{−K̂}(ĉ + v̂/k).
3. Output S̃ = T and r̃ = Tĉ.

Every T is symplectic, since e^{K̂} is for K̂ ∈ sp(2m). The total number of queries is 4mN_c + 4mN(2^{L+1} − 1), with N = ⌈100 t²/(η²γ²)⌉. This gives the bound of Theorem 1, since 2^L < 2 max{k_A, k_B, 1}, t² = O(m + log(L/δ)), η² = ñ/2, and η²γ² ≤ t², so that N ≥ 100 and N_c ≥ 800 and the ceilings at most double the counts. Every algorithm that uses only inputs of at most ñ ≤ n̄_in photons meets the constraint, so Lemma 4 below is applied with ñ in place of n̄_in.

## Proofs

**Facts.** For matrices X, Y and E, F:
- (F1) ‖e^X − e^Y‖ ≤ ‖X − Y‖ e^{max(‖X‖, ‖Y‖)}, and ‖e^X − 1‖ ≤ e^{‖X‖} − 1.
- (F2) If ‖E‖, ‖F‖ ≤ ρ < 1, then ‖log(1 + E) − log(1 + F)‖ ≤ ‖E − F‖/(1 − ρ), from the power series and ‖Eⁿ − Fⁿ‖ ≤ nρ^{n−1}‖E − F‖.
- (F3) log e^X = X for ‖X‖ < ln 2, and ‖log(1 + E)‖ ≤ −ln(1 − ‖E‖).
- (F4) If W is symplectic and ‖W − 1‖ < 1, then K = log W lies in sp(2m), since W^{−1} = Ω^{−1}WᵀΩ gives −K = Ω^{−1}KᵀΩ.
- (F5) P is a projection onto sp(2m) with ‖P(X)‖ ≤ ‖X‖, since X ↦ ΩXᵀΩ preserves the operator norm. A symplectic T has ‖T^{−1}‖ = ‖T‖.

**Lemma 3 (one chain).** With W = T^{−1}S and b = T^{−1}r − ĉ, one step is the Gaussian unitary D_b U_W. A chain of k steps maps |x⟩ to the Gaussian state with mean W^k x + M_k b, M_k = Σ_{j<k} W^j, and covariance W^k (W^k)ᵀ.

*Proof.* U_T^{−1} D_r U_S = D_{T^{−1}r} U_{T^{−1}S}, and D_{−ĉ} D_{T^{−1}r} = D_b. Displacements shift the mean, U_W acts by x ↦ Wx and V ↦ WVWᵀ. ∎

**Invariants at stage k.** Let K = log W. (I1) k‖K‖ ≤ γ. (I2) If k ≥ 2, then ‖b‖ ≤ η/(4k e^γ).

**Lemma 4 (energy).** Under (I1) and (I2), every state fed into G during stage k has mean photon number at most 0.92 ñ ≤ n̄_in.

*Proof.* The input of the (j + 1)-th query of a chain is the state of Lemma 3 after j < k steps. By (F1), ‖W^j‖ ≤ e^{j‖K‖} ≤ e^γ, so tr(W^j (W^j)ᵀ − 1)/4 ≤ m(e^{2γ} − 1)/2 ≤ 1.65 mγ ≤ 0.33 ñ, using e^{2γ} − 1 ≤ 2γe^{2γ} ≤ 3.3γ for γ ≤ 1/4 and γ ≤ ñ/(5m). For j ≥ 1 the chain has k ≥ 2, and ‖M_j b‖ ≤ j e^γ ‖b‖ ≤ η/4 by (I2), so the mean has norm at most (e^γ + 1/4)η and contributes (e^{1/4} + 1/4)² η²/2 ≤ 1.18 η² = 0.59 ñ. ∎

**Lemma 5 (estimation).** In stage k, with probability at least 1 − 2δ′,

‖Â − W^k‖ ≤ τ := 0.0814 γ   and   ‖v̂ − M_k b‖ ≤ 0.0145 η.

*Proof.* By Lemma 3 the heterodyne outcomes of the probe |±ηe_i⟩ are Gaussian with mean ±ηW^k e_i + M_k b and covariance Σ = (W^k(W^k)ᵀ + 1)/2, with ‖Σ‖ ≤ (e^{2γ} + 1)/2 ≤ 1.325. The columns of Â − W^k are independent with covariance Σ/(2η²N), so the operator-norm bound of [1, Lemma 4.2, eq. (4.33)] gives ‖Â − W^k‖ ≤ (1.325/(2η²N))^{1/2} t ≤ (1.325/200)^{1/2} γ ≤ 0.0814 γ. The vector v̂ − M_k b is Gaussian with covariance Σ/(4mN), and the norm of a standard Gaussian vector in ℝ^{2m} exceeds (2m)^{1/2} + (2 ln(1/δ′))^{1/2} with probability at most δ′, so ‖v̂ − M_k b‖ ≤ (1.325/(4mN))^{1/2} t ≤ (1.325/400)^{1/2} γη ≤ 0.0145 η. ∎

**Lemma 6 (one stage).** If (I1) and (I2) hold at stage k and the events of Lemma 5 occur, then after the update, with W′ = T′^{−1}S and b′ = T′^{−1}r − ĉ′:

‖W′ − 1‖ ≤ 0.21 γ/k,   ‖log W′‖ ≤ γ/(2k),   ‖b′‖ ≤ η/(8k e^γ),

so (I1) and (I2) hold at stage 2k.

*Proof.* By (I1) and (F3), log W^k = kK, and ‖W^k − 1‖ ≤ e^γ − 1 ≤ 0.2841. So ‖Â − 1‖ ≤ 0.2841 + τ ≤ 0.305, and (F2) gives ‖log Â − kK‖ ≤ τ/0.695 ≤ 1.44τ. Since kK ∈ sp(2m) by (F4), (F5) gives ‖K̂ − K‖ ≤ 1.44τ/k ≤ 0.118γ/k, and ‖K̂‖ ≤ 1.118γ/k ≤ 0.28.

Symplectic part. W′ = e^{−K̂}T^{−1}S = e^{−K̂}e^{K}, so by (F1) ‖W′ − 1‖ ≤ e^{‖K̂‖} ‖e^K − e^{K̂}‖ ≤ e^{0.56} · 0.118γ/k ≤ 0.21γ/k. By (F3), ‖log W′‖ ≤ −ln(1 − 0.21γ/k) ≤ 0.222γ/k.

Displacement part. Since T′ = Te^{K̂} and ĉ′ = e^{−K̂}(ĉ + v̂/k), b′ = e^{−K̂}(b − v̂/k) = e^{−K̂}((1 − M_k/k) b − (v̂ − M_k b)/k). For k = 1, M_1 = 1. For k ≥ 2, ‖1 − M_k/k‖ ≤ (1/k) Σ_{j<k} (e^{j‖K‖} − 1) ≤ e^γ − 1 ≤ 0.285 by (F1). With ‖e^{−K̂}‖ ≤ e^{0.28} ≤ 1.33 and (I2),

‖b′‖ ≤ 1.33 (0.285 η/(4k e^γ) + 0.0145 η/k) ≤ η/(8k e^γ),

because 1.33 (0.0713 + 0.0145 e^{1/4}) ≤ 0.12 ≤ 1/8. The case k = 1 gives ‖b′‖ ≤ 1.33 · 0.0145 η ≤ η/(8e^γ). ∎

**Coarse stage.** With N_c samples per probe, [1, Lemma 4.2] gives ‖Ŝ − S‖ ≤ ε₀ = γ/(40z³) with probability at least 1 − δ′, using inputs with mean photon number η²/2 ≤ ñ. Since (2z + 1)ε₀ < 1/2, [1, Lemma 4.3] gives ‖T − S‖ ≤ 9z²ε₀ ≤ 0.057, hence ‖T^{−1}‖ = ‖T‖ ≤ 1.06z and ‖T^{−1}S − 1‖ ≤ 1.06z · 9z²ε₀ ≤ 0.24γ. By (F3), ‖log W‖ ≤ 0.26γ, so (I1) holds at k = 1, and (I2) is not needed there.

*Proof of Theorem 1.* By a union bound, the coarse stage and the two events of Lemma 5 in each of the L + 1 stages hold together with probability at least 1 − (2L + 3)δ′ = 1 − δ. Then Lemmas 4 and 6 hold at every stage by induction, so every input of G has mean photon number at most n̄_in. After the last stage, with k_L = 2^L ≥ max{k_A, k_B}, let W = S̃^{−1}S and b = S̃^{−1}r − ĉ. Lemma 6 gives ‖W − 1‖ ≤ 0.21γ/k_L ≤ 0.0525, while ‖W‖ ≥ 1 since W is symplectic, and ‖b‖ ≤ η/(8k_L e^γ), and ‖S̃‖ ≤ ‖S‖ ‖W^{−1}‖ ≤ z e^{γ}, so ‖r̃ − r‖ = ‖S̃ b‖ ≤ zη/(8k_L).

By the triangle inequality, unitary invariance and the energy bound below,

½‖G̃ − G‖_{⋄,n̄} ≤ ½‖U_{S̃} − U_S‖_{⋄,n̄} + ½‖D_{r̃} − D_r‖_{⋄,n̄′}.

For the first term, [1, Proposition 2.2] (from [2, Theorem S12]) with S₁ = S, S₂ = S̃ and S₂^{−1}S₁ = W reads ½‖U_{S̃} − U_S‖_{⋄,n̄} ≤ ((6^{1/2} + 10^{1/2} + 5(2m)^{1/2})(n̄ + 1))^{1/2} g(‖W‖) ‖W − 1‖₂^{1/2} with g(x) = (π/(x + 1))^{1/2} + (2x)^{1/2}. Here 6^{1/2} + 10^{1/2} + 5(2m)^{1/2} ≤ 9(2m)^{1/2}, ‖W − 1‖₂ ≤ (2m)^{1/2}‖W − 1‖, and 1 ≤ ‖W‖ ≤ 1.06 gives g(‖W‖) ≤ (π/2)^{1/2} + 2.12^{1/2} ≤ 2.71. So ½‖U_{S̃} − U_S‖_{⋄,n̄} ≤ 2.71 (18 m (n̄ + 1) ‖W − 1‖)^{1/2} ≤ 2.71 (18 · 0.21 m (n̄ + 1) γ/k_L)^{1/2} ≤ ε/2, since k_L ≥ k_A and 4 · 2.71² · 18 · 0.21 ≤ 112. For the second term, [1, Proposition 2.1] gives ½‖D_{r̃} − D_r‖_{⋄,n̄′} ≤ (2(n̄′ + 1))^{1/2} ‖r̃ − r‖ ≤ (2(n̄′ + 1))^{1/2} zη/(8k_L) ≤ ε/2, since k_L ≥ k_B. ∎

*Energy bound.* With the quadrature vector R̂ and the energy Ê = R̂ᵀR̂/2 = N̂ + m/2, U_S^† Ê U_S = R̂ᵀSᵀSR̂/2 ≤ ‖S‖² Ê as operators, since ‖S‖²1 − SᵀS ⪰ 0. So U_S maps states with mean photon number at most n̄ (on the system, with any reference system) to states with mean photon number at most z²(n̄ + m/2) − m/2 ≤ n̄′. The squeezed vacuum shows that the additive term m/2 is needed: a single-mode squeezer with ‖S‖ = z maps the vacuum to (z² + z^{−2} − 2)/4 > 0 photons. In the proof of [1, Lemma 6.3], eq. (6.22) uses the photon number z²n̄ at this point; with z²(n̄ + m/2) − m/2 in its place, the condition on ε_r there holds with n̄ replaced by n̄ + m/2.

*Proof of Proposition 2.* Let k = ⌊π/θ⌋, so that k ≥ 2n̄ and p = n̄/k ≤ 1/2, and take the input |ψ⟩ = (1 − p)^{1/2}|0⟩ + p^{1/2}|k⟩ with mean photon number n̄. Then |⟨ψ|U_θ|ψ⟩|² = 1 − 2p(1 − p)(1 − cos kθ), and kθ ∈ (π − θ, π] gives 1 − cos kθ ≥ 1 + cos θ ≥ 1. The outputs are pure, so their trace distance is (2p(1 − p)(1 − cos kθ))^{1/2} ≥ p^{1/2} ≥ (n̄θ/π)^{1/2}, using p ≥ n̄θ/π. Finally ‖S_θ − 1‖ = 2 sin(θ/2) ≤ θ. ∎

## Check

`sim/doubling.py` runs the algorithm on random instances with m ∈ {1, 2}, z ∈ {1.5, 2}, n̄ ∈ {1, 2, 10}, n̄_in ∈ {1, 2, 4, 10⁴} (the last above the cap 32t²) and ε from 0.2 to 0.0125, propagating the first and second moments exactly and drawing each empirical mean from its exact law. It checks with asserts:

- the coarse estimate, the symplectic rounding and (I1) at k = 1;
- in every stage: (I1), (I2), both events of Lemma 5, the bounds of Lemma 6, and that T stays symplectic;
- that the mean photon number of the input of every query is at most 0.92ñ, at every step of chains with k ≤ 4096 and at 4096 evenly spaced steps and the last step of longer chains, and the chain moments of Lemma 3 against step-by-step composition for k ≤ 64;
- the final bound g(‖W‖)(18 m (n̄ + 1) ‖W − 1‖)^{1/2} + (2(n̄′ + 1))^{1/2} ‖r̃ − r‖ ≤ ε, and the query count against the formula;
- Proposition 2 for n̄ ∈ {1, 3, 10} and θ ∈ {0.05, 0.01, 0.002}, and the photon number of the squeezed vacuum.

The number of doubling-stage queries times ε² stays constant as ε decreases. Output in `sim/doubling_out.txt`.

## Lean

The folder [lean/](lean/) checks the scalar steps of the proofs in Lean 4 with Mathlib, with no `sorry` and only the standard axioms. Build it with `lake build`. Running `lake env lean GaussianDoubling/Axioms.lean` prints the axioms of each theorem (output in `lean/axioms.txt`).

**Checked** (`GaussianDoubling/Basic.lean`):

- **Exponential and logarithm bounds** (`exp_quarter_le`, `exp_half_le`, `exp_056_le`, `exp_028_le`, `exp_le_inv_one_sub`, `expm1_le_mul`, `neg_log_one_sub_le`): e^{1/4} ≤ 1.2841, e^{1/2} ≤ 1.6488, e^{0.56} ≤ 1.7541, e^{0.28} ≤ 1.33, e^x ≤ 1/(1 − x), e^x − 1 ≤ x e^x and −ln(1 − x) ≤ x/(1 − x).
- **Lemma 4** (`energy_le`): m(e^{2γ} − 1)/2 + (e^γ + 1/4)² η²/2 ≤ 0.92 ñ for η² = ñ/2, γ ≤ 1/4 and 5mγ ≤ ñ.
- **Lemma 5** (`sigma_le`, `tau_coef`, `nu_coef`): (e^{1/2} + 1)/2 ≤ 1.325, (1.325/200)^{1/2} ≤ 0.0814 and (1.325/400)^{1/2}/4 ≤ 0.0145.
- **Lemma 6** (`log_lip`, `khat_le`, `wprime_le`, `kappa_le`, `mk_le`, `b_update`, `b_update_one`): the radius 0.305 and constant 1.44 of the logarithm, 0.118 and 0.28 for K̂, e^{0.56} · 0.118 ≤ 0.21, −ln(1 − 0.21y) ≤ y/2 for y ≤ 1/4, e^{1/4} − 1 ≤ 0.285, and the two inequalities of the displacement update.
- **Coarse stage** (`coarse_norm`, `coarse_dist`, `coarse_log`): (2z + 1)ε₀ < 1/2, ‖T‖ ≤ 1.06z, ‖T^{−1}S − 1‖ ≤ 0.24γ and ‖log W‖ ≤ 0.26γ for ε₀ = γ/(40z³).
- **Final step** (`prop22_const`, `g_le`, `prop22_combine`, `final_sym`, `final_disp`): 6^{1/2} + 10^{1/2} + 5(2m)^{1/2} ≤ 9(2m)^{1/2}, g(x) ≤ 2.71 for 1 ≤ x ≤ 1.06, the two error terms are at most ε/2 for k_L ≥ k_A and k_L ≥ k_B.
- **Proposition 2** (`rotation_floor`, `rotation_p`, `rotation_dist`): ⌊π/θ⌋ ≥ 2n̄ for θ ≤ π/(2n̄ + 1), p ≥ n̄θ/π, and 2p(1 − p)(1 − c) ≥ p for p ≤ 1/2 and c ≤ 0.
- **Query count** (`geom_queries`): Σ_{t ≤ L} 2^t = 2^{L+1} − 1.

**Not formalized:** the matrix statements (Lemma 3, the matrix facts (F1) to (F5), the chain moments), the Gaussian tail bounds, the continuity bounds of [1, 2], the rounding of [1, Lemma 4.3] and the trace distance in Proposition 2.

## Scope

- Written proof with numerical checks, and the scalar steps checked in Lean. The bound of [1, Lemma 4.2, eq. (4.33)], the symplectic rounding [1, Lemma 4.3], the continuity bounds [1, Propositions 2.1 and 2.2] from [2], and the norm bound for standard Gaussian vectors are used as stated there.
- The queries are sequential and adaptive: the known Gaussian operations between queries depend on earlier outcomes, and a chain of length 2^L is coherent. The algorithm of [1] uses independent queries. With independent coherent-probe queries and heterodyne detection, the error of the matrix estimate decreases as the inverse square root of the number of queries, which together with Proposition 2 is the source of the 1/ε⁴.
- The constants are explicit and not optimized. No lower bound on the query complexity is given here.
- The bound uses at most ñ = min{n̄_in, 32t²} photons per input and does not improve with larger n̄_in.

## References

[1] M. Fanizza, V. Iyer, J. Lee, A. A. Mele, F. A. Mele. Efficient learning of bosonic Gaussian unitaries. arXiv:2510.05531 (v2).

[2] S. Becker, N. Datta, L. Lami, C. Rouzé. Energy-constrained discrimination of unitaries, quantum speed limits, and a Gaussian Solovay-Kitaev theorem. Physical Review Letters 126, 190504 (2021). arXiv:2006.06659.

[3] A. Christensen, A. Zhao. Learning fermionic linear optics with Heisenberg scaling and physical operations. arXiv:2602.05058.

[4] H. Li, Y. Tong, H. Ni, T. Gefen, L. Ying. Heisenberg-limited Hamiltonian learning for interacting bosons. arXiv:2307.04690.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
