# Learning non-unitary bosonic Gaussian channels in the energy-constrained diamond norm

2026-11-12

## Problem

An m-mode bosonic Gaussian channel Φ = Φ_{X,Y,d} acts on the first moments μ and the covariance matrix V of a state as

μ ↦ Xμ + d,   V ↦ XVXᵀ + Y,

with real 2m × 2m matrices X, Y = Yᵀ and d ∈ ℝ^{2m}, subject to Y + iΩ − iXΩXᵀ ⪰ 0. Here R = (x_1, p_1, …, x_m, p_m) with [x_j, p_k] = iδ_jk, Ω = ⊕_j [[0, 1], [−1, 0]], V = tr({R − μ, (R − μ)ᵀ}ρ), so the vacuum has V = 1, and N = Σ_j a_j†a_j. The error is measured in the energy-constrained diamond distance

d_E(Φ_1, Φ_2) = sup ½‖(id_S ⊗ Φ_1)(ρ) − (id_S ⊗ Φ_2)(ρ)‖_1,

over all reference systems S and states ρ on S ⊗ A with tr(ρ_A N) ≤ E.

For Gaussian unitaries (Y = 0, X symplectic) a learner with O(m⁴z⁸(E + 1)²(n̄_in + 1)^{1/2}(m + log(m/δ_f))/(n̄_in ε⁴)) parallel queries for n̄_in ≥ (2m)^{4/3} is given in [1, Remark 6.1], with failure probability δ_f. For non-unitary Gaussian channels no query bound was known: [1, Sec. 1.4] names perturbation bounds on the energy-constrained diamond distance between Gaussian channels as the main obstacle, and [2, Sec. 8] states that the general case of non-unitary Gaussian channels remains open.

## Results

Throughout, ‖X_i‖ ≤ z with z ≥ 1, ‖Y_i‖ ≤ y, m ≥ 1, ‖·‖ is the operator norm and ‖·‖_1 the trace norm. Write δ = ‖X_1 − X_2‖ + ‖Y_1 − Y_2‖ and

Q = 11 m z (z² + y) + √(z² + y) (2E + 3m).

Say that Φ_{X,Y,d} has noise margin ξ > 0 if Y − ξXXᵀ + iΩ − iXΩXᵀ ⪰ 0, that is, if Φ = Φ_{X, Y − ξXXᵀ, d} ∘ N_ξ with N_ξ = Φ_{1, ξ1, 0} the additive Gaussian noise channel.

**Theorem 1 (perturbation bounds).** Let Φ_i = Φ_{X_i, Y_i, d_i}, i = 1, 2, be Gaussian channels. In the last term of each bound below, z and y only need to bound ‖X_2‖ and ‖Y_2‖.

(a) If both channels have noise margin ξ ∈ (0, 1], then

d_E(Φ_1, Φ_2) ≤ δ (11 m z (z² + y)/ξ² + √(z² + y)(2E + 3m)/√ξ) + |d_1 − d_2| √(2z²E + z²m + my + 1).

(b) In general, for every ξ ∈ (0, 1],

d_E(Φ_1, Φ_2) ≤ 2√(mξ(2E + 1)) + δQ/ξ² + |d_1 − d_2| √(2z²E + z²m + my + 1),

and the choice of ξ gives, for all δ,

d_E(Φ_1, Φ_2) ≤ 2.88 (m(2E + 1))^{2/5} (Qδ)^{1/5} + |d_1 − d_2| √(2z²E + z²m + my + 1).

So the distance grows at most linearly with the parameter error for channels with a noise margin, and at most as its fifth root for all Gaussian channels, with explicit polynomial constants.

**Theorem 2 (learning).** Let ε ∈ (0, 1], and let z, y, E, ε, δ_f and, in the first case below, ξ be known. There is a learner that uses coherent input states with at most n̄_in photons, heterodyne detection and (4m + 1)N parallel queries to an unknown m-mode Gaussian channel Φ with ‖X‖ ≤ z and ‖Y‖ ≤ y, and outputs a Gaussian channel Φ̂ with d_E(Φ̂, Φ) ≤ ε with probability at least 1 − δ_f, where

N = O( (z² + y)(m² + log(1/δ_f)) ( (z²/n̄_in + (z² + y)/m)/δ_*² + (z²E + z²m + my)/ε² ) ),

with δ_* = 3ε/(4P) and P = 11 m z′(z′² + y′)/ξ² + √(z′² + y′)(2E + 3m)/√ξ, z′ = z + 1, y′ = y + 1, if Φ is known to have noise margin ξ ∈ (0, 1] (then Φ̂ has noise margin ξ as well), and with δ_* = (0.26ε)⁵/(Q′ m²(2E + 1)²) and Q′ = Q(z′, y′) in general. The explicit constants are in the proof.

For channels with a noise margin ξ this is O(poly(m, z, y, E, 1/ξ)(1 + 1/n̄_in) log(1/δ_f)/ε²) queries, since 1/δ_*² = O(P²/ε²). In general 1/δ_*² = O(Q′² m⁴ (2E + 1)⁴/ε¹⁰), so the number of queries is polynomial in m, z, y, E, 1/ε and log(1/δ_f). Examples of channels with a noise margin are thermal attenuators X = √η 1, Y = (1 − η)(2n_th + 1)1 with n_th > 0 (margin min{1, 2n_th(1 − η)/η}), amplifiers above the quantum limit, and every channel Φ ∘ N_ξ with Gaussian noise at the input (margin min{1, ξ}).

Many channels without a noise margin, such as pure loss, quantum-limited amplifiers and phase-conjugating channels, have a non-degenerate matrix A = Ω − XΩXᵀ. For them the distance has the square-root form of the unitary case. Write Z = 1 + z² and, for a > 0, K = Z/a.

**Theorem 3 (square-root continuity).** Let Φ_i = Φ_{X_i, Y_i, d_i}, i = 1, 2, with ‖X_i‖ ≤ z, ‖Y_i‖ ≤ y and smallest singular value σ_min(Ω − X_iΩX_iᵀ) ≥ a > 0. Then

d_E(Φ_1, Φ_2) ≤ 382 Z² K^{5/2} (m(E + my/(2a) + 1)‖X_1 − X_2‖)^{1/2} + 0.7 m y a^{−2} (18 y K^{7/2} ‖X_1 − X_2‖ + ‖Y_1 − Y_2‖) + |d_1 − d_2| √(2z²E + z²m + my + 1).

**Theorem 4 (learning with 1/ε⁴).** Let ε ∈ (0, 1], and let z, y, a, E, ε, δ_f be known. For an unknown m-mode Gaussian channel Φ with ‖X‖ ≤ z, ‖Y‖ ≤ y and σ_min(Ω − XΩXᵀ) ≥ a, the learner of Theorem 2 (with ξ = 0) outputs a Gaussian channel Φ̂ with d_E(Φ̂, Φ) ≤ ε with probability at least 1 − δ_f after (4m + 1)N queries, where

N = O( (z² + y)(m² + log(1/δ_f)) ( z²/(n̄_in Δ_*²) + (z² + y)/(m λ_*²) + (z²E + z²m + my)/ε² ) ),

Δ_* = min{ ε²/(4 · 382² Z′⁴K′⁵ m(E + my′/a′ + 1)), ε a′²/(101 m y′² K′^{7/2}), a/(4(2z + 1)), λ_*/(4(2z + 1)) }, λ_* = min{ ε a′²/(11.2 m y′), 1/2 }, with z′ = z + 1, y′ = y + 1, a′ = a/2, Z′ = 1 + z′², K′ = Z′/a′. This is O(poly(m, z, y, 1/a)(E + my/a + 1)²(1 + 1/n̄_in) log(1/δ_f)/ε⁴) queries, the same power of 1/ε as for Gaussian unitaries in [1]. For one mode, σ_min(Ω − XΩXᵀ) = |1 − det X|, so the condition holds for every one-mode channel with det X ≠ 1.

## Proofs

*Facts used.*

- (F1) Moments. For every state with finite second moments, Φ_{X,Y,d} maps μ ↦ Xμ + d and V ↦ XVXᵀ + Y. With ⟨RᵀR⟩ = ½ tr V + |μ|² = 2⟨N⟩ + m, the output energy of Φ_{X,Y,0} on inputs with ⟨N⟩ ≤ E is at most ‖X‖²(E + m/2) + tr(Y)/4 − m/2 ≤ z²(E + m/2) + my/2, since tr(XVXᵀ) ≤ ‖X‖² tr V and |Xμ| ≤ ‖X‖|μ|.
- (F2) Covariance. For the displacement operators D_w, with D_w† R D_w = R + w, Gaussian channels satisfy Φ_{X,Y,d}(D_w ρ D_w†) = D_{Xw} Φ_{X,Y,d}(ρ) D_{Xw}†. In the dual picture, acting on observables, Φ* maps W(k) = e^{ikᵀR} to W(Xᵀk) e^{ikᵀd − kᵀYk/4}, and D_w† W(k) D_w = e^{ikᵀw} W(k), so Φ*(D_{Xw}† W(k) D_{Xw}) = e^{ikᵀXw} Φ*(W(k)) = D_w† Φ*(W(k)) D_w.
- (F3) Displacement continuity. If σ is a state on S ⊗ B with tr(σ_B N) ≤ n, then ½‖D_w σ D_w† − σ‖_1 ≤ |w|√(2n + 1). For a purification φ, ½‖D_wφD_w† − φ‖_1 = (1 − |⟨φ|D_w|φ⟩|²)^{1/2} ≤ ‖(D_w − 1)φ‖ ≤ ‖Gφ‖, where D_w = e^{−iG} with G = |w| uᵀR for a unit vector u (u = ±Ωw/|w|). With uᵀR = (b + b†)/√2 for a normalized mode b, (uᵀR)² ≤ 2b†b + 1 ≤ 2N + 1, so ‖Gφ‖² ≤ |w|²(2n + 1). Consequently d_E(id, N_ξ) ≤ √(mξ(2E + 1)): N_ξ is the average of D_w · D_w† over w ~ 𝒩(0, (ξ/2)1_{2m}), and E|w| ≤ (E|w|²)^{1/2} = √(mξ).
- (F4) Teleportation [4], [5, Eq. (11)], for arbitrary input states. Let τ_r be the two-mode squeezed vacuum on modes R, B (m pairs), with covariance [[c1, sZ], [sZ, c1]], c = cosh 2r, s = sinh 2r, Z = ⊕_j diag(1, −1). Measure x_A − x_R and p_A + p_R in every mode of an input ρ on S ⊗ A and of R, with outcome q ∈ ℝ^{2m}, and apply D_q to B. The averaged output is (id_S ⊗ N_ξ)(ρ) with ξ = 2e^{−2r}. The outcome satisfies E|q|² = ⟨R_AᵀR_A⟩ + ⟨R_RᵀR_R⟩ ≤ 2E + m(1 + c).
- (F5) Trace distance of Gaussian states [3, Theorem 3]. For Gaussian states with covariance matrices V, W and equal first moments, ½‖ρ(V) − ρ(W)‖_1 ≤ (1 + √3)/8 · tr(|V − W| Ωᵀ (V + W)/2 Ω) ≤ (1 + √3)/8 · max(‖V‖, ‖W‖) ‖V − W‖_1.
- (F6) Gaussian unitaries [1, Proposition 2.2], from [7]. For symplectic S_1, S_2 on M modes and W = S_2^{−1}S_1, ½‖U_{S_1} − U_{S_2}‖_{⋄,E} ≤ ((6^{1/2} + 10^{1/2} + 5(2M)^{1/2})(E + 1))^{1/2} g(‖W‖) ‖W − 1‖_2^{1/2}, with g(x) = (π/(x + 1))^{1/2} + (2x)^{1/2} and ‖·‖_2 the Frobenius norm. A symplectic matrix S satisfies ‖S^{−1}‖ = ‖S‖ and ‖S‖ ≥ 1.

*Lemma 3 (teleportation simulation).* Let Φ_i′ = Φ_{X_i, Y_i′, 0} and Ψ_i = Φ_i′ ∘ N_ξ with ξ = 2e^{−2r} ∈ (0, 1], ‖X_i‖ ≤ z with z ≥ 1, ‖Y_i′‖ ≤ y, and let E_2 bound the output energy of Ψ_2 on inputs with energy E. With a = e^{2r} = 2/ξ,

d_E(Ψ_1, Ψ_2) ≤ (1 + √3)/8 · (z²a + y)(a(1 + 2z)‖X_1 − X_2‖_1 + ‖Y_1′ − Y_2′‖_1) + ‖X_1 − X_2‖ √(2E + m(1 + c)) √(2E_2 + 1).

*Proof.* Let ω_i = (id_R ⊗ Φ_i′)(τ_r), a zero-mean Gaussian state with covariance V_i = [[c1, sZX_iᵀ], [sX_iZ, cX_iX_iᵀ + Y_i′]]. For a state ω on R ⊗ B and a matrix X let T_{X,ω} be the protocol of (F4) with resource ω and correction D_{Xq}. Since Φ_i′ acts on B, it commutes with the measurement on A and R; if σ_q is the post-measurement state of B for the resource τ_r, the protocol with resource ω_i leaves Φ_i′(σ_q), and by (F2) and (F4)

T_{X_i, ω_i}(ρ) = ∫ D_{X_i q} Φ_i′(σ_q) D_{X_i q}† p(q) dq = Φ_i′(∫ D_q σ_q D_q† p(q) dq) = Φ_i′(N_ξ(ρ)) = Ψ_i(ρ).

For a fixed input, ω ↦ T_{X,ω}(ρ) is a channel (append ρ, measure, displace), so ½‖T_{X_1,ω_1}(ρ) − T_{X_1,ω_2}(ρ)‖_1 ≤ ½‖ω_1 − ω_2‖_1. By (F5) this is at most (1 + √3)/8 · max_i ‖V_i‖ · ‖V_1 − V_2‖_1. Here V_i = diag(1, X_i)[[c1, sZ], [sZ, c1]]diag(1, X_i)ᵀ + diag(0, Y_i′) gives ‖V_i‖ ≤ z²(c + s) + y = z²a + y, and

‖V_1 − V_2‖_1 ≤ 2s‖X_1 − X_2‖_1 + c‖X_1X_1ᵀ − X_2X_2ᵀ‖_1 + ‖Y_1′ − Y_2′‖_1 ≤ a(1 + 2z)‖X_1 − X_2‖_1 + ‖Y_1′ − Y_2′‖_1,

using 2s ≤ a, c ≤ a and ‖X_1X_1ᵀ − X_2X_2ᵀ‖_1 ≤ 2z‖X_1 − X_2‖_1.

For the corrections, let κ_q = D_{X_2q} Φ_2′(σ_q) D_{X_2q}†, a state on S ⊗ B with ∫ κ_q p(q) dq = Ψ_2(ρ). Since D_{X_1q} D_{X_2q}† equals D_{(X_1 − X_2)q} up to a phase,

T_{X_1,ω_2}(ρ) − T_{X_2,ω_2}(ρ) = ∫ (D_{(X_1−X_2)q} κ_q D_{(X_1−X_2)q}† − κ_q) p(q) dq.

By (F3) with n_q = tr(κ_q N_B), and E[XY] ≤ (E[X²] E[Y²])^{1/2},

½‖T_{X_1,ω_2}(ρ) − T_{X_2,ω_2}(ρ)‖_1 ≤ ‖X_1 − X_2‖ ∫ |q| √(2n_q + 1) p(q) dq ≤ ‖X_1 − X_2‖ (E|q|²)^{1/2} (2 ∫ n_q p(q) dq + 1)^{1/2},

and ∫ n_q p(q) dq = tr(Ψ_2(ρ) N) ≤ E_2. ∎

*Proof of Theorem 1.* The first moment shift: Φ_{X,Y,d} = D_d Φ_{X,Y,0}(·) D_d†, so by the triangle inequality and (F3), d_E(Φ_1, Φ_2) ≤ d_E(Φ_{X_1,Y_1,0}, Φ_{X_2,Y_2,0}) + |d_1 − d_2| √(2E_out + 1), with E_out ≤ z²(E + m/2) + my/2 the output energy of Φ_{X_2,Y_2,0} by (F1). Set d_i = 0 from now on.

(a) Apply Lemma 3 with Φ_i′ = Φ_{X_i, Y_i − ξX_iX_iᵀ, 0}, so Ψ_i = Φ_i. Here 0 ⪯ Y_i′ ⪯ Y_i gives ‖Y_i′‖ ≤ y, ‖Y_1′ − Y_2′‖ ≤ ‖Y_1 − Y_2‖ + 2ξz‖X_1 − X_2‖, and E_2 ≤ z²(E + m/2) + my/2.

(b) By (F3) and data processing, d_E(Φ_i, Φ_i ∘ N_ξ) ≤ d_E(id, N_ξ) ≤ √(mξ(2E + 1)). Apply Lemma 3 to Ψ_i = Φ_i ∘ N_ξ with Φ_i′ = Φ_i; here E_2 ≤ z²(E + m(1 + ξ)/2) + my/2 by (F1), since N_ξ adds mξ/2 to the energy.

The simplified forms: with ‖·‖_1 ≤ 2m‖·‖ on 2m × 2m matrices, a ≥ 2 and z ≥ 1, the first term of Lemma 3 is at most (1 + √3)/8 · 2m(z² + y)a · 4za δ ≤ 11 m z (z² + y) δ/ξ² in case (a) and ≤ 8.2 m z (z² + y) δ/ξ² in case (b). For the second term, 1 + c = 1 + 1/ξ + ξ/4 ≤ 2.25/ξ, 2E_2 + 1 ≤ (z² + y)(2E + 2m + 1), and the inequality of arithmetic and geometric means gives √((2E + 2.25m)(2E + 2m + 1)) ≤ 2E + 3m, so the second term is at most ‖X_1 − X_2‖ √(z² + y)(2E + 3m)/√ξ, and 1/√ξ ≤ 1/ξ² in (b). Finally, A√ξ + B/ξ² with A = 2√(m(2E + 1)), B = Qδ is minimized at ξ = (4B/A)^{2/5} with value (5/4)4^{1/5} A^{4/5} B^{1/5} ≤ 2.88 (m(2E + 1))^{2/5} B^{1/5}, and this ξ lies in (0, 1] when 4B ≤ A. If 4B > A, then 2.88 (m(2E + 1))^{2/5} B^{1/5} > 2.88 · 2^{−1/5} (m(2E + 1))^{1/2} > 1 ≥ d_E. ∎

*Proof of Theorem 2.* The learner sends N copies of each of the coherent states with mean vectors 0 and ±αe_j, j = 1, …, 2m, with α = √(2n̄_in) (photon number α²/2 = n̄_in), and heterodynes every output. For a coherent input with mean μ_in the output is Gaussian, and the heterodyne outcome is distributed as 𝒩(Xμ_in + d, Σ) with Σ = (XXᵀ + Y + 1)/2, ‖Σ‖ ≤ σ² := (z² + y + 1)/2. Estimates:

- d̂ = mean of the outcomes for input 0, so d̂ − d ~ 𝒩(0, Σ/N) and |d̂ − d| ≤ b_d = σ(√(2m) + √(2 log(3/δ_f)))/√N with probability at least 1 − δ_f/3, by concentration of Gaussian vectors, |g| ≤ (tr C)^{1/2} + (2‖C‖ log(1/δ))^{1/2} for g ~ 𝒩(0, C).
- X̂e_j = (μ̂_{+j} − μ̂_{−j})/(2α) from the outcome means. The columns of X̂ − X are independent 𝒩(0, Σ/(2α²N)), so ‖X̂ − X‖ ≤ ‖X̂ − X‖_F ≤ b_X = σ(2m + √(2 log(3/δ_f)))/(α√(2N)) with probability at least 1 − δ_f/3.
- Σ̂ = (1/n) Σ_k w_k w_kᵀ over the n = (4m + 1)⌊N/2⌋ differences w_k = (u − u′)/√2 of disjoint pairs of outcomes from the same input, which are independent 𝒩(0, Σ). By the singular value bound for Gaussian matrices [6, Chapter 6], ‖Σ̂ − Σ‖ ≤ b_Σ = σ²(2t + t²) with t = √(2m/n) + √(2 log(6/δ_f)/n), with probability at least 1 − δ_f/3.
- Ŷ = 2Σ̂ − 1 − X̂X̂ᵀ + λ1 with λ = 2b_Σ + (2 + ξ)(2z + b_X)b_X, where ξ is the known noise margin, or ξ = 0 in general.

On the joint success event, ‖Ŷ − λ1 − Y‖ ≤ 2b_Σ + ‖X̂X̂ᵀ − XXᵀ‖, and ‖X̂X̂ᵀ − XXᵀ‖, ‖X̂ΩX̂ᵀ − XΩXᵀ‖ ≤ (2z + b_X)b_X. Hence

Ŷ − ξX̂X̂ᵀ + iΩ − iX̂ΩX̂ᵀ = (Y − ξXXᵀ + iΩ − iXΩXᵀ) + (Ŷ − λ1 − Y) − ξ(X̂X̂ᵀ − XXᵀ) − i(X̂ΩX̂ᵀ − XΩXᵀ) + λ1 ⪰ 0,

so Φ̂ = Φ_{X̂,Ŷ,d̂} is a Gaussian channel, with noise margin ξ if Φ has it, and ‖Ŷ − Y‖ ≤ 2λ. Suppose b_X ≤ δ_*/(24(2z + 1)) and b_Σ ≤ δ_*/16. Since ε ≤ 1 and P, Q′ ≥ 22, δ_* ≤ 2, so b_X ≤ 1/2 and λ ≤ δ_*/8 + δ_*/8 ≤ 1/2. Then ‖X̂ − X‖ + ‖Ŷ − Y‖ ≤ δ_*, ‖X̂‖ ≤ z′ and ‖Ŷ‖ ≤ y′. Theorem 1(a) with the constant P, or Theorem 1(b) with Q′ = Q(z′, y′) and δ_* = (0.26ε)⁵/(Q′ m²(2E + 1)²), which gives 2.88(m(2E + 1))^{2/5}(Q′δ_*)^{1/5} ≤ 3ε/4, bounds the distance by 3ε/4 plus the displacement term, applied with Φ_2 = Φ, so that its last term uses the true bounds z and y. The displacement term is at most ε/4 if b_d ≤ ε/(4√(2z²E + z²m + my + 1)). The three conditions on b_X, b_Σ and b_d hold for the N below, where the second entry uses ⌊N/2⌋ ≥ (N − 1)/2 and t ≤ δ_*/(48σ²) ≤ 1, so that 2t + t² ≤ 3t:

N ≥ max{ 144(2z + 1)²σ²(2m + √(2 log(3/δ_f)))²/(n̄_in δ_*²),  2(48σ²/δ_*)²(√(2m) + √(2 log(6/δ_f)))²/(4m + 1) + 2,  16σ²(√(2m) + √(2 log(3/δ_f)))²(2z²E + z²m + my + 1)/ε² }. ∎

*Lemma 5 (dilation).* Let A = Ω − XΩXᵀ be invertible. A is antisymmetric, so A = J|A| with |A| = (AᵀA)^{1/2} and J = A|A|^{−1} orthogonal, antisymmetric and commuting with |A|. Choose an orthogonal O with OΩOᵀ = J (from the real normal form of J) and set M = |A|^{1/2}O, so that MΩMᵀ = A. Let B = Ω − ΩXᵀA^{−1}XΩᵀ, which is antisymmetric with B^{−1} = −(Ω − XᵀΩX), as the matrix inversion formula shows. With B = J_B|B| and an orthogonal O_B with O_BΩO_Bᵀ = J_B, set C = O_Bᵀ|B|^{−1/2} and D = CΩXᵀM^{−ᵀ}Ω. Then S = [[X, M], [C, D]] is symplectic on 2m modes: XΩXᵀ + MΩMᵀ = Ω by the definition of A, XΩCᵀ + MΩDᵀ = 0 by the choice of D, and CΩCᵀ + DΩDᵀ = C(Ω − ΩXᵀA^{−1}XΩᵀ)Cᵀ = CBCᵀ = Ω, using M^{−ᵀ}ΩM^{−1} = −A^{−1}. For a valid Y let γ be the zero-mean Gaussian state of m modes with covariance V_E = M^{−1}YM^{−ᵀ}; it is a covariance matrix since V_E + iΩ = M^{−1}(Y + iA)M^{−ᵀ} ⪰ 0. Then Φ_{X,Y,0}(ρ) = tr_E U_S(ρ ⊗ γ)U_S†, since the right side is a Gaussian channel with matrices X and XVXᵀ + MV_EMᵀ − XVXᵀ = Y.

Bounds, with σ_min(A) ≥ a, ‖X‖ ≤ z: ‖A‖ ≤ Z, ‖M‖ ≤ Z^{1/2}, ‖M^{−1}‖ ≤ a^{−1/2}, ‖B‖ ≤ 1 + z²/a ≤ 2K, σ_min(B) = 1/‖Ω − XᵀΩX‖ ≥ 1/Z, ‖C‖ ≤ Z^{1/2}, ‖D‖ ≤ Z/a^{1/2}, so ‖S‖ ≤ z + 2Z^{1/2} + Z/a^{1/2} ≤ 4Z/a^{1/2}, and ‖V_E‖ ≤ y/a, so γ has at most my/(2a) photons.

*Lemma 6 (Lipschitz dilations).* Let X_1, X_2 satisfy the bounds of Lemma 5 with Δ = ‖X_1 − X_2‖ ≤ 1/(10Z³K⁴), and let S_1 be the dilation of X_1 for some choices O_1, O_{B,1}. Then there is a dilation S_2 of X_2 with ‖S_1 − S_2‖ ≤ 104 Z^{7/2}K^{9/2} Δ.

*Proof.* For orthogonal antisymmetric J_1, J_2 with ‖J_1 − J_2‖ < 2, T = (1 − J_2J_1)/2 satisfies J_2T = TJ_1 and ‖T − 1‖ = ‖(J_1 − J_2)J_1‖/2 =: t. Its polar factor P = T|T|^{−1} is orthogonal with PJ_1 = J_2P, since TᵀT commutes with J_1, and ‖P − 1‖ ≤ ‖1 − |T|‖ + t ≤ ‖1 − TᵀT‖ + t ≤ 3t + t² ≤ 8t for t ≤ 1/2. So O_2 = PO_1 satisfies O_2ΩO_2ᵀ = J_2. The steps, using ‖√P − √Q‖ ≤ ‖P − Q‖/(σ_min(√P) + σ_min(√Q)) for positive P, Q, and ‖P^{−1} − Q^{−1}‖ ≤ ‖P^{−1}‖‖Q^{−1}‖‖P − Q‖:

- ‖A_1 − A_2‖ ≤ 2zΔ ≤ ZΔ, ‖|A_1| − |A_2|‖ ≤ 2Z‖A_1 − A_2‖/(2a) ≤ ZKΔ, ‖|A_1|^{1/2} − |A_2|^{1/2}‖ ≤ ZKΔ/(2a^{1/2}), ‖J_1 − J_2‖ ≤ ZΔ/a + Z · ZKΔ/a² = (K + K³)Δ, so t ≤ K³Δ ≤ 1/2 and ‖P − 1‖ ≤ 8K³Δ;
- ‖M_1 − M_2‖ ≤ Z^{1/2} · 8K³Δ + Z^{1/2}K^{3/2}Δ/2 ≤ 9Z^{1/2}K³Δ, and ‖M_1^{−1} − M_2^{−1}‖ ≤ 9Z^{1/2}K³Δ/a;
- ‖B_1 − B_2‖ ≤ 2zΔ/a + z²‖A_1 − A_2‖/a² ≤ 2K²Δ, ‖|B_1| − |B_2|‖ ≤ 4K · 2K²Δ · Z/2 = 4ZK³Δ, ‖|B_1|^{−1/2} − |B_2|^{−1/2}‖ ≤ Z · 4ZK³Δ · Z^{1/2}/2 = 2Z^{5/2}K³Δ, ‖J_{B,1} − J_{B,2}‖ ≤ 2K²Δ · Z + 2K · Z² · 4ZK³Δ ≤ 10Z³K⁴Δ, so t_B ≤ 5Z³K⁴Δ ≤ 1/2 and ‖P_B − 1‖ ≤ 40Z³K⁴Δ;
- ‖C_1 − C_2‖ ≤ 40Z³K⁴Δ · Z^{1/2} + 2Z^{5/2}K³Δ ≤ 42Z^{7/2}K⁴Δ;
- ‖D_1 − D_2‖ ≤ ‖C_1 − C_2‖ z a^{−1/2} + Z^{1/2}Δ a^{−1/2} + Z^{1/2} z ‖M_1^{−1} − M_2^{−1}‖ ≤ (42 + 1 + 9)Z^{7/2}K^{9/2}Δ.

Summing the four blocks gives (1 + 9 + 42 + 52)Z^{7/2}K^{9/2}Δ. ∎

*Proof of Theorem 3.* The first moment shift is handled as in Theorem 1. Let d_i = 0, and let Δ = ‖X_1 − X_2‖. If Δ > 1/(416Z⁴K⁵), the first term exceeds 382/416^{1/2} > 1 ≥ d_E. Otherwise take the dilations S_1, S_2 of Lemma 6 with environment states γ_1, γ_2. Then

d_E(Φ_1, Φ_2) ≤ ½‖γ_1 − γ_2‖_1 + ½‖U_{S_1} − U_{S_2}‖_{⋄, E + my/(2a)},

since inputs ρ ⊗ γ_2 have at most E + my/(2a) photons. For the second term, W = S_2^{−1}S_1 has ‖W − 1‖ ≤ ‖S_2‖‖S_1 − S_2‖ ≤ 4Z a^{−1/2} · 104Z^{7/2}K^{9/2}Δ = 416Z⁴K⁵Δ ≤ 1, so 1 ≤ ‖W‖ ≤ 2 and g(‖W‖) ≤ 3.3. By (F6) with M = 2m, 6^{1/2} + 10^{1/2} + 10m^{1/2} ≤ 16m^{1/2} and ‖W − 1‖_2 ≤ 2m^{1/2}‖W − 1‖, the second term is at most 3.3(32m(E + my/(2a) + 1)‖W − 1‖)^{1/2} ≤ 18.7 · 416^{1/2} Z²K^{5/2}(m(E + my/(2a) + 1)Δ)^{1/2}. For the first term, (F5) gives ½‖γ_1 − γ_2‖_1 ≤ (1 + √3)/8 · (y/a) · 2m‖V_{E,1} − V_{E,2}‖, and

‖V_{E,1} − V_{E,2}‖ ≤ 2‖M_1^{−1} − M_2^{−1}‖ y a^{−1/2} + ‖Y_1 − Y_2‖/a ≤ 18 y K³ Z^{1/2} a^{−3/2} Δ + ‖Y_1 − Y_2‖/a,

with K³Z^{1/2}a^{−3/2} = K^{7/2}/a. ∎

*Proof of Theorem 4.* The estimates and the repair are those of Theorem 2 with ξ = 0. On the success event, ‖Â − A‖ ≤ (2z + b_X)b_X ≤ a/2 when b_X ≤ a/(4(2z + 1)), so σ_min(Ω − X̂ΩX̂ᵀ) ≥ a′, and ‖X̂‖ ≤ z′, ‖Ŷ‖ ≤ y′ when b_X ≤ 1/2 and λ ≤ 1/2. Theorem 3 with a′, z′, y′ and Φ_2 = Φ in the last term bounds d_E(Φ̂, Φ) by ε/2 + ε/8 + ε/8 + ε/4 if b_X ≤ Δ_* and 2λ ≤ 2λ_*: the first term is at most ε/2 by the first entry of Δ_*, the X part of the second at most ε/8 by the second entry (0.7 · 18 · 8 ≤ 101), the Y part, with ‖Ŷ − Y‖ ≤ 2λ, at most ε/8 by λ_*, and the displacement term at most ε/4 under the condition on b_d of Theorem 2. These hold for N as stated, by the bounds on b_X, b_Σ, b_d in the proof of Theorem 2, with λ = 2b_Σ + 2(2z + b_X)b_X ≤ λ_* when b_Σ ≤ λ_*/4 and b_X ≤ λ_*/(4(2z + 1)) ≤ 1/8. ∎

## Check

`sim/` contains scripts with asserts:

- `teleport.py`: for random channels on m = 1, 2, 3 modes, random Gaussian inputs and squeezing r, the teleportation protocol of Lemma 3 with correction D_{Xq} reproduces the first and second moments of Φ′ ∘ N_ξ with ξ = 2e^{−2r} (homodyne conditioning of the joint Gaussian state), E|q|² = ⟨R_AᵀR_A⟩ + m cosh 2r, and the bounds on ‖V_i‖ and ‖V_1 − V_2‖_1.
- `fock_check.py`: in a truncated photon-number basis, (F5) on 40 random pairs of one-mode Gaussian states (largest ratio of the two sides 0.64), and Theorem 1(b) for pure-loss channels with transmissivities η and η + Δη, on a two-mode squeezed input with E = 0.5 and 2 (for Δη = 10⁻⁶ the bound is below 1).
- `learn.py`: 300 runs each of the learner on random one- and two-mode channels, with and without a noise margin. The error bounds b_d, b_X, b_Σ hold in all runs, and the repaired Ŷ always gives a valid channel with the required noise margin.
- `queries.py`: the simplified forms of Theorem 1 dominate the explicit form of Lemma 3 on 20000 random parameter sets, and the query numbers of Theorem 2 for example parameters.
- `dilation.py`: the dilation of Lemma 5 for 600 random channels on m = 1, 2, 3 modes is symplectic, reproduces (X, Y) and has a valid environment state, ‖S‖ ≤ 4Z/a^{1/2}, and on 453 nearby pairs the transported dilations of Lemma 6 satisfy ‖S_1 − S_2‖ ≤ 0.053 Z^{7/2}K^{9/2}‖X_1 − X_2‖, against the proven 104.
- `dil_check.py`: the numerical constants in the proof of Theorem 3.
- `bounds.py`: the bounds as functions.

Output in `sim/out.txt`.

## Scope

- Written proof with numerical checks. Facts (F4), (F5), (F6) and the concentration bounds for Gaussian vectors and matrices are taken from [1], [3], [4], [5], [6], [7].
- The constants are large. The exponent 10 of 1/ε for general channels is not shown to be tight; Theorems 2 and 4 give 1/ε² with a noise margin and 1/ε⁴ when σ_min(Ω − XΩXᵀ) ≥ a, and [1] gives 1/ε⁴ for Gaussian unitaries. Channels near both boundaries, such as a unitary followed by weak noise, are covered only by the general bound.
- Theorem 3 uses the continuity bound (F6) for Gaussian unitaries from [1], [7].
- The noise margin ξ in Theorem 2 and the bound a in Theorem 4 enter as known prior information.

## References

[1] M. Fanizza, V. Iyer, J. Lee, A. A. Mele, F. A. Mele. Efficient learning of bosonic Gaussian unitaries. arXiv:2510.05531 (v2).

[2] F. A. Mele. Advances in quantum learning theory with bosonic systems. Il Nuovo Cimento C 49, 137 (2026). arXiv:2605.08082.

[3] L. Bittel, F. A. Mele, A. A. Mele, S. Tirone, L. Lami. Optimal estimates of trace distance between bosonic Gaussian states and applications to learning. Quantum 9, 1769 (2025). arXiv:2411.02368.

[4] S. L. Braunstein, H. J. Kimble. Teleportation of continuous quantum variables. Physical Review Letters 80, 869 (1998).

[5] M. M. Wilde. Strong and uniform convergence in the teleportation simulation of bosonic Gaussian channels. Physical Review A 97, 062305 (2018). arXiv:1712.00145.

[6] M. J. Wainwright. High-Dimensional Statistics: A Non-Asymptotic Viewpoint. Cambridge University Press (2019).

[7] S. Becker, N. Datta, L. Lami, C. Rouzé. Energy-constrained discrimination of unitaries, quantum speed limits, and a Gaussian Solovay-Kitaev theorem. Physical Review Letters 126, 190504 (2021). arXiv:2006.06659.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
