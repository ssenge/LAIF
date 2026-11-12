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

## Proofs

*Facts used.*

- (F1) Moments. For every state with finite second moments, Φ_{X,Y,d} maps μ ↦ Xμ + d and V ↦ XVXᵀ + Y. With ⟨RᵀR⟩ = ½ tr V + |μ|² = 2⟨N⟩ + m, the output energy of Φ_{X,Y,0} on inputs with ⟨N⟩ ≤ E is at most ‖X‖²(E + m/2) + tr(Y)/4 − m/2 ≤ z²(E + m/2) + my/2, since tr(XVXᵀ) ≤ ‖X‖² tr V and |Xμ| ≤ ‖X‖|μ|.
- (F2) Covariance. For the displacement operators D_w, with D_w† R D_w = R + w, Gaussian channels satisfy Φ_{X,Y,d}(D_w ρ D_w†) = D_{Xw} Φ_{X,Y,d}(ρ) D_{Xw}†. In the dual picture, acting on observables, Φ* maps W(k) = e^{ikᵀR} to W(Xᵀk) e^{ikᵀd − kᵀYk/4}, and D_w† W(k) D_w = e^{ikᵀw} W(k), so Φ*(D_{Xw}† W(k) D_{Xw}) = e^{ikᵀXw} Φ*(W(k)) = D_w† Φ*(W(k)) D_w.
- (F3) Displacement continuity. If σ is a state on S ⊗ B with tr(σ_B N) ≤ n, then ½‖D_w σ D_w† − σ‖_1 ≤ |w|√(2n + 1). For a purification φ, ½‖D_wφD_w† − φ‖_1 = (1 − |⟨φ|D_w|φ⟩|²)^{1/2} ≤ ‖(D_w − 1)φ‖ ≤ ‖Gφ‖, where D_w = e^{−iG} with G = |w| uᵀR for a unit vector u (u = ±Ωw/|w|). With uᵀR = (b + b†)/√2 for a normalized mode b, (uᵀR)² ≤ 2b†b + 1 ≤ 2N + 1, so ‖Gφ‖² ≤ |w|²(2n + 1). Consequently d_E(id, N_ξ) ≤ √(mξ(2E + 1)): N_ξ is the average of D_w · D_w† over w ~ 𝒩(0, (ξ/2)1_{2m}), and E|w| ≤ (E|w|²)^{1/2} = √(mξ).
- (F4) Teleportation [4], [5, Eq. (11)], for arbitrary input states. Let τ_r be the two-mode squeezed vacuum on modes R, B (m pairs), with covariance [[c1, sZ], [sZ, c1]], c = cosh 2r, s = sinh 2r, Z = ⊕_j diag(1, −1). Measure x_A − x_R and p_A + p_R in every mode of an input ρ on S ⊗ A and of R, with outcome q ∈ ℝ^{2m}, and apply D_q to B. The averaged output is (id_S ⊗ N_ξ)(ρ) with ξ = 2e^{−2r}. The outcome satisfies E|q|² = ⟨R_AᵀR_A⟩ + ⟨R_RᵀR_R⟩ ≤ 2E + m(1 + c).
- (F5) Trace distance of Gaussian states [3, Theorem 3]. For Gaussian states with covariance matrices V, W and equal first moments, ½‖ρ(V) − ρ(W)‖_1 ≤ (1 + √3)/8 · tr(|V − W| Ωᵀ (V + W)/2 Ω) ≤ (1 + √3)/8 · max(‖V‖, ‖W‖) ‖V − W‖_1.

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

## Check

`sim/` contains scripts with asserts:

- `teleport.py`: for random channels on m = 1, 2, 3 modes, random Gaussian inputs and squeezing r, the teleportation protocol of Lemma 3 with correction D_{Xq} reproduces the first and second moments of Φ′ ∘ N_ξ with ξ = 2e^{−2r} (homodyne conditioning of the joint Gaussian state), E|q|² = ⟨R_AᵀR_A⟩ + m cosh 2r, and the bounds on ‖V_i‖ and ‖V_1 − V_2‖_1.
- `fock_check.py`: in a truncated photon-number basis, (F5) on 40 random pairs of one-mode Gaussian states (largest ratio of the two sides 0.64), and Theorem 1(b) for pure-loss channels with transmissivities η and η + Δη, on a two-mode squeezed input with E = 0.5 and 2 (for Δη = 10⁻⁶ the bound is below 1).
- `learn.py`: 300 runs each of the learner on random one- and two-mode channels, with and without a noise margin. The error bounds b_d, b_X, b_Σ hold in all runs, and the repaired Ŷ always gives a valid channel with the required noise margin.
- `queries.py`: the simplified forms of Theorem 1 dominate the explicit form of Lemma 3 on 20000 random parameter sets, and the query numbers of Theorem 2 for example parameters.
- `bounds.py`: the bounds as functions.

Output in `sim/out.txt`.

## Scope

- Written proof with numerical checks. Facts (F4) and (F5) and the concentration bounds for Gaussian vectors and matrices are taken from [3], [4], [5], [6].
- The constants are large and the exponent 10 of 1/ε in the general case is not shown to be tight. For Gaussian unitaries, [1] gives 1/ε⁴.
- The noise margin ξ enters Theorem 2 as known prior information.

## References

[1] M. Fanizza, V. Iyer, J. Lee, A. A. Mele, F. A. Mele. Efficient learning of bosonic Gaussian unitaries. arXiv:2510.05531 (v2).

[2] F. A. Mele. Advances in quantum learning theory with bosonic systems. Il Nuovo Cimento C 49, 137 (2026). arXiv:2605.08082.

[3] L. Bittel, F. A. Mele, A. A. Mele, S. Tirone, L. Lami. Optimal estimates of trace distance between bosonic Gaussian states and applications to learning. Quantum 9, 1769 (2025). arXiv:2411.02368.

[4] S. L. Braunstein, H. J. Kimble. Teleportation of continuous quantum variables. Physical Review Letters 80, 869 (1998).

[5] M. M. Wilde. Strong and uniform convergence in the teleportation simulation of bosonic Gaussian channels. Physical Review A 97, 062305 (2018). arXiv:1712.00145.

[6] M. J. Wainwright. High-Dimensional Statistics: A Non-Asymptotic Viewpoint. Cambridge University Press (2019).

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
