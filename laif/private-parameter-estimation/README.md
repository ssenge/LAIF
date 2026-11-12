# Dimension-free bounds for parameter estimation under quantum local differential privacy

2026-11-12

## Problem

A family of states ρ_λ on ℂ^d depends on a scalar parameter λ, with derivative D = ∂_λ ρ_λ. A channel E is ε-locally differentially private (ε-QLDP) if Tr[M E(ρ)] ≤ e^ε Tr[M E(σ)] for all 0 ≤ M ≤ I and all states ρ, σ [1, Definition 1]. Copies are privatized by E, and λ is estimated from E(ρ_λ)^{⊗N}. With F the quantum Fisher information (symmetric logarithmic derivative), the quantity that controls the error is the private Fisher information

F_ε(λ) = sup_{E ε-QLDP} F(E(ρ_λ)),

where, as in [1, Definition 2], the channel may be chosen for the point λ. Channels map into states on ℂ^d; a channel with a two-dimensional output embeds into span{|0⟩, |1⟩} ⊂ ℂ^d for d ≥ 2 without changing privacy or Fisher information. For an unbiased estimator with error variance α, N ≥ 1/(α F_ε(λ)), and [1] uses the matching achievability of the quantum information bound for scalar parameters.

Previous best bounds [1]: for qubits, Θ(1/(α ε²)) copies for ε < 1 [1, Theorem 1 and Corollary 1], under the assumption ⟨∂_λ ω_λ, ω_λ⟩ ≠ 0 on the coordinate vector ω_λ of ρ_λ, which excludes families of pure states; for qubits and ε < 1/2, a bound of the same order for pure families over channels with c = 0 in the coordinate form of [1] [1, Theorem 2]; for qudits, O(d/(α ε²)) copies from the global depolarizing channel [1, Proposition 1], where "the linear dependence to the dimension is not known to be tight" [1]. For ε ≫ 1 the lower bound of [1] tends to 0 [1, Remark 3]. For every ε-QLDP channel, the χ² contraction bound of [3, Lemma 4.7 and Equation (4.19)] implies F(E(ρ_λ)) ≤ e^{−ε}(e^ε − 1)² ‖D‖_1²/2, in the limit of nearby parameters and since the symmetric logarithmic derivative information is at most the χ² information; for classical data, Fisher information under local privacy is bounded in terms of an L1 quantity of the score in [4].

## Results

**Theorem 1.** For every dimension d, every family and every ε > 0,

(e^ε − 1)²/(e^ε + 1)² · ‖D‖_1² ≤ F_ε(λ) ≤ min{ F(ρ_λ), (e^ε − 1)²/(2(e^ε + 1)) · ‖D‖_1² }.

The lower bound is attained by a channel that measures the projector onto the positive part of D and passes the outcome through binary randomized response; the same channel attains the private contraction coefficient of the trace distance in [5]. The upper bound improves the bound implied by [3] by the factor 1 + e^{−ε}, and its constant is attained as ε → ∞ up to a factor 1 + O(e^{−ε}) (Remark below). When the second term is the minimum, the two bounds differ by the factor (e^ε + 1)/2, which tends to 1 as ε → 0 and is at most 1.86 for ε ≤ 1.

**Corollary 2.** In the sense of [1, Definition 2], with the estimation step of [1],

max{ 1/(α F(ρ_λ)), 2(e^ε + 1)/((e^ε − 1)² α ‖D‖_1²) } ≤ inf_E N_α(E) ≤ (e^ε + 1)²/((e^ε − 1)² α ‖D‖_1²).

For ε ≤ 1 this is Θ(1/(α ε² ‖D‖_1²)), with no dependence on d. Since D is traceless, ‖D‖_1² ≥ 2‖D‖_2² = ‖∂_λ ω_λ‖² in the coordinates of [1] (generators with Tr[η_i η_j] = 2δ_ij). So the upper bound is at most (e^ε + 1)²/((e^ε − 1)² α ‖∂_λ ω_λ‖²): the qubit bound of [1, Theorem 1] holds in every dimension, which removes the factor d of [1, Proposition 1]. For d = 2 the two bounds coincide.

**Corollary 3 (pure families).** If ρ_λ = |ψ_λ⟩⟨ψ_λ|, then ‖D‖_1² = F(ρ_λ), so

tanh²(ε/2) · F(ρ_λ) ≤ F_ε(λ) ≤ min{1, (e^ε − 1)²/(2(e^ε + 1))} · F(ρ_λ).

For every ε > 0 the two sides differ by at most a factor 2.62, and the ratio tends to 1 both as ε → 0 and as ε → ∞. So for pure families the private Fisher information is ε²F(ρ_λ)/4 up to a factor 1 + O(ε) for small ε and F(ρ_λ) up to a factor 1 + O(e^{−ε}) for large ε, with no condition on the family. At small ε the depolarizing channel of [1, Proposition 1] gives about 2/d of the private Fisher information of the two-outcome channel on such families (`sim/check.py`). The bound 1/(α F(ρ_λ)) of Corollary 2 for large ε is data processing; Corollary 3 shows that for pure families it is attained up to a factor 1 + O(e^{−ε}).

**Remark (sharpness of the upper constant).** For ρ_λ = diag(s + λ, s − λ, 1 − 2s) at λ = 0 (so t = 1), measure in the standard basis and output y ∈ {0, 1, 2} with K(·|0) = (e^ε u, u, w), K(·|1) = (u, e^ε u, w), K(·|2) = (u, u, e^ε w), where u = (1 − e^{−ε})/(e^ε + 1 − 2e^{−ε}) and w = e^{−ε}(1 − 2u). This kernel is ε-private, and as s → 0 the Fisher information tends to 2(e^ε − 1)² u, which is a fraction (1 − e^{−ε})(e^ε + 1)/(e^ε + 1 − 2e^{−ε}) of the upper bound: 0.955 at ε = 3 and 1 − O(e^{−ε}) in general. On this family the two-outcome channel is far below it for large ε, so for mixed families at large ε the open gap lies in the lower bound.

## Proofs

Let t = ‖D‖_1/2 and write D = P − Q with P, Q ⪰ 0 of orthogonal supports; since Tr D = 0, Tr P = Tr Q = t. Assume t > 0.

*Upper bound.* The quantum Fisher information of E(ρ_λ) is the largest classical Fisher information of a measurement on it [2]. Fix a measurement {M_x}, and let p_x = Tr[M_x E(ρ_λ)], a_x = Tr[M_x E(P/t)] and b_x = Tr[M_x E(Q/t)]. Then ∂_λ p_x = t(a_x − b_x), and since P/t, Q/t and ρ_λ are states, the privacy condition gives a_x ≤ e^ε b_x, b_x ≤ e^ε a_x, a_x ≤ e^ε p_x and b_x ≤ e^ε p_x. Let m_x = max(a_x, b_x). Then |a_x − b_x| ≤ (1 − e^{−ε}) m_x and m_x ≤ e^ε p_x, so

(∂_λ p_x)²/p_x ≤ t² (1 − e^{−ε})² e^ε m_x.

Outcomes with p_x = 0 have a_x = b_x = 0. Summing, the Fisher information is at most t² (e^ε − 1)² e^{−ε} Σ_x m_x, and Σ_x m_x = 1 + d_TV(a, b). For two distributions whose ratios lie in [e^{−ε}, e^ε], let S = {a > b}, A = a(S) and B = b(S). Then A ≤ e^ε B and 1 − B ≤ e^ε (1 − A), so d_TV(a, b) = A − B ≤ (e^ε − 1)/(e^ε + 1). Hence the Fisher information is at most t² (e^ε − 1)² e^{−ε} · 2e^ε/(e^ε + 1) = 2(e^ε − 1)² t²/(e^ε + 1), which is the second term with t² = ‖D‖_1²/4. The first term is data processing for the quantum Fisher information. ∎

Privacy forces all outputs E(ρ) to have the same support (if Tr[M E(σ)] = 0 then Tr[M E(ρ)] = 0), so the rank of E(ρ_λ) does not change with λ and the measurement formula for the quantum Fisher information applies.

*Lower bound.* Let Π be the projector onto the support of P, q = 2/(e^ε + 1), and E(ρ) = (1 − r(ρ))|0⟩⟨0| + r(ρ)|1⟩⟨1| with r(ρ) = q/2 + (1 − q) Tr[Πρ]. Both r and 1 − r lie in [1/(e^ε + 1), e^ε/(e^ε + 1)], so for 0 ⪯ M ⪯ I, Tr[M E(ρ)] = M_00 (1 − r(ρ)) + M_11 r(ρ) ≤ e^ε Tr[M E(σ)]; E is ε-QLDP. The output is diagonal, so its quantum Fisher information is the classical one, ((1 − q) Tr[ΠD])²/(r(1 − r)) ≥ 4(1 − q)² t², with Tr[ΠD] = t and 1 − q = (e^ε − 1)/(e^ε + 1). ∎

*Corollaries.* Corollary 2 is Theorem 1 with N ≥ 1/(α F) and the achievability step of [1]. For a pure family, D = |∂ψ⟩⟨ψ| + |ψ⟩⟨∂ψ| with ⟨ψ|∂ψ⟩ + ⟨∂ψ|ψ⟩ = 0 has rank at most 2, trace 0 and ‖D‖_2² = 2(⟨∂ψ|∂ψ⟩ − |⟨ψ|∂ψ⟩|²) = F/2, so its eigenvalues are ±√F/2 and ‖D‖_1² = F. The ratio of the bounds in Corollary 3 is min{coth²(ε/2), (e^ε + 1)/2}, which is largest where (e^ε − 1)² = 2(e^ε + 1), that is e^ε = 2 + √5, with value ((3 + √5)/(1 + √5))² = (1 + √5)²/4 < 2.62. ∎

## Check

`sim/check.py` asserts, for random full-rank families in dimensions 2 to 8 and ε ∈ {0.05, 0.3, 1, 2.5}: ‖D‖_1² ≤ F(ρ_λ); that the two-outcome channel reaches the lower bound and stays below the upper bound; and that 4741 random measure-and-prepare ε-QLDP channels (random POVMs, random privacy kernels, random output states) stay below the upper bound (largest ratio 0.11). It also asserts ‖D‖_1² = F for pure families up to d = 16, that the two-outcome channel beats the depolarizing channel by a factor of at least d/4 at ε = 0.05 (observed d/2), and that a random search over triples of ε-close distributions stays below the upper bound of the proof (it reaches 95% of it at ε = 3), and that the kernel of the Remark reaches 0.955 and 0.9975 of the upper bound at ε = 3 and 6. Output in `sim/out.txt`.

## Scope

- Written proofs with numerical checks.
- The channel may depend on the point λ, as in [1]; the estimation step that attains N ≈ 1/(α F) is the one used in [1]. A channel built from an estimate λ′ keeps Tr[Π_{λ′} D_λ] ≥ t − ‖D_λ − D_{λ′}‖_1, so a first stage of estimation can fix Π without changing the privacy of each copy.
- The upper bound of Theorem 1 is implied by [3] up to the factor 1 + e^{−ε}; the new parts are the matching lower bound in every dimension, the constant, and Corollary 3.
- For mixed families and large ε, the gap between ‖D‖_1² and F(ρ_λ) remains and can depend on d.
- Only pure ε-QLDP (δ = 0) is treated.

## References

[1] F. Farokhi. Sample complexity bounds for scalar parameter estimation under quantum differential privacy. IEEE Control Systems Letters (2025). arXiv:2501.14184.

[2] S. L. Braunstein, C. M. Caves. Statistical distance and the geometry of quantum states. Physical Review Letters 72, 3439 (1994).

[3] H.-C. Cheng, C. Hirche, C. Rouzé. Sample complexity of locally differentially private quantum hypothesis testing. arXiv:2406.18658.

[4] L. P. Barnes, W.-N. Chen, A. Özgür. Fisher information under local differential privacy. arXiv:2005.10783.

[5] T. Nuradha, M. M. Wilde. Contraction of private quantum channels and private quantum hypothesis testing. arXiv:2406.18651.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
