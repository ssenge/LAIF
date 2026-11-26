# The leading constant of sample-based Hamiltonian simulation

2026-11-26

In sample-based Hamiltonian simulation a protocol receives n copies of an unknown state σ on C^d and must apply e^{−itσ} to a system, up to error ε in the normalized diamond distance. Density matrix exponentiation (DME) [3] does this with one copy per step: each step applies e^{−iΔ SWAP} to the system and a fresh copy and discards the copy, with Δ = t/n. The number of copies is of order t²/ε, and this order is optimal [2]. With explicit constants, DME needs at most 4t²/ε copies and every protocol needs at least 0.032 t²/ε copies, for ε < min{9t/(100π), 1/10} [1, Corollary 3 and Theorem 5]. Here the leading constant is pinned down: it is 1, for every d, and DME attains it.

| Quantity | Previous bound | Here |
|---|---|---|
| Copies sufficient for every σ (DME) | at most 4t²/ε [1, Corollary 3] | at most t²/ε + 3t, for every ε and t (Theorem 1) |
| Copies needed by every protocol, any joint processing of the n copies | at least 0.032 t²/ε for ε < min{9t/(100π), 1/10} [1, Theorem 5] | at least (1 − Kt) t²/ε for every ε and every t ≤ c, with absolute constants c and K (Theorem 2) |
| Leading constant of the copy count, t ≤ c, every d ≥ 2 | between 0.032 and 4 | exactly 1 |

## Setting

S = C^d is the system and P = C^d holds one copy of σ. A protocol with n copies is any channel Λ from S ⊗ P^{⊗n} to S. Its error is ε(Λ) = sup_σ ½‖Λ(· ⊗ σ^{⊗n}) − 𝒰_σ‖⋄, where 𝒰_σ(ρ) = e^{−itσ} ρ e^{itσ}, and ad_σ(ρ) = −i[σ, ρ]. One DME step is Λ_Δ(ρ) = cos²Δ ρ + sin²Δ σ − i sinΔ cosΔ [σ, ρ].

## Results

**Theorem 1 (DME, leading constant 1).** For every d ≥ 2, every state σ, every t > 0 and n ≥ 2t, n DME steps of time Δ = t/n have error at most t²/n + 2.65 t³/n². Hence n = ⌈t²/ε + 3t⌉ copies give error at most ε.

*Proof.*
1. **Expansion.** Λ_Δ = id + ½ sin 2Δ · ad_σ + sin²Δ · (σ tr(·) − id), and e^{Δ ad_σ} = id + Δ ad_σ + (Δ²/2) ad_σ² + R with ‖R‖⋄ ≤ (2Δ)³ e^{2Δ}/6, since ‖ad_σ‖⋄ ≤ 2. So Λ_Δ − e^{Δ ad_σ} = Δ² Φ + (sin²Δ − Δ²)(σ tr(·) − id) + (½ sin 2Δ − Δ) ad_σ − R, with Φ(ρ) = σ tr(ρ) − ρ + ½{σ², ρ} − σρσ.
2. **Leading term.** Φ = P − N with P(ρ) = σ tr(ρ) − σρσ + ¼ σ²ρσ² and N(ρ) = (I − σ²/2) ρ (I − σ²/2). The map σ tr(·) − σ · σ is completely positive, since its Choi matrix I ⊗ σ dominates the rank-one Choi matrix of σ · σ (in the eigenbasis of σ the ratio is Σ_i λ_i²/λ_i = 1). So P and N are completely positive. Since Φ annihilates the trace, P*(I) = N*(I) = (I − σ²/2)² ≤ I, and ½‖Φ‖⋄ ≤ ‖P*(I)‖ ≤ 1.
3. **Remainder.** For Δ ≤ 1/2, |sin²Δ − Δ²| ≤ Δ⁴/3, |½ sin 2Δ − Δ| ≤ 2Δ³/3 and ‖σ tr(·) − id‖⋄ ≤ 2, so one step has error at most Δ² + Δ³ (1/6 + 2/3 + 2e/3) ≤ Δ² + 2.65 Δ³. The errors of the n steps add. With n = A + 3t and A = t²/ε, the first term is εA/n and the second is at most 3tε/n, because 2.65 t² ≤ 3εn. ∎

At a pure σ and an input orthogonal to σ the leading term is attained: the target fixes the input, while each step moves the population sin²Δ towards σ. So the constant 1 of Theorem 1 is the worst case of DME.

**Theorem 2 (every protocol needs t²/ε copies).** There are absolute constants c and K such that for every d ≥ 2, every n ≥ 1, every t ∈ (0, c] and every channel Λ from S ⊗ P^{⊗n} to S, with any joint processing of the n copies,

n · sup_σ ½‖Λ(· ⊗ σ^{⊗n}) − 𝒰_σ‖⋄ ≥ t² (1 − Kt).

The supremum may be restricted to the pure states σ_v = |v⟩⟨v| with v = cos θ |0⟩ + e^{iφ} sin θ |1⟩. Hence every protocol with error ε uses at least (1 − Kt) t²/ε copies, at every accuracy ε.

*Proof sketch.* The argument follows the forced-leak bound for one jump operator of [this repository, `laif/wml-sample-constants`, Theorem 6]. Let ε be the supremum and τ = n^{−1/2} Σ_j |0 … 1 … 0⟩ (|1⟩ in copy j).
1. **Choi matrix.** Let G = (1/n) Σ_j (−i[X_j, ·]), where X_j is the j-th copy of the program, and B = Λ − Tr_P − tG. The Choi matrix of Λ is C₀ + tC₁ + C_B ≥ 0, with C₀ and C₁ the Choi matrices of Tr_P and G.
2. **Test vectors.** Take e = |1⟩|0⟩^{⊗n}|0⟩ (input |1⟩ with program |0…0⟩, output |0⟩) and f = −C₀⁺C₁e = −i (d√n)^{−1} Σ_m |m⟩|τ⟩|m⟩. Then e†C₀e = e†C₁e = 0, so e†Ce is the population ⟨0|Λ(|1⟩⟨1| ⊗ |0⟩⟨0|^{⊗n})|0⟩, which the target 𝒰_{|0⟩⟨0|} leaves at 0. Also f†C₀f = 1/n, e†C₁f = −1/n and f†C₁f = 0. Positivity of the 2 × 2 compression gives e†Ce ≥ |e†Cf|²/f†Cf.
3. **Bernstein's inequality.** The map (θ, φ) ↦ Λ(· ⊗ σ_v^{⊗n}) is a trigonometric polynomial of degree 2n in θ, and the Taylor polynomial of 𝒰_{σ_v} of order n + 1 in t has degree 2n + 2, with remainder at most (2t)^{n+2} e^{2t}/(n+2)!. Their difference lies within 2ε plus that remainder of zero for all θ, φ, so its first and second θ-derivatives are at most 2n + 2 and (2n + 2)² times that bound. At θ = 0 these derivatives are B applied to √n |τ⟩⟨0…0| and its adjoint, and to 2n(|τ⟩⟨τ| − |0…0⟩⟨0…0|), up to the smooth part of the target, which is O(t²). This gives |e†C_B f| ≤ O(ε) + O(t²/n) and f†C_B f ≤ O(ε + t²/n), uniformly in d and n.
4. **Conclusion.** With e†Cf = −t/n + e†C_B f and f†Cf = 1/n + f†C_B f, the population leaving |1⟩ is at least (t²/n)(1 − O(nε/t + t)). It is a lower bound on the error at σ = |0⟩⟨0|. If nε > t² there is nothing to prove; otherwise nε/t ≤ t, and nε ≥ t²(1 − Kt). ∎

No factor d appears: the forced leak runs from one state orthogonal to σ towards σ, and the normalizations of f in d cancel.

**Numerical checks.** The leading-order optimal one-copy step, computed as a semidefinite program over covariant second-order maps with a cutting plane over states σ, has constant 1.00000 at d = 2 and d = 3, the value of DME. The optimal channel with n copies over all channels, an exact semidefinite program on covariant Choi matrices at the pure σ (a single orbit of the unitary group, so the value is the worst case over pure states), gives n ε/t² = 0.9185, 0.9576, 0.9713, 0.9783 for n = 1, 2, 3, 4 at d = 2 and t = 0.05, and the same values for n = 1, 2 at d = 3.

## Scope

- Theorem 1 is a written proof (Claim). The decomposition Φ = P − N and complete positivity of P and N are checked on 400 random states for d = 2 to 5, and the n-step bound against the matrix exponential for d = 2, 3, t from 0.3 to 3 and n up to 40.
- Theorem 2 is a written proof sketch (Claim), with c and K not optimized. The test vectors and their overlaps are checked for d = 2, 3 and n = 1 to 3. Protocols with a random number of copies are not covered.
- The semidefinite programs are numerical, at a fixed small t.

## Files

- `sim/dme_check.py`: Theorem 1 (decomposition, complete positivity, n-step error) and the test vectors of Theorem 2, with asserts.
- `sim/lead_dme.py`: the leading-order optimal one-copy step.
- `sim/opt_dme.py`: the optimal channel with n copies over all channels.

## References

1. B. Go, H. Kwon, S. Park, D. Patel, M. M. Wilde, Sample-based Hamiltonian and Lindbladian simulation: Non-asymptotic analysis of sample complexity, arXiv:2412.02134.
2. S. Kimmel, C. Y.-Y. Lin, G. H. Low, M. Ozols, T. J. Yoder, Hamiltonian simulation with optimal sample complexity, npj Quantum Inf. 3, 13 (2017), arXiv:1608.00281.
3. S. Lloyd, M. Mohseni, P. Rebentrost, Quantum principal component analysis, Nat. Phys. 10, 631 (2014).

## Use of AI

The results, proofs and scripts were developed with the help of an AI system (Claude Opus 5.5), which also checked them.
