# The leading constant of sample-based Hamiltonian simulation

2026-11-26

In sample-based Hamiltonian simulation a protocol receives n copies of an unknown state σ on C^d and must apply e^{−itσ} to a system, up to error ε in the normalized diamond distance. Density matrix exponentiation (DME) [3] does this with one copy per step: each step applies e^{−iΔ SWAP} to the system and a fresh copy and discards the copy, with Δ = t/n. The number of copies is of order t²/ε, and this order is optimal [2]. With explicit constants, DME needs at most 4t²/ε copies and every protocol needs at least 0.032 t²/ε copies, for ε < min{9t/(100π), 1/10} [1, Corollary 3 and Theorem 5]. Here the leading constant is pinned down: it is 1, for every d, and DME attains it.

| Quantity | Previous bound | Here |
|---|---|---|
| Copies sufficient for every σ (DME) | at most 4t²/ε [1, Corollary 3] | at most t²/ε + 3t, for every ε and t (Theorem 1) |
| Copies needed by every protocol, any joint processing of the n copies | at least 0.032 t²/ε for ε < min{9t/(100π), 1/10} [1, Theorem 5] | at least (1 − 19t) t²/ε for every ε and every t ≤ 1/10 (Theorem 2) |
| Leading constant of the copy count as t → 0, every d ≥ 2 | between 0.032 and 4 | exactly 1 |

## Setting

S = C^d is the system and P = C^d holds one copy of σ. A protocol with n copies is any channel Λ from S ⊗ P^{⊗n} to S. Its error is ε(Λ) = sup_σ ½‖Λ(· ⊗ σ^{⊗n}) − 𝒰_σ‖⋄, where 𝒰_σ(ρ) = e^{−itσ} ρ e^{itσ}, and ad_σ(ρ) = −i[σ, ρ]. One DME step is Λ_Δ(ρ) = cos²Δ ρ + sin²Δ σ − i sinΔ cosΔ [σ, ρ].

## Results

**Theorem 1 (DME, leading constant 1).** For every d ≥ 2, every state σ, every t > 0 and n ≥ 2t, n DME steps of time Δ = t/n have error at most t²/n + 2.65 t³/n². Hence n = ⌈t²/ε + 3t⌉ copies give error at most ε.

*Proof.*
1. **Expansion.** Λ_Δ = id + ½ sin 2Δ · ad_σ + sin²Δ · (σ tr(·) − id), and e^{Δ ad_σ} = id + Δ ad_σ + (Δ²/2) ad_σ² + R with ‖R‖⋄ ≤ (2Δ)³ e^{2Δ}/6, since ‖ad_σ‖⋄ ≤ 2. So Λ_Δ − e^{Δ ad_σ} = Δ² Φ + (sin²Δ − Δ²)(σ tr(·) − id) + (½ sin 2Δ − Δ) ad_σ − R, with Φ(ρ) = σ tr(ρ) − ρ + ½{σ², ρ} − σρσ.
2. **Leading term.** Φ = P − N with P(ρ) = σ tr(ρ) − σρσ + ¼ σ²ρσ² and N(ρ) = (I − σ²/2) ρ (I − σ²/2). The map σ tr(·) − σ · σ is completely positive, since its Choi matrix I ⊗ σ dominates the rank-one Choi matrix of σ · σ (in the eigenbasis of σ the ratio is Σ_i λ_i²/λ_i = 1). So P and N are completely positive. Since Φ annihilates the trace, P*(I) = N*(I) = (I − σ²/2)² ≤ I, and ½‖Φ‖⋄ ≤ ‖P*(I)‖ ≤ 1.
3. **Remainder.** For Δ ≤ 1/2, |sin²Δ − Δ²| ≤ Δ⁴/3, |½ sin 2Δ − Δ| ≤ 2Δ³/3 and ‖σ tr(·) − id‖⋄ ≤ 2, so one step has error at most Δ² + Δ³ (1/6 + 2/3 + 2e/3) ≤ Δ² + 2.65 Δ³. The errors of the n steps add. With n = A + 3t and A = t²/ε, the first term is εA/n and the second is at most 3tε/n, because 2.65 t² ≤ 3εn. ∎

At a pure σ and an input orthogonal to σ the leading term is attained: the target fixes the input, while each step moves the population sin²Δ towards σ. So the constant 1 of Theorem 1 is the worst case of DME.

**Theorem 2 (every protocol needs t²/ε copies).** For every d ≥ 2, every n ≥ 1, every t ∈ (0, 1/10] and every channel Λ from S ⊗ P^{⊗n} to S, with any joint processing of the n copies,

n · sup_σ ½‖Λ(· ⊗ σ^{⊗n}) − 𝒰_σ‖⋄ ≥ t² (1 − 19t).

The supremum may be restricted to the pure states σ_v = |v⟩⟨v| with v = cos θ |0⟩ + e^{iφ} sin θ |1⟩. Hence every protocol that uses a fixed number n of copies and has error at most ε on these states has n ≥ (1 − 19t) t²/ε, at every accuracy ε.

*Proof.* Let ε be the supremum over the states σ_v, Λ_v(ρ) = Λ(ρ ⊗ σ_v^{⊗n}) and 𝒰_v = 𝒰_{σ_v}, so ‖Λ_v − 𝒰_v‖⋄ ≤ 2ε for all θ, φ. Let C = Σ_{a,b} |a⟩⟨b| ⊗ Λ(|a⟩⟨b|) ≥ 0 be the Choi matrix of Λ, with ⟨a|⟨x| C |b⟩|y⟩ = ⟨x|Λ(|a⟩⟨b|)|y⟩, and let |τ⟩ = n^{−1/2} Σ_j |0 … 1 … 0⟩ (|1⟩ in copy j).
1. **Test vectors.** Let e = |1⟩|0⟩^{⊗n}|0⟩ (input |1⟩, program |0…0⟩, output |0⟩) and f = c Σ_m |m⟩|τ⟩|m⟩ with c = −i/(d√n). Positivity of C gives |e†Cf|² ≤ (e†Ce)(f†Cf).
2. **The leak is at most ε.** e†Ce = ⟨0|Λ_0(|1⟩⟨1|)|0⟩ with Λ_0 = Λ_v at θ = 0, that is σ = |0⟩⟨0|. The target 𝒰_0 fixes |1⟩⟨1|, so e†Ce = tr(|0⟩⟨0| (Λ_0 − 𝒰_0)(|1⟩⟨1|)) ≤ ε, since the difference of two states has trace zero.
3. **f has weight at most 1/n.** f†Cf = |c|² Σ_{m,m′} ⟨m|Λ_τ(|m⟩⟨m′|)|m′⟩ with the channel Λ_τ(ρ) = Λ(ρ ⊗ |τ⟩⟨τ|). The sum is d² times the entanglement fidelity of Λ_τ, which is at most 1, so f†Cf ≤ 1/n. With steps 1 and 2, ε ≥ n |e†Cf|².
4. **The cross term is a θ-derivative.** Let M(ρ) = Λ(ρ ⊗ |0^n⟩⟨τ|) and Q(X) = Σ_m ⟨0|X(|1⟩⟨m|)|m⟩ for a linear map X on operators of S. Then e†Cf = c Q(M). Since |v⟩^{⊗n} = |0^n⟩ + θ e^{iφ} √n |τ⟩ + O(θ²), the coefficient of e^{−iφ} in ∂_θ Λ_v at θ = 0 is √n M. Also Q(X) = ⟨0 0|(X ⊗ id)(|1 0⟩⟨Ω|)|Ω⟩ with |Ω⟩ = Σ_m |m⟩|m⟩, so |Q(X)| ≤ d ‖X‖⋄.
5. **The target.** With a = e^{−it} − 1 and W = e^{−it|0⟩⟨0|}, the coefficient of e^{−iφ} in ∂_θ 𝒰_v at θ = 0 is Y(ρ) = a |0⟩⟨1| ρ W† + ā W ρ |0⟩⟨1|, because e^{−itσ_v} = I + aσ_v. A direct computation gives Q(Y) = a tr W† = −(d − 2)(1 − cos t) − i d sin t, so |Q(Y)| ≥ d sin t.
6. **Bernstein's inequality.** Let T_v = Σ_{k ≤ n+1} t^k ad_{σ_v}^k/k! be the Taylor polynomial of 𝒰_v = e^{t ad_{σ_v}}. The entries of σ_v^{⊗n} and of ad_{σ_v}^k are trigonometric polynomials in θ of degrees 2n and 2k, so Λ_v − T_v is a trigonometric polynomial of degree at most 2n + 2 in θ, with values in maps of diamond norm at most 2ε + R, where R = Σ_{k ≥ n+2} (2t)^k/k! (since ‖ad_σ‖⋄ ≤ 2). Bernstein's inequality, applied through bounded linear functionals, bounds its θ-derivative by (2n + 2)(2ε + R). The θ-derivative of 𝒰_v − T_v is at most R′ = Σ_{k ≥ n+2} (2t)^k/(k − 1)!, since ‖∂_θ ad_{σ_v}^k‖⋄ ≤ k 2^k at θ = 0. Taking the coefficient of e^{−iφ}, √n M = Y + E with ‖E‖⋄ ≤ 4(n + 1)ε + δ_n and δ_n = (2n + 2)R + R′.
7. **Conclusion.** By steps 4 to 6, n |e†Cf| = |Q(Y) + Q(E)|/d ≥ sin t − 4(n + 1)ε − δ_n. For t ≤ 1/10 and n ≥ 1, δ_n ≤ 12t³. Write x = nε, so 4(n + 1)ε ≤ 8x. If x ≥ t² there is nothing to prove. Otherwise sin t − 8x − δ_n ≥ t − t³/6 − 8t² − 12t³ ≥ t(1 − 9.22t) > 0, and step 3 gives x ≥ n²|e†Cf|² ≥ t²(1 − 9.22t)² ≥ t²(1 − 19t). ∎

No factor d appears: the forced leak runs from one state orthogonal to σ towards σ, and the normalizations of f in d cancel.

**Numerical checks.** The leading-order optimal one-copy step, computed as a semidefinite program over covariant second-order maps with a cutting plane over states σ, has constant 1.00000 at d = 2 and d = 3, the value of DME. The optimal channel with n copies over all channels, an exact semidefinite program on covariant Choi matrices at the pure σ (a single orbit of the unitary group, so the value is the worst case over pure states), gives n ε/t² = 0.9185, 0.9576, 0.9713, 0.9783 for n = 1, 2, 3, 4 at d = 2 and t = 0.05, and the same values for n = 1, 2 at d = 3.

## Scope

- Theorem 1 is a written proof (Claim). The decomposition Φ = P − N and complete positivity of P and N are checked on 400 random states for d = 2 to 5, and the n-step bound against the matrix exponential for d = 2, 3, t from 0.3 to 3 and n up to 40.
- Theorem 2 is a written proof (Claim) for protocols with a fixed number n of copies; protocols with a random number of copies are not covered. The constants 1/10 and 19 are not optimized. The test vectors and their overlaps are checked for d = 2, 3 and n = 1 to 3; the target coefficient Y, the value Q(Y) and the identity for Q(X) for d = 2, 3, 5; every inequality of the proof on n DME steps and on the optimal channel for d = 2, n = 1, 2 and t = 0.05; and the bound δ_n ≤ 12t³ for n < 60 on a grid of t ≤ 1/10.
- The semidefinite programs are numerical, at a fixed small t.

## Files

- `sim/dme_check.py`: Theorem 1 (decomposition, complete positivity, n-step error) and the test vectors of Theorem 2, with asserts.
- `sim/thm2_check.py`: the steps of the proof of Theorem 2 and its constants, with asserts.
- `sim/lead_dme.py`: the leading-order optimal one-copy step.
- `sim/opt_dme.py`: the optimal channel with n copies over all channels.

## References

1. B. Go, H. Kwon, S. Park, D. Patel, M. M. Wilde, Sample-based Hamiltonian and Lindbladian simulation: Non-asymptotic analysis of sample complexity, arXiv:2412.02134.
2. S. Kimmel, C. Y.-Y. Lin, G. H. Low, M. Ozols, T. J. Yoder, Hamiltonian simulation with optimal sample complexity, npj Quantum Inf. 3, 13 (2017), arXiv:1608.00281.
3. S. Lloyd, M. Mohseni, P. Rebentrost, Quantum principal component analysis, Nat. Phys. 10, 631 (2014).

## Use of AI

The results, proofs and scripts were developed with the help of an AI system (Claude Opus 5.5), which also checked them.
