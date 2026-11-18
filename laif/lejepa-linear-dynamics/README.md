# Gradient dynamics of linear LeJEPA: variance first, predictability last

Written 18 Nov 2026.

LeJEPA [1] trains an encoder with an invariance term between two views and the regularizer SIGReg, with no predictor, no stop-gradient and no teacher network. For a linear encoder the global minimizers are known: they order the learned spectrum by the whitened invariance cost of each feature, and their rank is bounded ([`sigreg-dimension-stiffness`](../sigreg-dimension-stiffness/), Theorems 2 and 3 and Proposition 4). The results below describe how gradient descent gets there. In the early phase, while the embedding is small, a feature grows at a rate proportional to its variance times its margin below a threshold. At the minimizers only the invariance cost counts. So a noisy feature with large variance can be learned first and dropped later, while a predictable feature with small variance is learned last and kept. For comparison, in deep linear self-distillation with stop-gradient the order of learning itself favours features with a high regression coefficient between the views [2]; in linear LeJEPA this preference appears only at the minimizers, while the early rate is weighted by the variance.

**Setting.** Two jointly Gaussian views x, x' ∈ ℝ^d with zero mean and equal marginals, Cov x = Σ ≻ 0, symmetric cross-covariance C = E x x'ᵀ (for example exchangeable views), and Δ = E(x − x')(x − x')ᵀ = 2(Σ − C). A linear encoder W ∈ ℝ^{K×d} gives the embedding covariance M = WΣWᵀ and the population loss

    L(W) = tr(WΔWᵀ) + μ S_h(M),   S_h(M) = E_a h(aᵀMa),

the population value of LeJEPA's loss for Gaussian embeddings, with a uniform on the unit sphere of ℝ^K and h the slice function of SIGReg, D(s) = √(2π)[(2s+1)^{−1/2} − 2(s+2)^{−1/2} + 3^{−1/2}], with D'(0) = √(2π)(2^{−3/2} − 1) ≈ −1.620. Its gradient is ∇L = 2WΔ + 2μ G(M) W Σ with G(M) = E h'(aᵀMa) aaᵀ, and we follow the gradient flow Ẇ = −∇L(W). We assume h'(0) ≤ 0, as for D, and set the threshold κ = −μh'(0)/K = μ|h'(0)|/K.

In the **commuting case** Σ, Δ (equivalently Σ, C) share an eigenbasis e₁, …, e_d with Σeᵢ = σᵢeᵢ and Δeᵢ = δᵢeᵢ. Feature i has the invariance cost cᵢ = δᵢ/σᵢ = 2(1 − ρᵢ), where ρᵢ = (eᵢᵀCeᵢ)/σᵢ is the regression coefficient of feature i of one view on the other, and the learned variance nᵢ(t) = σᵢ‖W(t)eᵢ‖². The initialization W(0) is arbitrary; in particular its rows need not be aligned with the eᵢ.

## Results

**Lemma 1 (feature equation).** In the commuting case, vᵢ = Weᵢ satisfies v̇ᵢ = −2δᵢvᵢ − 2μσᵢGvᵢ, so

    ṅᵢ = −4δᵢnᵢ − 4μσᵢ² vᵢᵀ G vᵢ.

The gradient formula behind it holds for every finite direction law on the unit sphere in place of the uniform law, in particular for a fixed finite set of weighted slice directions.

**Lemma 2 (the gradient matrix).** Let M ⪰ 0 and v ∈ ℝ^K.
(a) If h'(x) ≥ h'(0) for x ≥ 0, then vᵀGv ≥ h'(0)‖v‖²/K.
(b) If h'(x) ≤ h'(0) + L₂x for x ≥ 0, then vᵀGv ≤ h'(0)‖v‖²/K + 3L₂ tr M ‖v‖²/(K(K+2)).
The slice function D satisfies (a), since D'(s) − D'(0) = √(2π)[(1 − (2s+1)^{−3/2}) − (2^{−3/2} − (s+2)^{−3/2})] and (s+2)^{−3/2} ≥ 2^{−3/2}(2s+1)^{−3/2}, and (b) with L₂ = sup_{s ≥ 0} D''(s) = D''(0) ≈ 6.855.

**Theorem 1 (features above the threshold are never learned).** In the commuting case, with h satisfying (a), for every feature i and every t ≥ 0,

    nᵢ(t) ≤ nᵢ(0) exp(4σᵢ(κ − cᵢ) t).

Features with cᵢ ≥ κ never grow, and features with cᵢ > κ decay exponentially, from every initialization.

**Theorem 2 (early phase).** In the commuting case, with h satisfying (a) and (b), on every interval [0, T] on which tr M(t) ≤ ε,

    nᵢ(0) exp(4σᵢ(κ − cᵢ − η) t) ≤ nᵢ(t) ≤ nᵢ(0) exp(4σᵢ(κ − cᵢ) t),   η = 3μL₂ε/(K(K+2)).

While the embedding is small, feature i therefore grows at the rate 4σᵢ(κ − cᵢ) = 4σᵢ(κ − 2 + 2ρᵢ) up to the relative error η/(κ − cᵢ), and reaches a given size after a time of about log(ε/nᵢ(0))/(4σᵢ(κ − cᵢ)). Since η/(κ − cᵢ) = 3L₂εκ/((K+2)|h'(0)|(κ − cᵢ)), this description holds while tr M is small against K(κ − cᵢ)/κ; features close to the threshold are not covered.

**Corollary 3 (variance first, predictability last).** Let s and n be two features with 0 < c_s < c_n < κ, and let ε be small enough that σ_n(κ − c_n − η) > σ_s(κ − c_s): a noisy feature n with large variance and a predictable feature s with small variance. By Theorem 2, on every interval [0, T] on which tr M ≤ ε,

    (n_n(t)/n_n(0)) / (n_s(t)/n_s(0)) ≥ exp(4[σ_n(κ − c_n − η) − σ_s(κ − c_s)] t),

so the noisy feature grows faster in the early phase. At every global minimizer λ* of the reduced objective F(λ) = Σ cᵢλᵢ + μS_h(λ) the spectrum is ordered by the costs ([`sigreg-dimension-stiffness`](../sigreg-dimension-stiffness/), Theorem 2 (i)), so λ*_s ≥ λ*_n, and with more than K features below the threshold λ*_n may be 0. In `sim/dynamics_check.py` (d = 6, K = 3, κ = 1) the feature with σ = 9 and ρ = 0.6 rises first to a peak of 0.092 and then falls to 0, outside the range of Theorem 2, while the feature with σ = 0.5 and ρ = 0.97 is learned last and ends with the largest variance, 0.97.

**Proposition 4 (general Σ and Δ, early phase).** Without the commuting assumption, Ẇ = 2W(κΣ − Δ) − 2μRWΣ with R = G − h'(0)I/K, and 0 ⪯ R ⪯ 3L₂ tr M/(K(K+2)) I by Lemma 2 (a) and (b). So while tr M is small the flow is a small perturbation of the linear flow Ẇ = 2W(κΣ − Δ), whose solution W(0)exp(2(κΣ − Δ)t) turns the row space of W towards the top eigenvectors of κΣ − Δ. The global minimizers instead have rows spanned by the generalized eigenvectors u with Δu = γΣu for the smallest γ, as many as their rank. In `sim/dynamics_check.py` (d = 8, K = 2, random Σ and Δ) the row space has overlap 0.955 with the top eigenvectors of κΣ − Δ when tr M first exceeds 10⁻³, and overlap 1.000 with the generalized eigenvectors at the end.

**Normalization.** With two views, the invariance term averaged over the K coordinates as in the code of [1], and weight λ for the regularizer, the loss is (1 − λ) tr(WΔWᵀ)/(4K) + λ S_h, so μ = 4Kλ/(1 − λ) and κ = 4λ|h'(0)|/(1 − λ) does not depend on K. With the invariance term summed, κ falls like 1/K and fewer features lie below the threshold, in line with the rank bound of the minimizers. The statistic of [1] is multiplied by the batch size N; its expected value has the slice function N D + B_N with the null bias B_N(s) = √(2π)(1 − (2s+1)^{−1/2}) (Lemma 2 in [`sigreg-dimension-stiffness`](../sigreg-dimension-stiffness/)), with h'(0) = −(N|D'(0)| − √(2π)), and it satisfies (a) for N ≥ 2. Then κ grows like N: at λ = 0.05 and N = 256, κ ≈ 87, so every feature lies below the threshold (cᵢ ≤ 4), Theorem 1 is void, and the early rates 4σᵢ(κ − cᵢ) are nearly proportional to the variances σᵢ.

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Lemma 1 | Commuting case; any finite direction law on the unit sphere; h differentiable on [0, ∞) with h and h' bounded there and h' measurable; Σ = SᵀS for some S | Lean: the directional derivatives of L are given by the gradient formula, and every gradient flow satisfies the feature equation | 2026-11-18 |
| Lemma 2 | M = BBᵀ, h' measurable and bounded on [0, ∞) | Lean, assuming the second and fourth moments of the uniform law on the sphere; (a) and (b) for D in Lean with L₂ = 8 (the sharp 6.855 by script) | 2026-11-18 |
| Theorems 1 and 2 | Every gradient flow of L defined for all times | Lean, also for h = D | 2026-11-18 |
| Corollary 3 | Global minimizers λ* of the reduced objective F; the identification of λ* with the learned variances of a minimizer W (the equality case of the trace inequality) and the convergence of the flow to a global minimizer are not proved | Claim, from Theorem 2 and the ordering theorem; the non-monotone trajectory is numerical | 2026-11-18 |
| Proposition 4 | General Σ, Δ, early phase; the closeness to the linear flow is not quantified | Claim; checked numerically | 2026-11-18 |
| Normalization remarks | As stated | Claim | 2026-11-18 |

## Formal verification

[`lean/`](lean/) is a Lean 4 project with the library `LejepaDyn` and the four modules of `SigregDim` it uses (from [`sigreg-dimension-stiffness`](../sigreg-dimension-stiffness/), unchanged), with no `sorry` and only the standard axioms (propext, Classical.choice, Quot.sound), as listed by [`lean/LejepaDyn/Axioms.lean`](lean/LejepaDyn/Axioms.lean) with its output in [`lean/axioms.txt`](lean/axioms.txt). It uses Lean v4.36.0-rc1 and Mathlib at revision d875a8de5222f62cf1c2fafc7984588adadc990a. Build with `lake exe cache get` and then `lake build` in `lean/`. The data covariance is written as Σ = SᵀS and the embedding covariance as M = WΣWᵀ = Σᵣ bᵣbᵣᵀ with bᵣ = Wsᵣ for the rows sᵣ of S, so that aᵀMa = Σᵣ(bᵣᵀa)² and tr M = Σᵣ‖bᵣ‖². Matrices are functions on index pairs, and a gradient flow is a path W(t) whose velocity Ẇ satisfies d/ds L(W(t) + sH) = −⟨Ẇ(t), H⟩ at s = 0 for every direction H, in the Frobenius inner product.

- `LejepaDyn/Moments.lean`: the hypothesis `Iso4` on the direction law (probability measure on the unit sphere with E(uᵀa)² = ‖u‖²/K and E(uᵀa)²(vᵀa)² = (‖u‖²‖v‖² + 2(uᵀv)²)/(K(K+2))), the inner-product inequality and integrability.
- `LejepaDyn/Gram.lean`, Lemma 2: `gq_ge` and `gq_le`, with `integral_qf_mul` for E(aᵀMa)(vᵀa)².
- `LejepaDyn/Growth.lean`: `growth_le` and `growth_ge`, the exponential comparison for ṅ ≤ Rn and ṅ ≥ Rn on [0, T].
- `LejepaDyn/Features.lean`, Theorems 1 and 2 from the feature equation: `never_learned` and `early_phase` for every h with (a) and (b), `epD'_ge` and `epD'_le_lin` for D, and `never_learned_D` and `early_phase_D`.
- `LejepaDyn/Flow.lean`, Lemma 1 and Theorems 1 and 2 for the gradient flow: `hasDerivAt_reg` (differentiation under the integral, by dominated convergence), `hasDerivAt_loss` (the gradient formula), `flow_eq` (a gradient flow follows Ẇ = −∇L), `grad_col` and `feature_ode` (the feature equation), and `never_learned_flow`, `early_phase_flow`, `never_learned_flow_D`, `early_phase_flow_D`.

**Assuming.** The second and fourth moments of the uniform law on the sphere (hypothesis `Iso4`), classical; Lean does not construct a law that satisfies it.

**Not formalized.** The existence of the gradient flow for all times (for h = D the vector field is locally Lipschitz with linear growth in W, so it exists by the classical existence theorem for ordinary differential equations), Corollary 3, Proposition 4, the normalization remarks, and the convergence of the flow.

## Simulations

[`sim/`](sim/) holds Python scripts with asserts (NumPy, SciPy):

- `dynamics_check.py`: gradient descent on the loss with 20000 sampled directions, whitened so that their second moment is exactly I/K. In the commuting case it checks Theorem 1 along the whole trajectory, Theorem 2 while tr M ≤ 0.05 (with 1 % slack for the fourth moments of the sampled directions and the time step), the faster relative growth nᵢ(t)/nᵢ(0) of the noisy feature, and the ordering of the final spectrum by the costs. In a non-commuting case it checks the two subspace overlaps of Proposition 4.
- `slice_function.py`: the closed forms of D, D', D'' and the constants used above.

## References

1. R. Balestriero, Y. LeCun. LeJEPA: provable and scalable self-supervised learning without the heuristics. arXiv:2511.08544, 2025.
2. E. Littwin, O. Saremi, M. Advani, V. Thilak, P. Nakkiran, C. Huang, J. Susskind. How JEPA avoids noisy features: the implicit bias of deep linear self distillation networks. arXiv:2407.03475, 2024.
3. A. M. Saxe, J. L. McClelland, S. Ganguli. Exact solutions to the nonlinear dynamics of learning in deep linear neural networks. arXiv:1312.6120, 2013.
4. M. S. Halvagal, A. Laborieux, F. Zenke. Implicit variance regularization in non-contrastive SSL. arXiv:2212.04858, 2022.

Decoupled learning rates per eigenmode of linear networks go back to [3], and for non-contrastive objectives with a predictor the eigenvalues act as learning-rate multipliers [4].

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
