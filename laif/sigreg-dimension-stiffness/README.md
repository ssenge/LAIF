# How the SIGReg regularizer of LeJEPA weighs scale against shape in dimension K

Written 17 Nov 2026.

LeJEPA [1] trains a joint-embedding predictive architecture with a regularizer, SIGReg, that pushes the embedding law towards the isotropic Gaussian. For embeddings z ∈ ℝ^K it draws random unit directions a, forms the slices aᵀz, and compares the empirical characteristic function of each slice with e^{−t²/2} by an unstandardized form of the statistic of [3] with weight e^{−t²/2}, multiplied by the batch size N. In [1] it is proved that the isotropic Gaussian is the unique zero, and in [2] the regularizer is written as a kernel discrepancy whose bandwidth grows with K. Table 1d of [1] reports that linear accuracy on ImageNet-1K falls as the projector dimension grows, from 75.3 at K = 64 to 73.65 at K = 1024.

The results below quantify how strongly SIGReg penalizes a non-isotropic covariance, as a function of K, and what this means for the minimizers of a linear model.

**Setting.** For Gaussian embeddings z ~ N(0, Σ), every slice is N(0, aᵀΣa). The population value of SIGReg is therefore S_h(Σ) = E_a h(aᵀΣa) with the slice function

    D(s) = ∫ (e^{−st²/2} − e^{−t²/2})² e^{−t²/2} dt = √(2π) [ (2s+1)^{−1/2} − 2 (s+2)^{−1/2} + 3^{−1/2} ],

the value of the statistic between N(0, s) and N(0, 1). With a uniform on the sphere and λ₁, …, λ_K the eigenvalues of Σ, the slice variance aᵀΣa has the law of X_λ = Σₖ λₖ aₖ². Write m for the mean and v for the variance of the spectrum λ. D vanishes at s = 1 together with its derivative, D''(1) = (3/2)√(2π) 3^{−5/2} ≈ 0.2412, and sup_{s ≥ 0} D''(s) = D''(0) ≈ 6.855.

## Results

**Lemma 1 (slice variance).** E X_λ = m and Var X_λ = 2v/(K+2).

**Theorem 1 (stiffness).** Let h be a slice function on [0, ∞).
(a) If h'' ≤ L on [0, ∞) (more generally, (L/2)x² − h is convex), then S_h(λ) ≤ h(m) + L v/(K+2).
(b) If h'' ≥ ℓ on [min λ, max λ], then S_h(λ) ≥ h(m) + ℓ v/(K+2).

For SIGReg this means that the scale m enters with the full weight D(m), independent of K, while the shape v enters only with weight O(1/K): near isotropy S_D ≈ D(m) + 0.2412 v/(K+2), in general the cost of the shape lies between −0.0118 v/(K+2) and 6.86 v/(K+2), and it is Θ(v/K) for spectra inside [0, 2.4], where D'' > 0. Collapsing an isotropic embedding with m = 1 onto K/2 of the K directions at the same trace (v = 1) costs at most 6.86/(K+2), and about 2.36 · 10⁻⁴ at K = 1024, while halving the variance of every coordinate costs D(1/2) ≈ 0.049 in every dimension.

**Corollary 1 (curvature at isotropy).** For smooth h and a symmetric direction Δ, the second derivative of ε ↦ S_h(I + εΔ) at ε = 0 is h''(1)((tr Δ)² + 2‖Δ‖_F²)/(K(K+2)). Per unit Frobenius norm, a traceless direction has curvature 2h''(1)/(K(K+2)) and the direction of the identity h''(1)/K, a ratio of 2/(K+2).

**Lemma 2 (minibatch statistic).** For N independent samples of N(0, s), the expected value of N times the statistic of one slice is N D(s) + B(s), with B(s) = √(2π)(1 − (2s+1)^{−1/2}). The identity holds pointwise in t, so it also holds for every quadrature in t, with D and B evaluated by that quadrature, and so does B''(1) = −2D''(1). Hence the expected minibatch loss has curvature (N − 2) D''(1) at isotropy in place of N D''(1).

**Theorem 2 (ordering and spectral gaps).** Let c₁, …, c_K > 0, μ ≥ 0, and let h be differentiable on [0, ∞) with h'(y) − h'(x) ≤ L(y − x) for 0 ≤ x ≤ y. Consider

    F(λ) = Σᵢ cᵢ λᵢ + μ S_h(λ),   λ ∈ [0, ∞)^K.

If h is continuous and bounded below on [0, ∞), F has a global minimizer λ*. At every global minimizer:
(i) if cᵢ < cⱼ, then λ*ᵢ ≥ λ*ⱼ;
(ii) if cᵢ < cⱼ and λ*ⱼ > 0, then cⱼ − cᵢ ≤ 2Lμ(λ*ᵢ − λ*ⱼ)/(K(K+2)).

For h = D with L = sup D'' = D''(0) ≈ 6.855, the constant in (ii) cannot be improved: when the costs approach μ|D'(0)|/K from below, the ratio of the two sides tends to 1 (0.994 at K = 2 in `sim/sharpness_check.py`).

**Theorem 3 (rank).** In the setting of Theorem 2, let the costs satisfy cₖ ≥ c₁ > 0 and c_l − c_k ≥ δ(l − k) for k < l, with δ > 0, and let h ≥ h_lo on [0, ∞). Every global minimizer has r = #{k : λ*ₖ > 0} active directions with

    r(r − 1) ≤ 4Lμ(Σᵢ cᵢ + μ(h(1) − h_lo)) / (c₁ δ K(K+2)).

**Corollary 3 (two normalizations).** For costs evenly spaced in a fixed range [c₁, c₁ + Δ], with h = D: if the invariance term is summed over the K coordinates and μ is fixed, then r = O(1) as K grows; if it is averaged over the coordinates, as in the code of [1] (μ = μ₀K), then r = O(√K), so the fraction of active directions is O(K^{−1/2}).

**Proposition 4 (linear LeJEPA).** Let two views x, x' ∈ ℝ^d be jointly Gaussian with zero mean and Cov(x) = Cov(x') = Σ_x ≻ 0, and let a linear encoder W ∈ ℝ^{K×d}, K ≤ d, minimize E‖W(x − x')‖² + μ S_h(WΣ_xWᵀ). Then the minimum equals min_λ F(λ) with costs c = (γ₁, …, γ_K), the smallest eigenvalues of Σ_x^{−1/2} E[(x − x')(x − x')ᵀ] Σ_x^{−1/2} in increasing order, and the rank of the embedding covariance at a minimizer is that of λ*. So Theorems 2 and 3 apply when γ₁ > 0.

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Lemma 1, Theorem 1 | Any direction law supported on the unit sphere with the second and fourth moments and the swap symmetry of the uniform law on the sphere; Gaussian embeddings. For a non-Gaussian embedding, S_h(Σ) is the value at the Gaussian with the same covariance | Lean, for the spectrum λ, for h bounded on [0, ∞) and with the quadratic models of h (implied by the bounds on h'') as hypotheses; the step from Σ to its spectrum uses the rotation invariance of the uniform law (classical) | 2026-11-17 |
| Corollary 1 | Smooth h | Claim | 2026-11-17 |
| Lemma 2 | One slice, independent samples | Claim; checked by Monte Carlo | 2026-11-17 |
| Theorem 2, existence of minimizers | As stated; global minimizers of the population objective, not the points reached by stochastic gradient descent | Lean, for h and h' bounded on [0, ∞) and the quadratic upper model of h as a hypothesis (proved for D) | 2026-11-17 |
| Theorem 3 | As stated, with μ > 0 and L > 0 in Lean (the other cases are immediate); for h = D, Lean uses the bound \|D\| ≤ 11, so h(1) − h_lo ≤ 11, while the sharp value 0 uses D ≥ 0 | Lean | 2026-11-17 |
| Corollary 3 | Asymptotic in K at fixed N and μ₀; evenly spaced costs are a modelling assumption. For the expected minibatch loss L becomes about N · 6.86, so at the batch size N = 256 of [1], μ₀ ≈ 0.21 and costs with c₁ and Δ of order 1, the bound allows full rank up to K of the order of 10³ (the bound scales with c̄/(c₁Δ)); the corollary describes the dependence on K, not the values in Table 1d of [1] | Claim, from Theorem 3; numerical minimizers consistent with both exponents | 2026-11-17 |
| Proposition 4 | Linear encoder, Gaussian views, no predictor | Claim, assuming the trace inequality tr(PC) ≥ Σ αᵢ↓γᵢ↑ for positive semidefinite P and C [4] | 2026-11-17 |

The population value averages over all directions, so it does not depend on the number of slices; Table 1d of [1] also shows a smaller loss of accuracy with 4096 slices, which these results do not model.

## Formal verification

[`lean/`](lean/) is a Lean 4 library `SigregDim` on Mathlib, with no `sorry` and only the standard axioms (propext, Classical.choice, Quot.sound), as listed by [`lean/SigregDim/Axioms.lean`](lean/SigregDim/Axioms.lean) with its output in [`lean/axioms.txt`](lean/axioms.txt). It uses Lean v4.36.0-rc1 and Mathlib at revision d875a8de5222f62cf1c2fafc7984588adadc990a. Build with `lake exe cache get` and then `lake build` in `lean/`. The direction law is a measure ν on ℝ^K with the properties `SphereLike` (probability measure, support on the unit sphere, E aₖ² = 1/K, E aₖ⁴ = 3/(K(K+2)), E aₖ²aₗ² = 1/(K(K+2)) for k ≠ l, invariance under every transposition of coordinates), and the regularizer is `sliced ν h λ = E h(Σₖ λₖ aₖ²)`.

- `SigregDim/Basic.lean`, Lemma 1: `integral_sliceVar`, `integral_sliceVar_sq`, `variance_sliceVar`.
- `SigregDim/Stiffness.lean`, Theorem 1: `sliced_le` (upper bound from the quadratic upper model of h) and `le_sliced` (lower bound from the quadratic lower model on an interval containing the spectrum), for h bounded on [0, ∞).
- `SigregDim/Collapse.lean`, Theorem 2: the objective and its global minimizers over [0, ∞)^K, the assumptions `SliceFn` on h (measurable, bounded, with the quadratic upper model and the one-sided bound h'(y) − h'(x) ≤ L(y − x)), `ordering`, `first_order_le` and `gap`.
- `SigregDim/Rank.lean`, Theorem 3: `trace_bound` and `rank_bound`, with `card_mul_pred_le_two_sum` for the counting step.
- `SigregDim/SliceD.lean`, the slice function D: its first and second derivatives, the bounds \|D\| ≤ 11, \|D'\| ≤ 3, \|D''\| ≤ 8 on [0, ∞), `descent_of_lip`, and `sliceFn_epD`, which shows that D satisfies `SliceFn` with L = 8 (the sharp constant 6.855 is checked by script).
- `SigregDim/Witness.lean`: `sphereLike_witness`, the law (2/(K(K+2))) Σₖ δ(eₖ) + (K/(K+2)) δ(𝟙/√K) satisfies `SphereLike` for every K ≥ 1, so the hypotheses are consistent.
- `SigregDim/Exists.lean`: `exists_minimizer` (h continuous and bounded below on [0, ∞), costs at least c₁ > 0), `epD'_one`, and `epD_minimizer`, which combines the above for h = D: a global minimizer exists, and every one satisfies the ordering, the gap bound with L = 8 and the rank bound.

**Assuming.** The moments and the rotation invariance of the uniform law on the sphere, which enter as the hypothesis `SphereLike` and through the reduction from Σ to its spectrum. The trace inequality [4], used on paper for Proposition 4.

**Not formalized.** The closed form of D as an integral and D ≥ 0 (Gaussian integrals), Corollary 1, Lemma 2 and the minibatch slice function N D + B, Corollary 3, Proposition 4, and the steps from the bounds on h'' to the quadratic models of h, which are hypotheses in Lean and are proved for D.

## Simulations

[`sim/`](sim/) holds Python scripts with asserts (NumPy, SciPy, PyTorch):

- `slice_function.py`: the closed forms of D, D', D'' and B against numerical integrals, the constants above, and the curvature of the two quadratures in use, t ∈ [−5, 5] with 17 points and t ∈ [0, 3] with 17 points doubled (D''(1) = 0.24121 and 0.24118).
- `stiffness_check.py`: S_D for collapse onto K/2 and K/8 directions and for halving the variance of every coordinate, against the second-order prediction, for K up to 1024.
- `batch_detect.py`: Lemma 2 by Monte Carlo, and the minibatch statistic on isotropic and collapsed Gaussian batches.
- `sharpness_check.py`: the ratio of the two sides of Theorem 2 (ii) for h = D, K = 2, as the costs approach μ|D'(0)|/K.
- `linear_rank.py`, `linear_rank_mean.py`: local minimizers of F with 6000 sampled directions, checked against Theorems 2 and 3, for both normalizations. With fixed μ the rank stays between 3 and 6 for all K tested; with μ = 2K the fraction of active directions falls from 0.31 at K = 64 to 0.10 at K = 512.

## References

1. R. Balestriero, Y. LeCun. LeJEPA: provable and scalable self-supervised learning without the heuristics. arXiv:2511.08544, 2025.
2. E. Zimmermann, H. Wiltzer, J. Szeto, D. Alvarez-Melis, L. Mackey. KerJEPA: kernel discrepancies for Euclidean self-supervised learning. arXiv:2512.19605, 2025.
3. T. W. Epps, L. B. Pulley. A test for normality based on the empirical characteristic function. Biometrika 70(3):723–726, 1983.
4. A. W. Marshall, I. Olkin, B. C. Arnold. Inequalities: Theory of Majorization and Its Applications, 2nd edition. Springer, 2011.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
