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
| Theorem 5 | Laws on the sphere of radius √K with mean 0 and identity covariance; SIGReg with the t-integral over ℝ | Lean for laws with finitely many atoms: the energy bound for every profile with a cubic remainder and for the SIGReg profile with any law of u on [0, 1]; Claim for general isotropic laws, for the identity S(P) = √(2π) E H_K(ρ) + const and for the lower bound S*_K ≤ S(P); checked by Monte Carlo | 2026-11-17 |
| Theorem 6 | As stated, t ≥ 0 | Lean for the energy form of (i) and of the upper bound in (iii), for laws with finitely many atoms; Claim for the steps through the logarithm, for (ii), from E e^{λa₁} ≤ e^{λ²/(2K)}, for general isotropic laws and for the lower bound in (iii); checked numerically | 2026-11-17 |

### Clustered embeddings on the sphere

For a law P on the sphere of radius √K write ρ = ⟨x, x'⟩/K for two independent draws x, x' ~ P. Integrating the statistic in t and using the rotation invariance of the direction law gives

    S(P) = √(2π) E H_K(ρ) − 2√π H_K(3/4) + √(2π/3),   H_K(ρ) = E exp(−K(1 − ρ)u),

with u = a₁² for a uniform direction a, so SIGReg on the sphere, with the t-integral over ℝ, is a kernel energy in ρ alone (a quadrature in t changes the profile H_K). H_K(ρ) = Σₙ βₙρⁿ with βₙ = E e^{−Ku}(Ku)ⁿ/n! ≥ 0 and Σβₙ = 1. Call P isotropic if it has mean 0 and identity covariance.

**Theorem 5 (cluster blindness).** Let P be an isotropic law on the sphere, for example one with finitely many atoms. Then E ρ = 0 and E ρ² = 1/K, whatever the number and position of the atoms, and for every profile H with |H(ρ) − (H₀ + H₁ρ + c₂ρ²)| ≤ C|ρ|³ on [−1, 1],

    |E H(ρ) − (H₀ + c₂/K)| ≤ C/K.

For the SIGReg profile C = 1 − β₀ − β₁ − β₂ < 1 (0.134 for large K), and since E ρⁿ = ‖E x^{⊗n}‖²/Kⁿ ≥ 0 and βₙ ≥ 0,

    S*_K ≤ S(P) ≤ S*_K + √(2π)(1 − β₀ − β₁ − β₂)/K,   S*_K = √(2π)(β₀ + β₂/K) − 2√π H_K(3/4) + √(2π/3).

So any two isotropic laws on the sphere, the uniform law among them, differ in SIGReg by at most √(2π)(1 − β₀ − β₁ − β₂)/K ≈ 0.34/K, however their mass is clustered. For large K, an embedding law concentrated on the 2K vertices ±√K eᵢ of the cross-polytope has S ≈ 0.125/K, and one on two random signed orthonormal bases (4K points) has S ≈ 0.063/K, while the uniform law on the sphere has S ≈ 0.117/K² (`sim/atomic_sigreg.py`). The penalty for such a clustering is thus of the same order 1/K as the cost of the shape in Theorem 1, and small against a scale error such as D(1/2) ≈ 0.049.

**Theorem 6 (uniformity term at inverse temperature t).** Let t ≥ 0 and R_t(P) = log E exp(−2t(1 − ρ)), the uniformity loss of [6] on normalized embeddings.
(i) Every law on the sphere with m atoms, with any weights, has R_t(P) ≥ −log m, for every t.
(ii) The uniform law has R_t ≤ −2t + 2t²/K, so a law with m atoms is separated from it by at least 2t − 2t²/K − log m.
(iii) Every isotropic law on the sphere has 0 ≤ R_t(P) − log(e^{−2t}(1 + 2t²/K)) ≤ (e^{2t} − 1 − 2t − 2t²)/K.

So the uniformity term is blind to isotropic clusters when e^{2t} is small against K, and it separates laws with m atoms when 2t exceeds log m + 2t²/K. At the usual t = 2 and K = 1024 the bound in (iii) is 0.041, and the bound in (ii) guarantees a positive margin only for laws with fewer than e^{4 − 8/K} ≈ 54 atoms, while an isotropic law needs at least K atoms. A regularizer S + γR_t keeps the Gaussian target of SIGReg and adds a guaranteed margin of γ(2t − 2t²/K − log m) against every law with m atoms, which is positive when log m < 2t − 2t²/K, for example for t between about log K and K/2 and m polynomial in K. The guaranteed margin from (ii) is largest at t = K/2, where it equals K/2 − log m. In [5] it is observed that smooth kernel discrepancies on the sphere favour clustered latent spaces while a density-based divergence separates instances; Theorems 5 and 6 give a quantitative form of this for the kernels above.

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
- `SigregDim/Atomic.lean`, Theorem 5: the structure `IsoAtoms` (finite law on the sphere with mean 0 and identity covariance), `energy_lin` and `energy_sq` (the moments of ρ), `energy_near` and `energy_diff` (the bound C/K and 2C/K), `remainder_le_of_series` (cubic remainder of a power series with nonnegative coefficients), and `energy_ge_inv_card` (energy at least 1/m for a profile H ≥ 0 with H(1) = 1).
- `SigregDim/Kernel.lean`, Theorems 5 and 6: `exp_remainder`, `sigKernel_remainder`, `sigreg_energy_near` and `sigreg_energy_diff` for the SIGReg profile with any probability law of u on [0, 1] and C = 1, `sigKernel_remainder_tail` and `sigreg_energy_near_tail` with C = 1 − β₀ − β₁ − β₂, `unif_energy_near` for the energy form of Theorem 6 (iii), and `unif_energy_ge` for the energy form of Theorem 6 (i).
- `SigregDim/CrossPolytope.lean`: `isoAtoms_cross`, the 2K vertices ±√K eᵢ with equal weights satisfy `IsoAtoms` for every K ≥ 1.

**Assuming.** The moments and the rotation invariance of the uniform law on the sphere, which enter as the hypothesis `SphereLike` and through the reduction from Σ to its spectrum. The trace inequality [4], used on paper for Proposition 4.

**Not formalized.** The closed form of D as an integral and D ≥ 0 (Gaussian integrals), Corollary 1, Lemma 2 and the minibatch slice function N D + B, Corollary 3, Proposition 4, the identity of Theorem 5 between SIGReg on the sphere and the kernel energy (Gaussian integrals and the rotation invariance of the direction law), Theorems 5 and 6 for isotropic laws that are not finite, the lower bounds in Theorems 5 and 6 (iii), Theorem 6 (ii), and the steps from the bounds on h'' to the quadratic models of h, which are hypotheses in Lean and are proved for D.

## Simulations

[`sim/`](sim/) holds Python scripts with asserts (NumPy, SciPy, PyTorch):

- `slice_function.py`: the closed forms of D, D', D'' and B against numerical integrals, the constants above, and the curvature of the two quadratures in use, t ∈ [−5, 5] with 17 points and t ∈ [0, 3] with 17 points doubled (D''(1) = 0.24121 and 0.24118).
- `stiffness_check.py`: S_D for collapse onto K/2 and K/8 directions and for halving the variance of every coordinate, against the second-order prediction, for K up to 1024.
- `batch_detect.py`: Lemma 2 by Monte Carlo, and the minibatch statistic on isotropic and collapsed Gaussian batches.
- `sharpness_check.py`: the ratio of the two sides of Theorem 2 (ii) for h = D, K = 2, as the costs approach μ|D'(0)|/K.
- `atomic_sigreg.py`: SIGReg on the sphere for the uniform law, the cross-polytope and two signed random bases, for K from 8 to 1024, from the kernel form, with a Monte Carlo check of the step over directions at K = 4.
- `cluster_bounds.py`: the moment identities, the bound of Theorem 5 for the SIGReg profile, Theorem 6 (i) and (iii) for t = 1, 2, 4, and the bound on E e^{λa₁}, for K up to 256, with the separation margins of Theorem 6 at K = 1024.
- `linear_rank.py`, `linear_rank_mean.py`: local minimizers of F with 6000 sampled directions, checked against Theorems 2 and 3, for both normalizations. With fixed μ the rank stays between 3 and 6 for all K tested; with μ = 2K the fraction of active directions falls from 0.31 at K = 64 to 0.10 at K = 512.

## References

1. R. Balestriero, Y. LeCun. LeJEPA: provable and scalable self-supervised learning without the heuristics. arXiv:2511.08544, 2025.
2. E. Zimmermann, H. Wiltzer, J. Szeto, D. Alvarez-Melis, L. Mackey. KerJEPA: kernel discrepancies for Euclidean self-supervised learning. arXiv:2512.19605, 2025.
3. T. W. Epps, L. B. Pulley. A test for normality based on the empirical characteristic function. Biometrika 70(3):723–726, 1983.
4. A. W. Marshall, I. Olkin, B. C. Arnold. Inequalities: Theory of Majorization and Its Applications, 2nd edition. Springer, 2011.
5. L. Nicollier, E. Meinhardt-Llopis, M. Dunitz, M. Pic, P. Musé, G. Facciolo. Expanding SPHERE-JEPA: a family of statistical regularizers for the hypersphere. arXiv:2606.17603, 2026.
6. T. Wang, P. Isola. Understanding contrastive representation learning through alignment and uniformity on the hypersphere. ICML 2020, arXiv:2005.10242.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
