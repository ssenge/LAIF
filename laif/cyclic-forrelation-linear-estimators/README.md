# Linear estimators for cyclic Forrelation

Written 25 Nov 2026.

Let f₁, …, f_k : F₂ⁿ → {−1, 1}, N = 2ⁿ, and

T_k = N⁻¹ Tr(D_{f₁} H D_{f₂} H ⋯ D_{f_k} H) = N^{−(k/2+1)} Σ_{x₁,…,x_k} f₁(x₁) ⋯ f_k(x_k) (−1)^{x₁·x₂ + ⋯ + x_{k−1}·x_k + x_k·x₁},

with D_f the diagonal matrix of f and H the n-qubit Hadamard matrix. The one-clean-qubit model estimates T_k to constant additive error with k queries. For nonadaptive classical algorithms, [1] proves Θ(N^{1−2/k}) for even k ≥ 4 and, for odd k ≥ 5, the bounds Ω(N^{1−2/(k−1)}) and O(N^{1−2/k}). It conjectures the exponent 1 − 1/⌊k/2⌋ for every k [1, Conjecture 1], and it shows that its product sampler is held at N^{1−2/k} by the term in which all k samples coincide [1, Remark 14].

A *linear estimator* chooses query sets A₁, …, A_k ⊆ F₂ⁿ at random, of total size at most Q, and outputs Σ_{t ∈ A₁×⋯×A_k} w(t) f₁(t₁) ⋯ f_k(t_k), where the weights w depend only on the random choices and not on the answers. The product sampler of [1] is one.

**Theorem 1.** Let k ≥ 3 and ε > 0. Every linear estimator of T_k that is unbiased on every input and has mean squared error at most ε² on every input makes

Q ≥ k · N^{1−2/k} · (ε² + N^{−2})^{−1/k}

queries. For odd k ≥ 5 and constant ε, the product sampler of [1, Corollary 12] meets this bound up to a constant factor, so Θ(N^{1−2/k}) is the complexity of the class, and an estimator with the conjectured exponent 1 − 2/(k − 1) has to depend nonlinearly on the answers. For k = 3 the bound is of order N^{1/3}, while the heavy-coefficient search of [1, Proposition 15], which is nonlinear, uses O(n log n) queries.

**Proposition 2 (character collapse).** Let k ≥ 4, indices mod k, and χ_w(x) = (−1)^{w·x}. Then

T_k(…, f_{j−2}, f_{j−1}, χ_w, f_{j+1}, f_{j+2}, …) = T_{k−2}(…, f_{j−2} χ_w, f_{j−1}(· + w) f_{j+1}, f_{j+2}, …),

and therefore T_k = Σ_w f̂_j(w) · T_{k−2}(…, f_{j−2} χ_w, f_{j−1}(· + w) f_{j+1}, f_{j+2}, …) with f̂_j(w) = E_x f_j(x) χ_w(x). For k = 4 the term is f̂₁(w) · E_x f₂(x + w) f₄(x). For k = 5 each term is a 3-cyclic Forrelation of f₁χ_w, f₂(· + w) f₄ and f₅.

Status: Claim. The inequality of the proof, its constants and the arithmetic of the bound are in Lean. Proposition 2 and the constants are checked by script.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Nonadaptive classical estimation of T_k by linear unbiased estimators, odd k ≥ 5, constant error | O(N^{1−2/k}) by the product sampler [1, Corollary 12]; the full-overlap term of its variance is of order N^{2/(k−1)} at N^{1−2/(k−1)} queries [1, Remark 14] | Ω(N^{1−2/k}) for every linear unbiased estimator, so Θ(N^{1−2/k}) in this class |

## 1. Proof of Theorem 1

Write T_k = Σ_t c(t) f₁(t₁) ⋯ f_k(t_k) with |c(t)| = N^{−(k/2+1)}, so Σ_t |c(t)| = N^{k/2−1}.

1. **Unbiasedness fixes the averaged weights.** The expectation of the output is Σ_t E[w(t) 1{t ∈ A}] f₁(t₁) ⋯ f_k(t_k), with A = A₁ × ⋯ × A_k. Products for distinct tuples t are distinct multilinear monomials in the Nk input signs, so unbiasedness on every input gives E[w(t) 1{t ∈ A}] = c(t) for every t.
2. **Uniform random inputs.** For independent uniform f₁, …, f_k the products for distinct tuples are orthonormal, so for every fixed choice of the sets the second moment of the output, averaged over inputs, is Σ_{t ∈ A} w(t)². Likewise E_f T_k² = Σ_t c(t)² = N^{−2}.
3. **Two applications of the inner-product inequality.** From c(t)² = E[w(t) 1{t ∈ A}]² ≤ E[w(t)² 1{t ∈ A}] · P(t ∈ A) and summing over t,

   (Σ_t |c(t)|)² ≤ E|A| · E Σ_{t ∈ A} w(t)².

   By the inequality of arithmetic and geometric means, |A| = |A₁| ⋯ |A_k| ≤ (Q/k)^k.
4. **Conclusion.** For an unbiased estimator the mean squared error on an input is the second moment minus T_k². Averaged over uniform inputs it is at least N^{k−2} (k/Q)^k − N^{−2}, so some input has at least that error. Error at most ε² everywhere forces (Q/k)^k ≥ N^{k−2}/(ε² + N^{−2}).

For the product sampler, |A| = q^k and the bound of step 3 is the full-overlap term N^{k−2}/q^k of [1, Remark 14].

## 2. Proof of Proposition 2

H D_{χ_w} H is the permutation matrix X_w of the shift x ↦ x + w. So D_{f_{j−1}} H D_{χ_w} H D_{f_{j+1}} = X_w D_{f_{j−1}(·+w)} D_{f_{j+1}}, and H X_w = D_{χ_w} H moves the shift through the Hadamard matrix before it, where it multiplies f_{j−2} by χ_w. Two Hadamard matrices and two diagonals leave the cycle. The expansion follows from f_j = Σ_w f̂_j(w) χ_w and the linearity of T_k in each function.

## 3. Lean

[`lean/LinearEstimators.lean`](lean/LinearEstimators.lean), with [`lean/LinearEstimatorsAxioms.lean`](lean/LinearEstimatorsAxioms.lean) and its output in [`lean/axioms.txt`](lean/axioms.txt):

- `second_moment_ge`: for a random design with probabilities p, sets A_r and weights w_r whose averages are c, (Σ_t |c(t)|)² ≤ (Σ_r p_r |A_r|) · Σ_r p_r Σ_{t ∈ A_r} w_r(t)² (step 3).
- `second_moment_ge_of_card_le`: with |A_r| ≤ M and Σ_r p_r = 1, the second moment is at least (Σ_t |c(t)|)²/M.
- `sum_abs_sq_of_const`: if c(t)² = γ ≥ 0 on a set of m tuples, then (Σ_t |c(t)|)² = m²γ.
- `cyclic_constant`: (N^k)² · N^{−(k+2)} = N^{k−2} for N > 0 and k ≥ 2.
- `second_moment_ge_tight` and `cyclic_constant_two_three`: one design that queries both tuples of a two-element set with weights 1 satisfies every hypothesis of `second_moment_ge` and `second_moment_ge_of_card_le`, and both sides of each bound equal 4 (and 2 after division by M = 2), so the hypotheses can hold and the bound is attained; the constant identity holds at N = 2, k = 3.

Lean 4 v4.36.0-rc1, Mathlib rev d875a8de5222f62cf1c2fafc7984588adadc990a.

Not formalized: step 1 (coefficient matching of multilinear monomials), step 2 (orthonormality of products of independent uniform signs), the inequality of arithmetic and geometric means of step 3, and Proposition 2.

## 4. Measurements

[`sim/identities.py`](sim/identities.py) checks, by exact computation with the Hadamard matrices:

- Proposition 2 for k = 4 to 8, every position j, every w and n = 2, 3, 4 (3,360 cases), with the closed form for k = 4;
- the expansion T_k = Σ_w f̂_j(w) T_k(…, χ_w, …) on the same inputs;
- E_f T_k² = N^{−2} by enumeration of all inputs for (n, k) = (1, 3), (1, 4), (1, 5), (2, 3), and Σ_t |c(t)| = N^{k/2−1}.

Run it with `python identities.py` in `sim/`.

## 5. Limits

- Theorem 1 covers estimators that are linear in the products of one answer per function and unbiased on every input, with the error measured as mean squared error. Medians of several runs, thresholds and estimators that use products of several answers of the same function are outside the class.
- The bound holds for nonadaptive algorithms, where the query sets do not depend on the answers.

## References

1. Y. Zhang, C. Shao. Exponential quantum-classical query separations for cyclic Forrelation. arXiv:2610.41694.

## Use of AI

The proofs, the scripts and this text were produced with the help of Claude Opus 5.5.
