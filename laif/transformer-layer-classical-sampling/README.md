# Classical sampling for a transformer layer with block-encoding normalization

2026-11-22

## Problem

A single transformer layer acts on a sequence S ∈ ℝ^{N×d} of N tokens with weights W_q, W_k, W_v ∈ ℝ^{d×d} and a two-layer feed-forward network M₁ ∈ ℝ^{N₁×d}, M₂ ∈ ℝ^{d×N₁}. For a token j it outputs

- the attention row G_j = Σ_k p_k V_k, with V = S W_v, p_k = e^{s_k}/Z_j, Z_j = Σ_k e^{s_k} and s_k = (S W_q W_kᵀ Sᵀ)_{jk}/α₀;
- ψ = LN(G_j + S_j) and Transformer(S, j) = LN(ψ + M₂ GELU(M₁ ψ)).

Here LN(z) = (z − z̄𝟙)/‖z − z̄𝟙‖ is the layer normalization with γ = 1/√d and β = 0, and ς, ς′ are the standard deviations of the entries of G_j + S_j and of ψ + M₂ GELU(M₁ψ), as in [1, Problems 1 to 3].

In [1] the inputs are given as block encodings: S with normalization α_s ≥ ‖S‖, the weights with normalization α_w, and M₁, M₂ with normalization α_m. The scaling factor of the scores is changed from the classical √d to α₀ = α_s² α_w² [1, Problem 1]. With this input, a state proportional to Transformer(S, j) is prepared with

Õ(d α_s α_w α_m³ √(N/Z_j) /(ς ς′))

uses of the block encodings [1, Theorem S12]. Under the norm assumptions of [1], ‖S‖_F = O(√N) and weights of norm O(1), this is Õ(√N d) [1, Theorem 1]. For the classical side, [1, Section F and Appendix D.4] considers sample and query access to S and states a query complexity of Θ(‖S‖_F² ‖W_v‖_F²/ε²) for the attention row, from the approximate matrix-vector product of [1, Lemma S7]. It concludes that there is "at least a quadratic separation on the matrix norm ‖S‖_F, and our quantum algorithm cannot be effectively dequantized". The softmax is described as a further obstacle for classical algorithms, since estimating a partition function is #P-hard in the worst case. Whether this prevents dequantization when the matrix norms are polylog(N) is stated as an open problem [1, Appendix D.4].

The algorithm below uses less than the sample and query access of [1, 3]. It needs uniformly random indices in [N] and queries to the entries of S.

| | cost for Transformer(S, j) |
|---|---|
| quantum, state preparation [1, Theorem S12] | Õ(d α_s α_w α_m³ /(ς ς′)), which is Õ(√N d) under the norm assumptions of [1] |
| classical attention row, as stated in [1] | Θ(‖S‖_F² ‖W_v‖_F²/ε²) queries |
| Theorem 2, classical, ℓ₂ error ε | O(md + d² + N₁d) time and md + d queries to S, with m = O((1 + α_m²)² ‖S‖_F² α_w² /(N d² ς² ς′² ε²)), which is independent of N under the norm assumptions of [1] |

## Results

Let b = max_k |s_k|. Since |(S W_q W_kᵀ Sᵀ)_{jk}| ≤ ‖S_j‖ ‖S_k‖ ‖W_q‖ ‖W_k‖ ≤ α_s² α_w² = α₀, the scaling of [1] gives b ≤ 1. The softmax weights then satisfy e^{−2b}/N ≤ p_k ≤ e^{2b}/N, and Z_j ∈ [e^{−b}N, e^{b}N]. Write r² = ‖S W_v‖_F²/N ≤ ‖S‖_F² ‖W_v‖²/N for the mean squared norm of the value rows, and c(b) = 2e^{4b}(1 + e^{2b} sinh² b), so c(1) < 1224.

**Algorithm.** Draw m indices k₁, …, k_m uniformly from [N], with w_i = e^{s_{k_i}}, and output

Ĝ_j = (Σ_i w_i S_{k_i}) W_v / Σ_i w_i.

The vector u = S_j W_q W_kᵀ/α₀ is computed once, so each sample costs one row of S and O(d) operations.

**Theorem 1 (attention row).** E‖Ĝ_j − G_j‖² ≤ c(b) r²/m.

**Theorem 2 (one layer).** Let Ô be Transformer computed with Ĝ_j in place of G_j, and let L = 1.13 ‖M₁‖ ‖M₂‖. In every run,

‖Ô − Transformer(S, j)‖ ≤ 4(1 + L) ‖Ĝ_j − G_j‖ /(d ς ς′).

So m = 3 c(b) (4(1 + L))² r² /(d² ς² ς′² ε²) samples give error at most ε with probability at least 2/3. Repeating O(log(1/δ)) times and returning an output that lies within 2ε of more than half of the others gives error at most 3ε with probability at least 1 − δ.

**Proposition 3 (near-uniform weights).** Let V̄ be the mean of the rows of V. Then ‖G_j − V̄‖ ≤ (e^{2b} − 1) r. If α_s ≥ ‖S‖ and α_w ≥ ‖W_q‖, ‖W_k‖, then b ≤ max_k ‖S_k‖²/‖S‖². For tokens of norm at most 1 and ‖S‖_F² ≥ cN, this gives b ≤ d/(cN).

The partition function Z_j is a mean of N terms in [e^{−b}, e^{b}], so uniform sampling estimates it to relative error ε with O(e^{2b} sinh²(b)/ε²) samples, for every N.

## Proofs

**Theorem 1.** Let A = (1/N) Σ_k e^{s_k} V_k and B = Z_j/N, so G_j = A/B. The estimator is Â/B̂ with the sample means Â = (1/m) Σ_i w_i V_{k_i} and B̂ = (1/m) Σ_i w_i. Every weight lies in [e^{−b}, e^{b}], so B, B̂ ≥ e^{−b}. Also ‖A‖ ≤ e^b (1/N) Σ_k ‖V_k‖ ≤ e^b r, since the mean of the norms is at most their root mean square. From

Â/B̂ − A/B = (Â − A)/B̂ + A (B − B̂)/(B B̂)

it follows that ‖Ĝ_j − G_j‖ ≤ e^b ‖Â − A‖ + e^{3b} r |B̂ − B|. Each sample of Â has second moment at most e^{2b} r², so E‖Â − A‖² ≤ e^{2b} r²/m. A variable with values in an interval of length ℓ has variance at most ℓ²/4, so E|B̂ − B|² ≤ (e^b − e^{−b})²/(4m) = sinh²(b)/m. Combining these with (x + y)² ≤ 2x² + 2y² gives the bound.

**Theorem 2.** For a ≠ 0, ‖a/‖a‖ − a′/‖a′‖‖ ≤ 2‖a − a′‖/‖a‖. Layer normalization is this map applied after the centring projection P, which does not increase norms, and ‖P(G_j + S_j)‖ = √d ς. So ‖ψ̂ − ψ‖ ≤ 2‖Ĝ_j − G_j‖/(√d ς). The derivative of GELU(x) = x Φ(x), with Φ the standard normal distribution function, is Φ(x) + x Φ′(x), and its absolute value is at most Φ(√2) + √2 Φ′(√2) < 1.129. So ψ ↦ ψ + M₂ GELU(M₁ψ) is (1 + L)-Lipschitz. The second layer normalization multiplies the error by at most 2/(√d ς′). The probability statement follows from Theorem 1 and the bound P(X ≥ ε²) ≤ E X/ε² for X ≥ 0. The repetition step is the usual one: with probability 1 − δ more than half of the runs are within ε of the truth, and then any output within 2ε of more than half of the runs is within 3ε of it.

**Proposition 3.** G_j − V̄ = Σ_k (p_k − 1/N)(V_k − V̄) and |p_k − 1/N| ≤ (e^{2b} − 1)/N. The root mean square of ‖V_k − V̄‖ is at most r. For the bound on b, |s_k| ≤ ‖S_j‖ ‖S_k‖ ‖W_q‖ ‖W_k‖/(α_s² α_w²) ≤ max_k ‖S_k‖²/‖S‖², and ‖S‖² ≥ ‖S‖_F²/d.

## Remarks

- In the comparison of [1, Section F], the classical cost Θ(‖S‖_F² ‖W_v‖_F²/ε²) is the cost of one method, the importance-sampling product of [1, Lemma S7] applied with sample access to the scores. Since the scaling α₀ = α_s² α_w² keeps all weights within a constant factor of 1/N, uniform sampling of the tokens already gives a cost that depends on ‖S‖_F²/N instead of ‖S‖_F². This hints at a possible gap in the separation argument. Under the norm assumptions of [1, Theorem 1], Theorem 2 has no dependence on N at a fixed precision, while the quantum bound grows as √N.
- The partition function is not an obstacle under this scaling, for any matrix norms, including the polylog(N) regime of [1, Appendix D.4]. In that regime ‖S‖_F²/N is even smaller.
- The quantum bound is for preparing a state, with error polylogarithmic in 1/ε and linear in 1/(ς ς′). Theorem 2 outputs a classical vector, with cost quadratic in 1/ε and in 1/(ς ς′). Reading out a classical vector from the quantum state adds a factor that grows with 1/ε [1, Section II E].
- For k layers, every token after a layer normalization has norm 1, so ‖S‖_F² = N and r ≤ α_w from the second layer on. Under the constant-precision convention of [1, Section II E], the N tokens of a layer cost O(N m d) classically, against Õ(N^{3/2} d) in [1]. Errors are carried from layer to layer on both sides, and they are not tracked here.
- For the full attention matrix with entries bounded by o(√log N), and for d = O(log N), an almost linear-time classical algorithm is given in [2]. Theorem 1 concerns one row with exponents bounded by 1, and its cost does not depend on N.

## Check

`sim/check.py`, output in `sim/out.txt`. The weights and both feed-forward matrices have spectral norm 1, d = 16, N₁ = 64, α_s = ‖S‖ (the smallest normalization allowed) and m = 2000 samples in 20 runs. There are four families of sequences: random tokens of norm about 1, two opposite clusters, ten tokens of 30 times the norm, and one dominant token. For N = 10³, 10⁴, 10⁵ and 10⁶ the script asserts:

- b ≤ 1 and Z_j/N ∈ [e^{−1}, e];
- the mean squared error of Ĝ_j is at most c(b) r²/m;
- the bound of Theorem 2 holds in every run.

For the random tokens, the mean output error is 0.011 to 0.016 for every N from 10³ to 10⁶.

## Scope

- The scaling is α₀ = α_s² α_w² of [1]. For the classical scaling α₀ = √d the exponents are not bounded, and that case is not treated here.
- The comparison is with the stated quantum complexity, not with a quantum lower bound.
- Lean: not formalized.

## References

1. N. Guo, Z. Yu, M. Choi, Y. Han, A. Agrawal, K. Nakaji, A. Aspuru-Guzik, P. Rebentrost. Quantum transformer: Accelerating model inference via quantum linear algebra. arXiv:2402.16714.
2. J. Alman, Z. Song. Fast attention requires bounded entries. arXiv:2302.13214.
3. E. Tang. A quantum-inspired classical algorithm for recommendation systems. arXiv:1807.04271.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
