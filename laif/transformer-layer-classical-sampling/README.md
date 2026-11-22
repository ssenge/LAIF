# Classical sampling for a transformer layer with block-encoding normalization

2026-11-22

## Problem

A single transformer layer acts on a sequence S ∈ ℝ^{N×d} of N tokens. It has weights W_q, W_k, W_v ∈ ℝ^{d×d} and a two-layer feed-forward network M₁ ∈ ℝ^{N₁×d}, M₂ ∈ ℝ^{d×N₁}. For a token j it computes:

- the attention row G_j = Σ_k p_k V_k, with V = S W_v, p_k = e^{s_k}/Z_j, Z_j = Σ_k e^{s_k} and s_k = (S W_q W_kᵀ Sᵀ)_{jk}/α₀;
- ψ = LN(G_j + S_j) and Transformer(S, j) = LN(ψ + M₂ GELU(M₁ ψ)).

Here LN(z) = Pz/‖Pz‖ with the centring projection Pz = z − z̄𝟙. This is the layer normalization with γ = 1/√d and β = 0 of [1, Problem 2], and LN(z) := 0 when Pz = 0. Following [1, proofs of Theorems S10 and S12], let ς = ‖P(G_j + S_j)‖ and ς′ = ‖P(ψ + M₂ GELU(M₁ψ))‖.

In [1] the inputs are given as block encodings:

- S, with normalization α_s;
- the weights, with normalization α_w;
- M₁ and M₂, with normalization α_m.

As in [1], α_s ≥ ‖S‖ and α_w ≥ ‖W_q‖, ‖W_k‖, ‖W_v‖. The scaling factor of the scores is changed from the classical √d to α₀ = α_s² α_w² [1, Problem 1]. With this input, a state proportional to Transformer(S, j) is prepared with

Õ(d α_s α_w α_m³ √(N/Z_j) /(ς ς′))

uses of the block encodings [1, Theorem S12]. Under the assumptions of [1], this is Õ(√N d) [1, Theorem 1]. Those assumptions are ‖S‖_F = O(√N), weights and α_m of order 1, Z_j = Ω(N) and ς, ς′ = Ω(1).

For the classical side, [1, Section IV F and Appendix D.4] assumes sample and query access [3] to Q, K and V, and also to the softmax row. With the approximate matrix-vector product of [1, Lemma S7], it states a query complexity of Θ(‖S‖_F² ‖W_v‖_F²/ε²) for the attention row. It concludes that "there is at least a quadratic separation on the matrix norm ‖S‖_F, and our quantum algorithm cannot be effectively dequantized". The softmax is described as a further obstacle for classical algorithms, since estimating a partition function is #P-hard in the worst case. Whether this prevents dequantization when the matrix norms are polylog(N) is stated as an open problem [1, Appendix D.4].

The algorithm below needs only uniformly random indices in [N], queries to the entries of S, the weight matrices, and the numbers α_s and α_w.

| | cost for Transformer(S, j) |
|---|---|
| quantum, state preparation [1, Theorem S12] | Õ(d α_s α_w α_m³ √(N/Z_j)/(ς ς′)); Õ(√N d) under the assumptions of [1] |
| quantum, classical vector to ℓ∞ error ε [1, Theorem S14] | Õ(√N d log d/ε²) under the assumptions of [1] |
| classical attention row, as stated in [1] | Θ(‖S‖_F² ‖W_v‖_F²/ε²) queries |
| Theorem 2, classical vector to ℓ₂ error ε | O(md + d² + N₁d) time and md + d queries to S, with m = O((1 + α_m²)² ‖S‖_F² α_w² /(N ς² ς′² ε²)); O(1/ε²) samples under the assumptions of [1] |

## Results

Let b = max_k |s_k|. Since |(S W_q W_kᵀ Sᵀ)_{jk}| ≤ ‖S_j‖ ‖S_k‖ ‖W_q‖ ‖W_k‖ ≤ α_s² α_w² = α₀, the scaling of [1] gives b ≤ 1. The softmax weights then satisfy e^{−2b}/N ≤ p_k ≤ e^{2b}/N, and Z_j ∈ [e^{−b}N, e^{b}N]. Write r² = ‖S W_v‖_F²/N ≤ ‖S‖_F² ‖W_v‖²/N for the mean squared norm of the value rows, and c(b) = 2e^{4b}(1 + e^{2b} sinh² b), so c(1) < 1224.

**Algorithm.** Draw m indices k₁, …, k_m uniformly from [N], with w_i = e^{s_{k_i}}, and output

Ĝ_j = (Σ_i w_i S_{k_i}) W_v / Σ_i w_i.

The vector u = S_j W_q W_kᵀ/α₀ is computed once, so each sample costs one row of S and O(d) operations. The partition function Z_j is never needed.

**Theorem 1 (attention row).** E‖Ĝ_j − G_j‖² ≤ c(b) r²/m.

**Theorem 2 (one layer).** Let Ô be the layer output computed with Ĝ_j in place of G_j, and let L = 1.13 ‖M₁‖ ‖M₂‖. In every run,

‖Ô − Transformer(S, j)‖ ≤ 4(1 + L) ‖Ĝ_j − G_j‖ /(ς ς′).

So m = 3 c(b) (4(1 + L))² r² /(ς² ς′² ε²) samples give error at most ε with probability at least 2/3. Repeat this O(log(1/δ)) times and return an output that lies within 2ε of more than half of all runs, itself included. That output has error at most 3ε with probability at least 1 − δ.

**Proposition 3 (near-uniform weights).** Let V̄ be the mean of the rows of V. Then ‖G_j − V̄‖ ≤ (e^{2b} − 1) r, and b ≤ max_k ‖S_k‖²/‖S‖². For tokens of norm at most 1 and ‖S‖_F² ≥ cN, this gives b ≤ d/(cN).

The partition function Z_j is a mean of N terms in [e^{−b}, e^{b}]. So uniform sampling estimates it to relative error ε with O(1 + e^{2b} sinh²(b)/ε²) samples, for every N and every matrix norm.

## Proofs

**Theorem 1.** Let A = (1/N) Σ_k e^{s_k} V_k and B = Z_j/N, so G_j = A/B. The estimator is Â/B̂, with the sample means Â = (1/m) Σ_i w_i V_{k_i} and B̂ = (1/m) Σ_i w_i.

- Every weight lies in [e^{−b}, e^{b}], so B, B̂ ≥ e^{−b}.
- ‖A‖ ≤ e^b (1/N) Σ_k ‖V_k‖ ≤ e^b r, since the mean of the norms is at most their root mean square.
- From Â/B̂ − A/B = (Â − A)/B̂ + A (B − B̂)/(B B̂) it follows that ‖Ĝ_j − G_j‖ ≤ e^b ‖Â − A‖ + e^{3b} r |B̂ − B|.
- Each sample of Â has second moment at most e^{2b} r², so E‖Â − A‖² ≤ e^{2b} r²/m.
- A variable with values in an interval of length ℓ has variance at most ℓ²/4, so E|B̂ − B|² ≤ (e^b − e^{−b})²/(4m) = sinh²(b)/m.
- Combining these with (x + y)² ≤ 2x² + 2y² gives the bound.

**Theorem 2.** For a ≠ 0, ‖a/‖a‖ − a′/‖a′‖‖ ≤ 2‖a − a′‖/‖a‖, and the same bound holds when a′ = 0 and a′/‖a′‖ is read as 0. The projection P does not increase norms. So ‖ψ̂ − ψ‖ ≤ 2‖Ĝ_j − G_j‖/ς.

The derivative of GELU(x) = x Φ(x), with Φ the standard normal distribution function, is Φ(x) + x Φ′(x). Its absolute value is at most Φ(√2) + √2 Φ′(√2) < 1.129. So the map ψ ↦ ψ + M₂ GELU(M₁ψ) changes distances by a factor at most 1 + L. The second layer normalization multiplies the error by at most 2/ς′.

The probability statement follows from Theorem 1 and the bound P(X ≥ ε²) ≤ E X/ε² for X ≥ 0. For the repetition step: with probability 1 − δ, more than half of the runs lie within ε of the truth. These runs are within 2ε of each other, so at least one output passes the test. Any output that passes it is within 2ε of some good run, and so within 3ε of the truth.

**Proposition 3.** G_j − V̄ = Σ_k (p_k − 1/N)(V_k − V̄) and |p_k − 1/N| ≤ (e^{2b} − 1)/N. The root mean square of ‖V_k − V̄‖ is at most r. For the bound on b: |s_k| ≤ ‖S_j‖ ‖S_k‖ ‖W_q‖ ‖W_k‖/(α_s² α_w²) ≤ max_k ‖S_k‖²/‖S‖². Also ‖S‖² ≥ ‖S‖_F²/d.

## Remarks

- [1, Lemma S7] has cost Θ(‖A‖_F² ‖x‖²/ε²) for a product Ax. For the attention row, A = Vᵀ and x is the softmax row. Under the scaling α₀ = α_s² α_w², ‖x‖² ≤ e^{2b}/N ≤ e²/N. So the lemma itself gives O(‖S‖_F² ‖W_v‖_F²/(N ε²)), while the comparison in [1, Section IV F and Appendix D.4] uses Θ(‖S‖_F² ‖W_v‖_F²). This hints at a possible gap in the separation argument. Under the assumptions of [1, Theorem 1], this cost has no dependence on N at a fixed precision, while the quantum bound grows as √N. Theorems 1 and 2 give this with uniform sampling and entry queries only, without the value of Z_j, and for the full layer.
- The partition function is not an obstacle under this scaling, for any matrix norms, including the polylog(N) regime of [1, Appendix D.4]. The cost of Theorem 2 depends on r²/(ς² ς′²), which does not change when S is multiplied by a constant. It is not small in every regime: for a few tokens of norm 1 among N zero rows, ς falls like 1/N. The quantum bound then also grows through its factor 1/(ς ς′).
- The quantum bound for preparing the state is polylogarithmic in 1/ε and linear in 1/(ς ς′). Theorem 2 outputs a classical vector in ℓ₂, which is stronger than the ℓ∞ readout of [1, Theorem S14], with cost quadratic in 1/ε and in 1/(ς ς′). The classical time also has the terms d² + N₁d from the weights.
- For k layers, every token after a layer normalization has norm 1, so ‖S‖_F² = N and r ≤ α_w from the second layer on. Under the constant-precision convention of [1, Section IV E], all N tokens of a layer cost O(N (md + d² + N₁d) log N) classically, with the log N factor so that all tokens succeed together. The corresponding cost in [1] is Õ(N^{3/2} d). Errors carried from layer to layer are not tracked here on either side.
- For the full attention matrix with entries bounded by o(√log N) and d = O(log N), an almost linear-time classical algorithm is given in [2]. Element-wise transforms of block-encoded matrices, including the step of [1, Theorems S8 and S9], are studied in [4]. That work also shows that one element-wise transform preserves oversampling and query access.

## Check

`sim/check.py`, output in `sim/out.txt`. The setup:

- The weights and both feed-forward matrices have spectral norm 1, with d = 16 and N₁ = 64.
- α_s = ‖S‖, the smallest normalization allowed.
- Each instance uses m = 2000 samples in 20 runs.

There are five families of sequences:

- random tokens of norm about 1;
- two opposite clusters;
- ten tokens with 30 times the norm;
- one dominant token;
- one dominant query token with W_q W_kᵀ = I, so that b = 1 up to rounding.

For N = 10³, 10⁴, 10⁵ and 10⁶ the script asserts:

- b ≤ 1 and Z_j/N ∈ [e^{−1}, e];
- the mean squared error of Ĝ_j is at most c(b) r²/m;
- the bound of Theorem 2 holds in every run.

For the random tokens, the mean output error is 0.011 to 0.016 for every N from 10³ to 10⁶.

## Scope

- The scaling is α₀ = α_s² α_w² of [1]. For the classical scaling α₀ = √d the exponents are not bounded, and that case is not treated here.
- The comparison is with the stated quantum complexity, not with a quantum lower bound.
- The sample count m is stated in terms of r, ς and ς′, as the quantum bound is stated in terms of ς, ς′ and Z_j.
- Lean: not formalized.

## References

1. N. Guo, Z. Yu, M. Choi, Y. Han, A. Agrawal, K. Nakaji, A. Aspuru-Guzik, P. Rebentrost. Quantum transformer: Accelerating model inference via quantum linear algebra. arXiv:2402.16714.
2. J. Alman, Z. Song. Fast attention requires bounded entries. arXiv:2302.13214.
3. E. Tang. A quantum-inspired classical algorithm for recommendation systems. arXiv:1807.04271.
4. Z. M. Rossi, R. Sarkar. Quantum element-wise transforms. arXiv:2606.06456.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
