# One attention head computes every fixed subset parity

2026-11-22

## Problem

Tokens x_1, …, x_N ∈ {−1, +1} are given with their positions. For S ⊆ [N] with |S| = k, the order-k interaction is the parity χ_S(x) = ∏_{j∈S} x_j. In [1] a quantum attention head on N qubits is constructed whose single-qubit read-out equals χ_S, for any S with |S| ≤ k, at depth O(log k) [1, Theorem 1 and Appendix B.2]. In [1, Theorem 1] it is also stated that no single classical attention layer with embedding dimension m, H heads and p bits of precision, mHp = o(N/log log N), represents this family. That bound is taken from [1, Lemma 1], which concerns the order-k matching task MATCH_k (is there a tuple whose sum with x_i vanishes modulo M), the task introduced in [2] for k = 3.

The classical model is the one of [2, Definitions 1 to 3]: a row-wise input map of each token and its position, a softmax attention unit with p-bit fixed-point parameters, and a row-wise output map.

| | budget mHp of one classical attention layer for χ_S |
|---|---|
| Stated in [1, Theorem 1] | not o(N/log log N), for every k ≥ 3 |
| Proposition 1 (S fixed) | m = 1, H = 1, p = O(log N) |
| Proposition 2 (S given as input marks) | m = 2, H = 1, p = O(log N) |

## Results

**Proposition 1.** Let S ⊆ [N], |S| = k ≥ 1, and c = ⌈ln(4kN)⌉. The input map sends token j to query 1, key c·1[j ∈ S] and value x_j. The output map rounds the attention output z to p = ⌈log₂(4k)⌉ + 2 fractional bits, sets t = k − 2·round((k − kz)/2) and outputs (−1)^{(k−t)/2}. Then every token outputs χ_S(x), for every x ∈ {−1, +1}^N.

**Proposition 2.** If each token also carries a mark s_j ∈ {0, 1} with S = {j : s_j = 1}, then one head with all scores 0, values (s_j x_j, s_j) and p = ⌈log₂ N⌉ + 2 fractional bits outputs χ_S(x) at every token, for every S and x. Here one fixed layer serves all S at once.

So the family {χ_S : |S| ≤ k} is represented by one attention layer of budget O(log N), per S and also with S as part of the input. This hints at a possible gap in [1, Theorem 1] as worded: the lower bound of [1, Lemma 1] is for MATCH_k, not for the parities that the quantum head realizes.

**Remark (norms).** In [1, Proposition 1] it is stated, citing [3, Proposition 5.1, Lemmas B.2 and B.3], that a bounded-norm attention head representing the parity of an unknown k-subset needs weight norm 2^{Ω(k)}. The results of [3] are constructions, so upper bounds. The parity of the bits in S is a symmetric function of those bits, and by [3, Lemmas B.2 and B.5] one head with a feed-forward output network represents every symmetric k-sparse function exactly, with attention weight norms O(log N) and O(k) and feed-forward norms poly(k). This hints at a possible gap in the norm claim of [1, Proposition 1] for parities.

## Proof

**Proposition 1.** All queries are 1, so every token has the same attention weights: e^c/Z on S and 1/Z elsewhere, Z = k e^c + N − k. The weight outside S is

w_out = (N − k)/(k e^c + N − k) ≤ (N − k)/(4k²N) < 1/(4k).

The output is z = Σ_j w_j x_j. With m_S = (1/k) Σ_{j∈S} x_j,

z − m_S = Σ_{j∉S} w_j x_j − w_out m_S,  so  |z − m_S| ≤ 2 w_out < 1/(2k).

Rounding to p fractional bits moves z by at most 2^{−p−1} ≤ 1/(32k). Hence the rounded value z̃ satisfies |k z̃ − t*| < 1/2 + 1/32 < 1 for t* = Σ_{j∈S} x_j. Since t* ≡ k (mod 2), t* is the unique integer of the parity of k within distance 1 of k z̃, and the output map recovers it as t. Finally (−1)^{(k−t*)/2} = χ_S(x), since (k − t*)/2 is the number of j ∈ S with x_j = −1. The key c ≤ ln(4N²) + 1 and all other parameters use O(log N) bits.

**Proposition 2.** With all scores 0 the softmax weights are exactly 1/N, so the output is (t*/N, k/N) with t* = Σ_{j: s_j = 1} x_j and k = |S|. Rounding to ⌈log₂ N⌉ + 2 fractional bits moves each coordinate by less than 1/(4N), so N times the rounded values round to t* and k. The output map returns (−1)^{(k−t*)/2}.

## Check

`sim/check.py`, output in `sim/out.txt`:

- Proposition 1: every S and every x for N ≤ 12, and 200 random inputs for N up to 10⁵ and k up to 50. The weight bound w_out < 1/(4k) and the output χ_S(x) are asserted.
- Proposition 2: every mark vector s and every x for N ≤ 10.

## Scope

- The classical side is the single-layer model of [2] with input and output maps. Propositions 1 and 2 say nothing on MATCH_k, for which the lower bound of [1, Lemma 1] stands as stated there.
- The quantum construction of [1] loads the bits in the computational basis. The trained head of [1] uses a different encoder, and its empirical learning results are not addressed here.
- The statements are Claims with exact checks on the listed sizes.

## References

1. J. Xu, C. Li, D. Zeng, J. Paisley, Q. Zhao. Higher-order token interactions via quantum attention. arXiv:2606.11673 (2026).
2. C. Sanford, D. Hsu, M. Telgarsky. Representational strengths and limitations of transformers. arXiv:2306.02896.
3. B. L. Edelman, S. Goel, S. Kakade, C. Zhang. Inductive biases and variable creation in self-attention mechanisms. arXiv:2110.10090.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
