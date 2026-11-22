# One attention head computes every fixed subset parity

2026-11-22

## Problem

Tokens x_1, …, x_N ∈ {−1, +1} are given with their positions. For S ⊆ [N] with |S| = k, the order-k interaction is the parity χ_S(x) = ∏_{j∈S} x_j. In [1] a quantum attention head on N qubits is constructed whose single-qubit read-out equals χ_S, for any S with |S| ≤ k, at depth O(log k) [1, Theorem 1 and Appendix B.2]. In [1, Theorem 1] it is also stated that no single classical attention layer with embedding dimension m, H heads and p bits of precision, mHp = o(N/log log N), represents this family. That bound is taken from [1, Lemma 1], which concerns the order-k matching task MATCH_k (is there a tuple whose sum with x_i vanishes modulo M), the task introduced in [2] for k = 3.

The classical model is the one of [2, Definitions 1 to 3]: a row-wise input map to an embedding e_j ∈ ℝ^m, softmax attention units softmax(E Q Kᵀ Eᵀ) E V with matrices Q, K, V, and a row-wise output map, with all numbers in p-bit fixed point. Positions enter as an input coordinate [2, Section 2.1], so p ≥ log₂ N.

| | budget mHp of one classical attention layer for χ_S |
|---|---|
| Stated in [1, Theorem 1] | not o(N/log log N), for every k ≥ 3 |
| Proposition 1 (S fixed) | m = 1, H = 1, p = O(log N) |
| Proposition 2 (S given as input marks) | m = 2, H = 1, p = O(log N) |

## Results

**Proposition 1.** Let S ⊆ [N], |S| = k ≥ 1. The input map sends token j to e_j = 1[j ∈ S]·x_j ∈ ℝ, and the unit has Q = K = 0 and V = 1. The output map rounds the unit output z to p = ⌈log₂ N⌉ + 2 fractional bits, sets t = round(N z) and outputs (−1)^{(k−t)/2}. Then every token outputs χ_S(x), for every x ∈ {−1, +1}^N.

**Proposition 2.** If each token also carries a mark s_j ∈ {0, 1} with S = {j : s_j = 1}, then one unit with e_j = (s_j x_j, s_j), Q = K = 0, V = I and the same precision outputs χ_S(x) at every token, for every S and x. Here one fixed layer serves all S at once. If the input is the single number y_j = s_j x_j ∈ {−1, 0, 1} per token, with no position coordinate, the embedding e_j = (y_j, y_j²) gives the same.

So the family {χ_S : |S| ≤ k} is represented by one attention layer of budget O(log N), per S and also with S as part of the input. This hints at a possible gap in [1, Theorem 1] as worded: the lower bound of [1, Lemma 1] is for MATCH_k, not for the parities that the quantum head realizes.

**Remark (readings of [1, Theorem 1]).** The quantum witness of [1, Appendix B.2] is one circuit per S, with read-out qubit in S, which is the setting of Proposition 1. In [1, Appendix B] the classical class has input dimension 1, so no position coordinate. Every layer of that class commutes with permutations of the tokens, so for 1 ≤ |S| ≤ N − 1 no layer of any budget outputs χ_S from x alone, also for k = 1 and k = 2. Under that reading the statement holds for a reason unrelated to [1, Lemma 1] and to the order k, and the quantum circuit of [1], which is not permutation invariant, is compared with a class that cannot see positions. With S given in the input, Proposition 2 covers input dimension 1. The setting where each token carries its own subset is not covered here.

**Remark (norms).** In [1, Proposition 1] it is stated, citing [3, Proposition 5.1, Lemmas B.2 and B.3], that a bounded-norm attention head representing the parity of an unknown k-subset needs weight norm 2^{Ω(k)} and Ω(k) heads. To our knowledge [3] contains no lower bound on weight norms; its lower bounds concern pseudo-dimension and sample size. The parity of the bits in S is a symmetric function of those bits, and by [3, Lemmas B.2 and B.5] one head with a feed-forward output network represents every symmetric k-sparse function exactly, with attention weight norms O(log N) and O(k) and feed-forward norms poly(k), under the input mapping of [3] (bits in {0, 1} added to near-orthogonal position vectors of dimension d ≥ k, with a class token). In [3], k heads appear only for general k-sparse functions. This hints at a possible gap in the norm claim of [1, Proposition 1] for parities.

## Proof

**Proposition 1.** With Q = K = 0 all scores are 0, so the softmax weights are exactly 1/N at every token, and the unit outputs z = (1/N) Σ_{j∈S} x_j = t*/N with t* = Σ_{j∈S} x_j. Rounding to p fractional bits moves z by at most 2^{−p−1} ≤ 1/(8N), so N times the rounded value lies within 1/8 of the integer t*, and t = t*. Finally (−1)^{(k−t*)/2} = χ_S(x), since (k − t*)/2 is the number of j ∈ S with x_j = −1. All numbers involved, including the positions, use O(log N) bits.

**Proposition 2.** The unit outputs (t*/N, k/N) with t* = Σ_{j: s_j = 1} x_j and k = |S|, and the rounding argument above recovers both. The output map returns (−1)^{(k−t*)/2}. With e_j = (y_j, y_j²) the second coordinate is again k/N, since y_j² = s_j.

## Check

`sim/check.py`, output in `sim/out.txt`. The script builds the embeddings and applies the unit with the stated Q, K, V:

- Proposition 1: every S and every x for N ≤ 12, and for N up to 10⁴ and k up to 50 three random S with 100 random inputs each.
- Proposition 2, with and without position coordinate: every mark vector s and every x for N ≤ 10.

## Lean

`lean/SubsetParity/Basic.lean` proves the counting step of Propositions 1 and 2: for a list of signs the product is (−1)^m and the length minus the sum is 2m, with m the number of entries −1 (`prod_sum_signs`, `prod_eq_from_count`); rounding recovers an integer from a value within 1/2 of it (`round_eq_of_near`); and rounding to p fractional bits with 2^p ≥ 4N moves N z by at most 1/8 (`rounding_error`). `lean/axioms.txt` lists the axioms of every named theorem: only `propext`, `Classical.choice` and `Quot.sound`. The rest of the proofs is a Claim.

## Scope

- The classical side is the single-layer model of [2] with input and output maps. The lower bound of [1, Lemma 1] for MATCH_k is not addressed here.
- The quantum construction of [1] loads the bits in the computational basis. The trained head of [1] uses a different encoder, and its empirical learning results are not addressed here.
- The statements are Claims with exact checks on the listed sizes. Lean covers only the steps listed in the Lean section.

## References

1. J. Xu, C. Li, D. Zeng, J. Paisley, Q. Zhao. Higher-order token interactions via quantum attention. arXiv:2606.11673 (2026).
2. C. Sanford, D. Hsu, M. Telgarsky. Representational strengths and limitations of transformers. arXiv:2306.02896.
3. B. L. Edelman, S. Goel, S. Kakade, C. Zhang. Inductive biases and variable creation in self-attention mechanisms. arXiv:2110.10090.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
