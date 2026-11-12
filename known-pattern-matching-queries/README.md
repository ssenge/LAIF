# Pattern matching with a known pattern, with quantum queries

Written 12 Nov 2026.

**Setting.** A pattern y ∈ Σ^m over a finite alphabet Σ is known in advance, and the text x ∈ Σ^n, with n ≥ m, is given by queries: a query returns one character x_j. The task is to decide whether y occurs in x, that is, whether x[i, i + m) = y for some start i ∈ [0, n − m].

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Does a known pattern occur in the text? | O(√(n log p)) for a pattern of period p over a constant-size alphabet [1]; O(√(n log m) + √(m log³ m log log m)), also with the pattern given by queries [2], improving [10] | O(√(n − m + 1) + √m) for every pattern over every finite alphabet, and an occurrence is found within the same bound | Claim; checked by script |
| Prop 2 | Lower bound | Ω(√n) for patterns of length 1 | Ω(√n) for every m ≤ n/2, so Theorem 1 is optimal there | Claim |

## 1. The windows of a block

Let w = max(1, ⌊m/4⌋), and call the starts in [b, b + w) a *block*. With s = b + w − 1 and L = m − w + 1, every start i = s − δ of the block, with δ ∈ [0, w), covers the positions [s, s + L), and an occurrence at i forces

M := x[s, s + L) = y[δ, δ + L).

So M must equal one of the *windows* y_δ = y[δ, δ + L), and the set Δ = {δ ∈ [0, w) : y_δ = M} contains the shift of every occurrence in the block. Let q be the least period of M.

**Lemma 1.** If Δ has two elements, all differences of elements of Δ are multiples of q, and y has period q on [min Δ, max Δ + L).

*Proof.* Let δ < δ′ be in Δ and d = δ′ − δ < w ≤ m/4. Then S = y[δ, δ′ + L) has period d, so M = S[0, L) has the periods d and q ≤ d. As q + d ≤ 2d < m/2 < L, by the periodicity lemma [3] gcd(q, d) is a period of M, and so it equals q, which divides d. For k with k + q < L + d, let k′ = k − td ∈ [0, d). Since k′ + q < d + q < L, the period q of M and the period d of S give S[k] = S[k′] = S[k′ + q] = S[k + q]. So S has period q. Windows of consecutive elements of Δ overlap in at least L > q positions, so their union has period q. ∎

If |Δ| ≥ 2, let [ℓ, r) be the largest interval containing [min Δ, max Δ + L) on which y has period q. Call j a *break* of the text if x_j ≠ x_{j+q}. Let λ be the largest break in [s − m, s), and ρ − q the smallest break with ρ in [s + L, s + L + m), if they exist.

**Lemma 2.** Let |Δ| ≥ 2 and i = s − δ with δ ∈ Δ.
1. If ℓ > 0 and y occurs at i, then λ = i + ℓ − 1.
2. If r < m and y occurs at i, then ρ = i + r.
3. If ℓ = 0 and r = m, then y occurs at i iff no break lies in [i, s) and no ρ lies in [s + L, i + m).

*Proof.* An occurrence at i copies the period of y on [ℓ, r) to x on [i + ℓ, i + r), so no j ∈ [i + ℓ, i + r − q) is a break. If ℓ > 0, then y_{ℓ−1} ≠ y_{ℓ−1+q}, so i + ℓ − 1 is a break. It lies in [s − m, s), and every j in (i + ℓ − 1, s) has j + q < s + L ≤ i + r, so it is not a break. This gives (1), and (2) is symmetric. In case (3), y has period q. If x has period q on [i, i + m) and agrees with y on [s, s + L), which has length L ≥ q, then x agrees with y on all of [i, i + m). The converse is clear. ∎

`sim/check_blocks.py` checks Lemmas 1 and 2 and the resulting block decision against brute force on about 950 000 blocks over alphabets of size 2 and 3. The inputs are random patterns and texts, periodic and nearly periodic patterns, patterns with a periodic run broken at one or both ends, and texts with long periodic runs and planted occurrences. It also asserts the periodicity statements of Lemma 1.

## 2. The algorithm

**Theorem 1.** For every known pattern y ∈ Σ^m and n ≥ m, it can be decided with O(√(n − m + 1) + √m) quantum queries and bounded error whether y occurs in a text x ∈ Σ^n. Within the same bound an occurrence is found.

*Proof.* Fix a block. Its decision B_b uses a constant number of steps, each with O(√m) queries and an error amplified to a small constant by a constant number of repetitions.

1. *Identify M.* The distinct windows y_δ, δ ∈ [0, w), are at most w ≤ m/4 strings of L characters. Written in binary they form a set of at most w strings of N ≥ L > w bits, and for at most N strings the unknown one is identified with O(√w) queries [4, Proposition 2]. A query of a character answers every bit query of that character. Run this on M, and check the answer δ̂ by a search for a mismatch between M and y_δ̂ with O(√m) queries [5]. If it fails, Δ is empty and B_b = 0. Otherwise M = y_δ̂ is known, so Δ and q follow with no queries.
2. *One window.* If Δ = {δ}, verify the start s − δ by a search for a mismatch with O(√m) queries.
3. *Several windows.* Otherwise compute λ or ρ by a search for the largest or smallest break in a range of m positions, a maximum or minimum finding over tests of two queries each, with O(√m) queries [6]. If ℓ > 0, Lemma 2(1) leaves the single start i = λ − ℓ + 1, kept only if s − i ∈ Δ, and it is verified as in step 2. The case r < m is symmetric. If ℓ = 0 and r = m, compute both λ and ρ, and by Lemma 2(3) the block contains an occurrence iff some δ ∈ Δ has λ < s − δ and s − δ + m ≤ ρ, with λ = −∞ or ρ = ∞ when there is none, which needs no further queries.

So B_b has bounded-error query complexity O(√m). The blocks with b a multiple of w up to n − m number K ≤ 4(n − m + 1)/m + 1, and y occurs iff some B_b = 1. The OR of K functions on a shared input, each with bounded-error complexity at most T, has bounded-error complexity O(√K T): the adversary bound characterizes bounded-error complexity [7, 8], and the composition of its dual solutions, with the OR on the outside, allows inner functions that read overlapping parts of the input. This is the functional composition of [Section 4 of the empty rectangle folder](../largest-empty-rectangle-queries/README.md#4-one-dimension). This gives O(√(Km)) = O(√(n − m + 1) + √m). Finding a block with B_b = 1, by search with a bounded-error test [9], and then its occurrence in step 2 or 3, costs the same. ∎

## 3. Lower bound

**Proposition 2.** For m ≤ n/2 and the pattern c^m, with a second character d, deciding whether the pattern occurs needs Ω(√n) quantum queries.

*Proof.* Take a = ⌊(n + 1)/(m + 1)⌋ blocks of m positions, each followed by one d, and d in all remaining positions. Every run of m consecutive characters c lies in one block, so c^m occurs iff some block is all c. This is OR over a blocks of AND over m characters, which needs Ω(√(am)) queries [8]. As a ≥ (n + 1)/(2(m + 1)), am ≥ (n + 1)/4. ∎

## Scripts

`sim/check_blocks.py` (Section 1) runs in a few seconds with Python 3 and no extra packages.

**Not formalized:** Lemmas 1 and 2, the oracle identification [4], the searches [5, 6, 9], the composition [7, 8], and the periodicity lemma [3].

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. A. Cornelissen. Quantum algorithms through graph composition. arXiv:2504.02115, Theorem 6.3.
2. Q. Wang, M. Ying. Quantum algorithm for lexicographically minimal string rotation. arXiv:2012.09376.
3. N. J. Fine, H. S. Wilf. Uniqueness theorems for periodic functions. Proc. Amer. Math. Soc. 16, 1965.
4. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
5. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
6. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
7. T. Lee, R. Mittal, B. W. Reichardt, R. Špalek, M. Szegedy. Quantum query complexity of state conversion. FOCS 2011. arXiv:1011.3020.
8. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
9. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
10. H. Ramesh, V. Vinay. String matching in Õ(√n + √m) quantum time. J. Discrete Algorithms 1, 2003. arXiv:quant-ph/0011049.
