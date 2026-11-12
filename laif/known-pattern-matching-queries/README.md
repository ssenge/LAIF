# Pattern matching with a known pattern, with quantum queries

Written 12 Nov 2026.

**Setting.** A pattern y ∈ Σ^m over a finite alphabet Σ is known in advance, and the text x ∈ Σ^n, with n ≥ m, is given by queries: a query returns one character x_j. The task is to decide whether y occurs in x, that is, whether x[i, i + m) = y for some start i ∈ [0, n − m].

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Does a known pattern occur in the text? | O(√(n log m)), and O(√(n log p)) for a pattern of period p, over a constant-size alphabet [1]; O(√(n log m) + √(m log³ m log log m)), also with the pattern given by queries [2] | O(√n) for every pattern over every finite alphabet, and an occurrence is found within the same bound | Claim; checked by script; Lemmas 1 and 2 in Lean |
| Prop 2 | Lower bound | Ω(√n) for patterns of length 1 | Ω(√n) for every m ≤ n, for the pattern c^m, so Theorem 1 is optimal for every m in the worst case over patterns | Claim |

## 1. The windows of a block

Let w = max(1, ⌊m/4⌋), and call the starts in [b, b + w) ∩ [0, n − m] a *block*. With s = b + w − 1 and L = m − w + 1, every start i = s − δ of the block, with δ ∈ [0, w), covers the positions [s, s + L), and s + L = b + m ≤ n. An occurrence at i forces

M := x[s, s + L) = y[δ, δ + L).

So M must equal one of the *windows* y_δ = y[δ, δ + L), and the set Δ of the δ ∈ [0, w) with s − δ ∈ [0, n − m] and y_δ = M contains the shift of every occurrence in the block. Let q be the least period of M.

**Lemma 1.** If δ < δ′ are in Δ, then q divides δ′ − δ, and y has period q on [δ, δ′ + L).

*Proof.* Let d = δ′ − δ < w ≤ m/4. As y_δ = y_δ′, y has period d on [δ, δ′ + L), so M has the periods d and q. Since q + d ≤ 2d < m/2 < L, the periodicity lemma [3] makes gcd(q, d) a period of M, so it equals q, which divides d. For k ∈ [δ, δ′ + L − q) with k + q ≥ δ + L, the position k − d lies in [δ, δ + L − q), and the periods d, q, d give y_k = y_{k−d} = y_{k−d+q} = y_{k+q}. ∎

Applied to the least and the largest element of Δ, Lemma 1 shows that y has period q on [min Δ, max Δ + L). If |Δ| ≥ 2, let [ℓ, r) be the largest interval containing [min Δ, max Δ + L) on which y has period q. It is unique, since two such intervals share an interval of length L ≥ q, so their union also has period q. Call j a *break* of the text if x_j ≠ x_{j+q}. Let λ be the largest break in [s − m, s), and ρ the least j ∈ [s + L, min(n, s + L + m)) with x_j ≠ x_{j−q}, if they exist.

**Lemma 2.** Let |Δ| ≥ 2 and i = s − δ with δ ∈ Δ.
1. If ℓ > 0 and y occurs at i, then λ = i + ℓ − 1.
2. If r < m and y occurs at i, then ρ = i + r.
3. If ℓ = 0 and r = m, then y occurs at i iff no break lies in [i, s) and no ρ lies in [s + L, i + m).

*Proof.* An occurrence at i copies the period of y on [ℓ, r) to x on [i + ℓ, i + r), so no j ∈ [i + ℓ, i + r − q) is a break. If ℓ > 0, then y_{ℓ−1} ≠ y_{ℓ−1+q}, so i + ℓ − 1 is a break. As ℓ ≤ δ, it lies in [s − w, s) ⊆ [s − m, s), and every j in (i + ℓ − 1, s) has j + q < s + L ≤ i + r, so it is not a break. This gives (1), and (2) is symmetric. In case (3), y has period q. If x has period q on [i, i + m) and agrees with y on [s, s + L), which has length L ≥ q, then x agrees with y on all of [i, i + m). The converse is clear. ∎

## 2. The algorithm

**Theorem 1.** For every known pattern y ∈ Σ^m and n ≥ m, it can be decided with O(√n) quantum queries and bounded error whether y occurs in a text x ∈ Σ^n. Within the same bound an occurrence is found.

*Proof.* Fix a block. Its decision B_b uses a constant number of steps, each with O(√m) queries and an error amplified to a small constant by a constant number of repetitions.

1. *Identify M.* The distinct windows y_δ, δ ∈ [0, w), are at most w strings of L characters. Written in binary they form a set of at most w strings of N ≥ L > w bits, and for at most N strings the unknown one is identified with O(√w) queries [4, Proposition 2]. A bit query is answered by two character queries. Run this on M, and check the answer δ̂ by a search for a mismatch between M and y_δ̂ with O(√m) queries [5]. If it fails, Δ is empty and B_b = 0. Otherwise M = y_δ̂ is known, so Δ and q follow with no queries.
2. *One window.* If Δ = {δ}, verify the start s − δ by a search for a mismatch with O(√m) queries.
3. *Several windows.* Otherwise compute λ or ρ by a search for the largest or least position in a range of m positions, a maximum or minimum finding over tests of two queries each, with O(√m) queries [6]. If ℓ > 0, Lemma 2(1) leaves the single start i = λ − ℓ + 1, kept only if s − i ∈ Δ, and it is verified as in step 2. The case r < m is symmetric. If ℓ = 0 and r = m, compute both λ and ρ. By Lemma 2(3), the block contains an occurrence iff some δ ∈ Δ has λ < s − δ and s − δ + m ≤ ρ, with λ = −∞ or ρ = ∞ when there is none. This needs no further queries.

So B_b is computed with O(√m) queries and bounded error. The blocks start at the multiples b of w up to n − m, so there are K = ⌊(n − m)/w⌋ + 1 of them, and K ≤ 7(n − m)/m + 1 since w ≥ m/7 for m ≥ 4 and w = 1 for m < 4. Search with a bounded-error test [7] over the K blocks, with test B_b, finds a block with B_b = 1, if there is one, with O(√K) calls of B_b. Its occurrence then follows from step 2 or 3. In total this is O(√(Km)) = O(√(7(n − m) + m)) = O(√n) queries. ∎

## 3. Lower bound

**Proposition 2.** For 1 ≤ m ≤ n and the pattern c^m, with a second character d, deciding whether the pattern occurs needs Ω(√n) quantum queries.

*Proof.* Take a = ⌊(n + 1)/(m + 1)⌋ blocks of m positions, separated by single characters d, and d in all remaining positions. Every run of m consecutive characters c lies in one block, so c^m occurs iff some block is all c. This is OR over a blocks of AND over m characters, which needs Ω(√(am)) queries [8]. As (n + 1)/(m + 1) ≥ 1, a ≥ (n + 1)/(2(m + 1)), so am ≥ (n + 1)/4. ∎

## Lean

`lean/KnownPattern/Basic.lean`, with strings as maps ℕ → α and `HasPeriod f a b q` for "f_k = f_{k+q} whenever a ≤ k and k + q < b":

- `period_gcd`: periods p and q of an interval of length at least p + q give the period gcd(p, q). This is the form of the periodicity lemma [3] that Lemma 1 uses, proved here.
- `windows_period`: Lemma 1.
- `left_break`, `run_copied`: an occurrence copies the breaks and the periodic runs of y to the text, the facts behind Lemma 2(1) and (2).
- `periodic_occ`: Lemma 2(3).
- `occ_of_parts` (in `lean/KnownPattern/Dict.lean`): if the text and the pattern have period q on overlapping runs, agree on a window of length at least q, and agree outside the run, then the pattern occurs. This is the converse direction of Lemma 1 of [known-dictionary-matching-queries](../known-dictionary-matching-queries/).

`lean/KnownPattern/Axioms.lean` prints the axioms of these theorems. The output, in `lean/axioms.txt` from a build of a clean copy of this folder, shows no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

**Not formalized:** the oracle identification [4], the searches [5, 6, 7], the lower bound for composed functions [8], and the query counts of Theorem 1.

## Scripts

`sim/check_blocks.py` checks Lemmas 1 and 2 and the resulting block decision against brute force on about 950 000 blocks over alphabets of size 2 and 3. The inputs are random patterns and texts, periodic and nearly periodic patterns, patterns with a periodic run broken at one or both ends, and texts with long periodic runs and planted occurrences. It runs in a few seconds with Python 3 and no extra packages.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check scripts, and to draft the text.

## References

1. A. Cornelissen. Quantum algorithms through graph composition. arXiv:2504.02115, Theorems 6.2 and 6.3.
2. Q. Wang, M. Ying. Quantum algorithm for lexicographically minimal string rotation. arXiv:2012.09376.
3. N. J. Fine, H. S. Wilf. Uniqueness theorems for periodic functions. Proc. Amer. Math. Soc. 16, 1965.
4. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
5. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
6. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
7. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
8. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
