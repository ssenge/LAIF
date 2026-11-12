# Matching a known pattern with wildcards, with quantum queries

Written 12 Nov 2026.

**Setting.** A pattern P ∈ (Σ ∪ {?})^m over a finite alphabet Σ is known in advance. It has k < m wildcards `?` and f = m − k ≥ 1 fixed letters, and ℓ is the length of its longest run of consecutive fixed letters. The text x ∈ Σ^n, with n ≥ m, is given by queries: a query returns one character x_j. P occurs at the start t ∈ [0, n − m] if x_{t+i} = P_i for every fixed position i. The task is to decide whether P occurs in x.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Does a known pattern with k wildcards occur in the text? | O(√((n − m + 1) f)) by a search over the starts with a search for a mismatch at each [2, 4]; Õ(√(nk)) for k ≥ 1, implied by [8] (deciding pattern matching with k mismatches) after replacing every wildcard of P by a letter that is not in Σ | O(√((k + 1) m (1 + (n − m)/ℓ))) for every pattern over every finite alphabet, with no logarithmic factors. This is O(√(n (k + 1))) when ℓ ≥ m/c for a constant c, and O((k + 1) √n) for every pattern with m ≥ 2k. An occurrence is found within the same bound | Claim; checked by script; the candidate lemmas in Lean |
| Cor 2 | Constant number of wildcards | Õ(√n), implied by [8] | Θ(√n) for every constant k, in the worst case over patterns with k wildcards | Claim |

For k = 0 Theorem 1 is the Θ(√n) bound of [1]. With the letter that is not in Σ, a start is an occurrence of P iff the copy of P there has at most k mismatches, so [8] decides the problem with Õ(√(nk)) queries, also when the pattern is given by queries. Theorem 1 removes the logarithmic factors of this bound for patterns with a constant number of wildcards, and for patterns with a run of fixed letters of length Ω(m). For patterns made of many short runs, the bound of [8] is smaller.

When wildcards may also occur in the text, a quantum algorithm with time Õ(√(n max(k, √n))) is given in [5], where k counts the wildcards of both strings.

## 1. The block decision

Let R = P[o, o + ℓ) be a longest run of fixed letters. Let w = max(1, ⌊ℓ/4⌋), and call the starts in [b, b + w) ∩ [0, n − m] a *block*. With s = b + o + w − 1 and L = ℓ − w + 1, the copy of R at every start of the block covers the *middle* M = x[s, s + L). If P occurs at t in the block, then R occurs at t + o, so M = R[δ, δ + L) with δ = s − t − o ∈ [0, w).

Once M is known, let q be its least period and W the word of period q that equals M on [s, s + L), that is, W(j) = M_{(j − s) mod q}. Let λ be the largest j ∈ [b, s) with x_j ≠ W(j), and ρ the least j ∈ [s + L, h) with x_j ≠ W(j), where h = min(n, b + w − 1 + m); if there is none, λ = b − 1 or ρ = h. So x = W on the *region* (λ, ρ), and every position that a start of the block reads lies in [b, h).

Call a start t *consistent* if every fixed letter P_i with t + i in the region equals W(t + i). This needs no queries. P occurs at t iff t is consistent and every fixed letter P_i with t + i outside the region matches the text (`occ_iff_outside`). A consistent t is *left-exposed* if t ≤ λ and *right-exposed* if t + m − 1 ≥ ρ. A consistent start that is not exposed is an occurrence, with no further queries.

**Lemma 1.** All consistent starts of a block are congruent modulo q.

*Proof.* A consistent t puts R[δ, δ + L) on [s, s + L), which lies in the region, so R[δ, δ + L) = M with δ = s − t − o. For two consistent starts the windows δ ≤ δ' satisfy 2(δ' − δ) < 2w ≤ L, since ℓ ≥ 4w when w ≥ 2 (for w = 1 there is one window). Then δ' − δ is a period of M, so q ≤ δ' − δ, and by the periodicity lemma [3] gcd(q, δ' − δ) is a period of M, so q divides δ' − δ (`same_class`). ∎

**Lemma 2.** Call a left-exposed consistent start t *admissible* if P_{λ−t} is a wildcard or a fixed letter different from W(λ), and a right-exposed one admissible if the same holds for P_{ρ−t} and W(ρ). Every exposed start with an occurrence is admissible on each side where it is exposed, and at most k + 1 left-exposed and at most k + 1 right-exposed starts are admissible.

*Proof.* If P occurs at a left-exposed t, then λ − t ∈ [0, m), since λ < s ≤ t + m − 1, and P_{λ−t} matches x_λ ≠ W(λ), so t is admissible. Let t < t' be two admissible left-exposed starts with fixed letters at λ − t and λ − t'. By Lemma 1, q divides t' − t, and λ + (t' − t) < s + w ≤ ρ. So the position λ − t of P falls on λ + (t' − t) in the region for the start t', and consistency of t' gives P_{λ−t} = W(λ + (t' − t)) = W(λ), a contradiction (`left_fixed_unique`). So at most one admissible start has a fixed letter at λ − t, and the others have distinct wildcard positions λ − t (`left_exposed_card`). The right side is symmetric. ∎

## 2. The algorithm

**Theorem 1.** For every known pattern P of length m with k < m wildcards and a longest run ℓ of fixed letters, over every finite alphabet, and every n ≥ m, it can be decided with O(√((k + 1) m (1 + (n − m)/ℓ))) quantum queries and bounded error whether P occurs in a text x ∈ Σ^n. Within the same bound an occurrence is found.

*Proof.* Fix a block. Its decision uses four steps, each with error amplified to at most 1/40 by a constant number of repetitions.

1. *Identify M.* The windows R[δ, δ + L), δ < w, are at most w strings of L characters. Written in binary they form at most w strings of N ≥ L ≥ w bits, and for at most N strings the unknown one is identified with O(√w) queries [6, Proposition 2]. M may be none of the windows, so run this algorithm with its query bound as a cutoff and check the answer by a search for a mismatch with O(√ℓ) queries [2]. If it fails, the block has no occurrence. Otherwise M, q and W are known.
2. *Breaks.* Compute λ and ρ by searches for the largest or least position in a range of at most m positions, with one query per test, with O(√m) queries [7].
3. *Free starts.* Compute the consistent starts and the exposed ones. If some consistent start is not exposed, accept. This needs no queries.
4. *Exposed starts.* Keep the exposed starts that are admissible on each side where they are exposed. By Lemma 2 at most 2k + 2 starts remain. Search among them, with a bounded-error test [4], for a start whose fixed letters outside the region all match. A test is a search for a mismatch among at most m positions, with O(√m) queries [2]. This takes O(√((k + 1) m)) queries.

So the block is decided with O(√((k + 1) m)) queries and error at most 1/10. There are K = ⌊(n − m)/w⌋ + 1 blocks, and w ≥ ℓ/7, so K ≤ 7(n − m)/ℓ + 1. Search with a bounded-error test [4] over the blocks finds a block with an occurrence, if there is one, with O(√K) block decisions, so with O(√(K (k + 1) m)) queries. Step 4 then gives the occurrence. ∎

The m − k fixed letters form at most k + 1 runs, so ℓ ≥ (m − k)/(k + 1). For m ≥ 2k this gives ℓ ≥ m/(2(k + 1)) and the bound O((k + 1) √n).

**Corollary 2.** For every constant k, a known pattern with k wildcards is matched with O(√n) quantum queries. This is optimal in the worst case over patterns with k wildcards: for the pattern c^{m−k} followed by k wildcards, an occurrence is an occurrence of c^{m−k} that starts in [0, n − m], so Proposition 2 of [1], on the text x[0, n − k), gives Ω(√(n − k)).

*Proof.* For m ≥ 2k, Theorem 1 gives O((k + 1) √n). For m < 2k, f < k, and the search over the starts gives O(√(nf)) = O(√(nk)). ∎

## Scripts

`sim/check_wild.py` checks the block decision against brute force. The decision uses M, λ and ρ, decides the consistent starts that are not exposed with no further access to the text, and reads the text only at the fixed positions of the exposed starts outside the region. The script asserts Lemma 1, the bound of Lemma 2 and the result on every block. It covers 40 000 random patterns of length up to 22 with up to 5 wildcards, over 2 and 3 letters, half of them periodic with changes, and texts with long periodic runs and planted occurrences: about 627 000 blocks, of which about 107 000 contain an occurrence. A second part covers 6000 long periodic patterns of length up to 48 with up to m/2 wildcards on texts that are periodic up to a few changes, about 131 000 blocks. A third part takes the patterns ?^k 0^ℓ, 0^ℓ ?^k, ?^k 0^ℓ ?^k, 1 ?^k 0^ℓ ?^k 1 and ?^k (01)^{ℓ/2}, with up to 8 wildcards, on periodic texts with changes, where k starts are admissible on one side, about 38 000 blocks. Wildcards are placed at every position, including the first and the last. It runs in a few seconds with Python 3 and no extra packages.

## Lean

`lean/KnownPattern/Wild.lean` of [known-pattern-matching-queries](../known-pattern-matching-queries/), with only the standard axioms:

- `same_class`: two windows of the run that both equal M are at a distance that the least period q of M divides (Lemma 1).
- `left_fixed_unique` and `left_exposed_card`: at most k + 1 consistent starts of one class modulo q reach the break λ with a wildcard or a fixed letter different from W(λ) there (Lemma 2, left side).
- `occ_iff_outside`: if the text equals W on the region, an occurrence is a consistent start whose fixed letters outside the region match.

The module uses `period_gcd` of `lean/KnownPattern/Basic.lean` there.

**Not formalized:** the right side of Lemma 2 (the mirror image of the left side), the step from consistency to the equality of the window with M in Lemma 1, the side conditions 2(δ' − δ) ≤ L and λ + (t' − t) < ρ, which follow from ℓ ≥ 4w, the step from the definitions of λ and ρ to x = W on the region, the oracle identification [6], the searches [2, 4, 7], and the query counts.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts and the Lean files, and to draft the text.

## References

1. [known-pattern-matching-queries](../known-pattern-matching-queries/): pattern matching with a known pattern in Θ(√n) quantum queries, Theorem 1 and Proposition 2.
2. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
3. N. J. Fine, H. S. Wilf. Uniqueness theorems for periodic functions. Proc. Amer. Math. Soc. 16, 1965.
4. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
5. M. Seddighin, S. Seddighin. Quantum pattern matching with wildcards. arXiv:2507.13885.
6. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
7. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
8. T. Kociumaka, J. Nogler, P. Wellnitz. Near-optimal-time quantum algorithms for approximate pattern matching. arXiv:2410.06808, Main Theorem 2.
