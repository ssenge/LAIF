# Dictionary matching with a known dictionary, with quantum queries

Written 12 Nov 2026.

**Setting.** A dictionary D of d patterns of length m over an alphabet Σ of constant size is known in advance, and the text x ∈ Σ^n, with n ≥ m, is given by queries: a query returns one character x_j. The task is to decide whether some pattern of D occurs in x.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Does a pattern of a known dictionary occur in the text? | O(min(√(dn), √(nm))): search over the patterns with the O(√n) algorithm of [1] for one pattern, or search over blocks of m starts that are read in full | O(√(n (1 + log d))), and an occurrence is found within the same bound | Claim; checked by script |
| Prop 2 | Lower bound | Ω(√n) for one pattern [1] | Ω(√(nk)) for a dictionary of d = C(m − 1, k) patterns over three letters, 1 ≤ k ≤ (m − 1)/2. So Theorem 1 is optimal up to the factor √(log(m/k)), and optimal for d = 2^{Ω(m)} and for constant d | Claim |

For a single pattern, Theorem 1 is the O(√n) bound of [1]. For d = 2^{Θ(m)} it is the bound O(√(nm)) of reading blocks, which Proposition 2 shows to be optimal there. In between, it replaces the factor √d or √m by √(log d).

## 1. The block decision

We use the blocks of [1]. Let w = max(1, ⌊m/4⌋), and call the starts in [b, b + w) ∩ [0, n − m] a *block*. With s = b + w − 1 and L = m − w + 1, every start of the block covers the *common part* M = x[s, s + L). Let q be the least period of M. For a pattern y ∈ D, let Δ_y be the set of δ ∈ [0, w) such that s − δ is a start and y[δ, δ + L) = M. If Δ_y is not empty, y has period q on [min Δ_y, max Δ_y + L): by Lemma 1 of [1] if |Δ_y| ≥ 2, and since the window equals M if |Δ_y| = 1. Let [ℓ_y, r_y) be the largest interval containing it on which y has period q.

Call j a *break* if x_j ≠ x_{j+q}. Let λ be the largest break in [s − m, s), and ρ the least j ∈ [s + L, min(n, s + L + m)) with x_j ≠ x_{j−q}, if they exist; otherwise λ = −∞ and ρ = ∞. These are the same for all patterns.

**Lemma 1.** Let y ∈ D, δ ∈ Δ_y and t = s − δ, and write ℓ = ℓ_y, r = r_y. Then y occurs at t iff

1. either ℓ > 0, λ = t + ℓ − 1 and x[t, t + ℓ) = y[0, ℓ), or ℓ = 0 and λ < t, and
2. either r < m, ρ = t + r and x[t + r, t + m) = y[r, m), or r = m and t + m ≤ ρ.

*Proof.* If y occurs at t, the conditions on λ and ρ are Lemma 2 of [1], whose proof uses only that y has period q on [ℓ, r) ⊇ [δ, δ + L). Conversely, x has no break in (λ, s) and agrees with M on [s, s + L), and x_j = x_{j−q} for j ∈ [s + L, ρ). So x has period q on [λ + 1, ρ). By (1) and (2), [t + ℓ, t + r) ⊆ [λ + 1, ρ). On this interval x and the copy of y at t both have period q, and they agree on [s, s + L), which has length L ≥ q. So they agree on all of it. The parts [t, t + ℓ) and [t + r, t + m) agree by (1) and (2). ∎

The parts in (1) and (2) are anchored: every *left part* y[0, ℓ_y) with ℓ_y > 0 has to end at position λ, and every *right part* y[r_y, m) with r_y < m has to start at position ρ. Let α* be the longest left part that ends x at λ, that is, equals x[λ − ℓ_y + 1, λ + 1), and β* the longest right part that equals x[ρ, ρ + m − r_y). A left part ends x at λ iff it is a suffix of α*, since both are suffixes of x[0, λ + 1). The same holds for right parts and β*. So once M, λ, ρ, α* and β* are known, Lemma 1 decides every start of the block with no further queries.

## 2. Longest match in a trie

**Lemma 2.** Let Z be a set of k ≥ 1 strings of length at most h, and let u ∈ Σ^h be given by queries. The largest π such that u[0, π) is a prefix of a string of Z, together with u[0, π), can be computed with O(√(h (1 + log k))) quantum queries and bounded error.

*Proof.* Let T be the trie of Z, and let the weight of a node be the number of strings of Z in its subtree. From a node v, the *heavy path* follows the child of largest weight until it reaches a node without children, and its label is a string z ∈ Z. Start at the root. In a round at a node v of depth p₀, search for the first position p ≥ p₀ with u_p ≠ z_p, for p < |z|. If there is none, π = |z|. Otherwise query u_p. If the node z[0, p) of the heavy path has a child for the letter u_p, continue from that child; otherwise π = p. A child that is not on the heavy path has at most half the weight of its parent, so there are at most log₂ k + 1 rounds. The searched intervals [p₀, p] of the rounds are disjoint, so their lengths g_i sum to at most h + log₂ k + 1. The search for the first difference in a round costs O(√g_i) [2, Theorem 6], and composed in sequence with the costs depending on the input [2, Theorems 4 and 5] the rounds take O(Σ √g_i) queries on every input, with bounded error and no factor for error reduction. By the Cauchy-Schwarz inequality, Σ √g_i ≤ √((log₂ k + 1)(h + log₂ k + 1)) = O(√(h (1 + log k))), since log k = O(h) for strings over a constant-size alphabet. ∎

This is the halving algorithm of [2, Algorithm 2] on a trie. The longest string of Z that is a prefix of u is then the longest string of Z that is a prefix of u[0, π), with no further queries. For the left parts, Lemma 2 runs on the reversed parts and the reversed text x[λ − m + 1, λ + 1), clipped at 0, and for the right parts on x[ρ, ρ + m), clipped at n.

## 3. The algorithm

**Theorem 1.** For every known dictionary D of d patterns of length m over an alphabet of constant size σ ≥ 2 and every n ≥ m, it can be decided with O(√(n (1 + log d))) quantum queries and bounded error whether a pattern of D occurs in a text x ∈ Σ^n. Within the same bound an occurrence is found.

*Proof.* Fix a block. Its decision uses five steps, each with error amplified to at most 1/20 by a constant number of repetitions.

1. *Identify M.* The windows y[δ, δ + L) with y ∈ D and δ < w are at most d' = dw distinct strings of N = L⌈log₂ σ⌉ bits, with the letters written in binary, so that a bit query is answered by two queries to the text. If d' ≤ N, M is identified with O(√d') = O(√m) queries [2, Proposition 2]. Otherwise [2, Theorem 2] gives O(√(N log d' / (log(N/log d') + 1))) queries. If log d ≥ log w, this is O(√(m log d)). If log d < log w, then log d' < 2 log m, and the bound is O(√(m log m / log(m/log m))) = O(√m). Check the answer by a search for a mismatch with O(√m) queries [3]; if the check fails, the block has no occurrence. Otherwise M, q, the sets Δ_y and the runs [ℓ_y, r_y) are known.
2. *Breaks.* Compute λ and ρ by searches for the largest or least position in a range of m positions, with tests of two queries each, with O(√m) queries [4].
3. *Left parts.* Compute α* by Lemma 2 on the at most d left parts, with h = m, with O(√(m (1 + log d))) queries.
4. *Right parts.* Compute β* in the same way.
5. *Decide.* By Lemma 1 and the remark after it, decide whether some y ∈ D and δ ∈ Δ_y give an occurrence. This needs no queries.

So the block is decided with O(√(m (1 + log d))) queries and error at most 1/4. There are K = ⌊(n − m)/w⌋ + 1 ≤ 7(n − m)/m + 1 blocks, as in [1]. Search with a bounded-error test [5] over the blocks finds a block with an occurrence, if there is one, with O(√K) block decisions, so with O(√(Km (1 + log d))) = O(√(n (1 + log d))) queries. Its occurrence then follows from Lemma 1. ∎

## 4. Lower bound

**Proposition 2.** Let 1 ≤ k ≤ (m − 1)/2 and m ≤ n, and let D_k be the set of strings 1u with u ∈ {0, 2}^{m−1} that have exactly k letters 2. Deciding whether a pattern of D_k occurs in a text of length n needs Ω(√(nk)) quantum queries. Here d = C(m − 1, k), so k ≥ log₂ d / log₂(e(m − 1)/k).

*Proof.* Take a = ⌊n/m⌋ blocks of the form 1u_j with u_j ∈ {0, 2}^{m−1}, and 0 in the remaining positions. Every window that starts with 1 starts a block and equals it, and every pattern of D_k starts with 1. So a pattern occurs iff some u_j has exactly k letters 2: the OR of a copies of the function EXACT_k on m − 1 bits. EXACT_k on N bits has adversary bound Ω(√((k + 1)(N − k))), by the relation between inputs of weight k and k + 1 [6]. The adversary bound of OR_a is √a, and the adversary bound of a composed function is the product [7]. So Ω(√(a (k + 1)(m − 1 − k))) = Ω(√(nk)) queries are needed. ∎

For k = Θ(m), d = 2^{Θ(m)} and Theorem 1 gives O(√(nm)), which is optimal. For constant d both bounds are Θ(√n). For k between, the bounds differ by the factor √(log(m/k)).

## Scripts

`sim/check_dict.py` checks Lemma 1 and the block decision of Theorem 1 against brute force. The decision uses only M, λ, ρ, the longest left part α* and the longest right part β*, and is compared with the occurrences of the dictionary in each block. It covers 20 000 random dictionaries of up to 8 patterns of length up to 16 over 2 and 3 letters, many of them built from one periodic run with changes at the ends, and texts with long periodic runs and planted patterns: about 185 000 blocks, of which about 5700 have several patterns with windows, 7300 a left part, 5800 a right part and 45 000 a periodic pattern. It runs in about a second with Python 3 and no extra packages.

**Not formalized:** Lemma 1, the remark on α* and β*, the oracle identification [2], the searches [3, 4, 5], Lemma 2, the lower bounds [6, 7], and the query counts.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. [known-pattern-matching-queries](../known-pattern-matching-queries/): pattern matching with a known pattern in Θ(√n) quantum queries, Theorem 1 and Lemmas 1 and 2.
2. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
3. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
4. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
5. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
6. A. Ambainis. Quantum lower bounds by quantum arguments. J. Comput. Syst. Sci. 64, 2002. arXiv:quant-ph/0002066.
7. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
