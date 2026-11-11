# Two-dimensional pattern matching with quantum queries

Written 11 Nov 2026.

**Setting.** The text is an array T : [n₁] × [n₂] → Σ and the pattern an array P : [m₁] × [m₂] → Σ, with m₁ ≤ n₁, m₂ ≤ n₂ and [k] = {0, …, k − 1}. A query returns one entry of T or of P. The pattern *occurs* at (r, c) if T[r + i][c + j] = P[i][j] for all (i, j) ∈ [m₁] × [m₂]. The task is to decide whether P occurs in T, and to find an occurrence. Write N = n₁n₂.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Two-dimensional pattern matching, n × n text, m × m pattern | O(nm), by search over the positions with an inner search for a mismatch [4] | O(n √m log⁴ n) | Claim; checked by script; lemmas in Lean |
| Thm 2 | Same, any n₁, n₂, m₁, m₂ | | Ω(√(n₁n₂)) for every pattern size | Claim |
| Thm 3 | Same, n × n text, m × m pattern without short periods (condition (★) of Section 6 with b ≥ m/8) | O(nm), and O(n √m log⁴ n) by Theorem 1 | O(m² + n log³ m), so O(n log³ n) for m ≤ √n | Claim; checked by script; lemmas in Lean |

In one dimension the problem takes Õ(√n + √m) queries [1], by deterministic sampling [2]. In two dimensions, quantum algorithms that are fast on average are given in [3]; to our knowledge, no worst-case bound below O(nm) was known for an n × n text and an m × m pattern. Classically, Θ(n²) queries are needed in the worst case, by the same family as in Theorem 2.

## 1. Strips and column strings

Fix a row offset r ∈ [n₁ − m₁ + 1]. The *strip* of r is the string S_r of length n₂ whose j-th character is the column segment (T[r][j], …, T[r + m₁ − 1][j]). The pattern becomes the string p of length m₂ whose j-th character is column j of P. The pattern occurs at (r, c) iff p occurs in S_r at c. Two characters are compared by a search for a differing entry, with O(√m₁ log N) queries and error at most N⁻⁵.

Sections 2 to 4 work with one string S of length n over an arbitrary alphabet, a pattern p of length m ≤ n, and character comparisons as the unit of cost. A *period* of p is a d ≥ 1 with p[y] = p[y + d] for all y < m − d, and L denotes the smallest one.

**Lemma 1.** (a) Two occurrences of p in S lie at least L apart. (b) If a segment of S is L-periodic, the starts x in it with S[x, x + L) = p[0, L) form at most one residue class modulo L.

*Proof.* (a) Occurrences at x < x′ with x′ − x < L ≤ m overlap, so x′ − x is a period of p, contradicting the choice of L. (b) In an L-periodic segment, the window of length L at x is the window at x′ rotated by (x − x′) mod L. If both equal u = p[0, L) and t = (x − x′) mod L ≠ 0, then the infinite word uuu… has the periods t and L, hence the period gcd(t, L) < L. Since p is a prefix of this word, gcd(t, L) is a period of p, a contradiction. ∎

## 2. Deterministic sample

Place L copies of p at the shifts 0, …, L − 1: copy j holds p[z − j] at position z ∈ [j, j + m). A *sample* is a list of positions z₁, …, z_k with values c₁, …, c_k and a *survivor* f ∈ [L] such that copy f has value c_t at z_t for every t, and every copy j ≠ f has a position z_t in [j, j + m) where its value differs from c_t.

**Lemma 2.** A sample with k ≤ 8⌈log₂ N⌉ positions can be computed with O(√(m₁m₂) log⁴ N) queries, with error O(N⁻¹), in the setting of Section 1.

*Proof.* This is the construction of [2] in the quantum form of [1]. Keep the set of surviving copies, initially all. In a stage, let l and r be the leftmost and rightmost survivors, found by minimum finding [5] with an oracle that checks the copies against the values chosen so far. Since 0 < r − l < L, the shift r − l is not a period, so the copies l and r differ at a position z ∈ [r, l + m), found by a search over the m₁ · m entries of the overlap. Every survivor j ∈ [l, r] covers z. Choose one of the two values of copies l and r at z uniformly at random and keep the survivors with this value. Every stage removes at least one copy, and with probability at least 1/2 it keeps at most half of them, since the two classes are disjoint. So after 8⌈log₂ N⌉ stages one copy is left, except with probability O(N⁻¹). The sample property holds because a copy removed in stage t is defined at z_t and differs from c_t there. Every search and minimum finding of a stage is run at error N⁻², so a stage costs O(√L log² N) comparisons plus O(√(m₁m₂) log N) queries. ∎

Say that a start x *passes* if S[x − f + z_t] = c_t for every t, that is, if S agrees with copy f placed at x − f on the sample. Every occurrence passes. If x passes, no start in [x − f, x − f + L) other than x is an occurrence: such a start x − f + j, with j ≠ f, would need value p[z_t − j] ≠ c_t at the position x − f + z_t, where S has c_t.

## 3. Candidates in a block of L starts

**Lemma 3.** Let I be an interval of at most L starts. If 2f ≥ L, let x₁ be the rightmost passing start in I and x₂ the rightmost passing start in I below x₁ − f. If 2f < L, let x₁ be the leftmost passing start in I and x₂ the leftmost passing start in I from x₁ − f + L on. Every occurrence in I is x₁ or x₂.

*Proof.* Take 2f ≥ L. Starts in I above x₁ do not pass, so they are not occurrences, and since x₁ passes, the starts of [x₁ − f, x₁) are not occurrences either. So every occurrence other than x₁ lies below x₁ − f. If there is no x₂, no start of I below x₁ − f passes. Otherwise the same argument for x₂ leaves only starts below x₂ − f ≤ x₁ − 2f − 1 ≤ x₁ − L − 1. These lie outside I, because I has at most L starts and contains x₁. The case 2f < L is symmetric: starts of I below x₁ do not pass, x₁ excludes the starts of (x₁, x₁ − f + L), and x₂ excludes those of (x₂, x₂ − f + L). What remains starts at or above x₂ − f + L ≥ x₁ + 2(L − f) ≥ x₁ + L + 1, outside I. ∎

So the occurrences in I are found with two minimum findings over at most L starts, each pass test costing k comparisons, and two checks of single starts.

## 4. Blocks of starts

If 2L > m, the starts are split into blocks of L, and Lemma 3 applies to each block.

If 2L ≤ m, the starts are split into blocks [B, B + K) with K = m − L ≥ m/2. Let c* = B + m − 1 and let D(j) say that S[j] ≠ S[j − L].

**Lemma 4.** Let g be the largest j ∈ [B + L, c*] with D(j), or B + L − 1 if there is none, and let h be the least j ∈ (c*, h₀) with D(j), or h₀ if there is none, where h₀ = min(B + K − 1 + m, n). Let X be the set of starts x ∈ [B, B + K) with x > g − L and x + m ≤ h. Then every occurrence in the block lies in X, and the occurrences in X form one residue class modulo L within X, or none.

*Proof.* An occurrence x in the block has D(j) false for j ∈ [x + L, x + m), and this range contains c*, since x + L ≤ B + K − 1 + L = c* and c* < B + m ≤ x + m. So g < x + L and h ≥ x + m, and x ∈ X. Conversely the segment S[g − L + 1, h) is L-periodic, and it contains [x, x + m) for every x ∈ X. For such x, S[x, x + m) is L-periodic, and so is p; both are determined by their first L characters, so x is an occurrence iff S[x, x + L) = p[0, L). By Lemma 1(b) these x form at most one residue class modulo L, and since the window of length L at x ∈ X depends only on x mod L, every member of X in that class is an occurrence. ∎

So the block needs a maximum and a minimum finding for g and h, then Lemma 3 on the first min(L, |X|) starts of X, which contain a member of the residue class if there is one, and a check of at most two starts.

## 5. Results

**Theorem 1.** Two-dimensional pattern matching takes O(√(n₁n₂m₁) log⁴ N + m₂√m₁ log N) quantum queries, and O(n √m log⁴ n) for an n × n text and an m × m pattern. With rows and columns exchanged, m₁ may be replaced by m₂.

*Proof.* The pattern work is done once: the smallest period L of the column string, by minimum finding over d ∈ [1, m₂] with a search for a violated column pair, O(m₂√m₁ log N) queries, and the sample of Lemma 2. In units of queries, a comparison costs O(√m₁ log N) and a pass test O(√m₁ log² N). A block (Sections 3 and 4) uses a constant number of minimum findings over O(m₂) positions with these tests, plus checks of single starts by a search for a mismatch over m₁m₂ entries, each run at error N⁻⁶ with O(√(m₁m₂) log N) queries, so O(√(m₁m₂) log² N) queries with constant error, and O(√(m₁m₂) log³ N) with error N⁻⁵ after O(log N) repetitions. A block reports an occurrence only after a check, so these repetitions only reduce the chance of missing one. Blocks have at least m₂/2 starts, so a strip has at most 2n₂/m₂ + 1 blocks, and a search over them costs O(√(n₂m₁) log³ N), or O(√(n₂m₁) log⁴ N) with error N⁻⁵. A search over the n₁ − m₁ + 1 strips gives the bound. All inner procedures have bounded cost on every run and are run coherently; each call with error at most N⁻⁵ moves the state by O(N^{−5/2}) in norm, and there are fewer than N² calls in total. For n₁ = n₂ = n and m₁ = m₂ = m, the term m^{1.5} log n is at most n √m log n. ∎

**Theorem 2.** For every m₁ ≤ n₁, m₂ ≤ n₂ and |Σ| ≥ 2, the problem needs Ω(√(n₁n₂)) quantum queries.

*Proof.* Let P be all 0. Fill T with 1, and place a ⌊(n₁ + 1)/(m₁ + 1)⌋ × ⌊(n₂ + 1)/(m₂ + 1)⌋ grid of m₁ × m₂ blocks, separated by single rows and columns of 1. The entries of the blocks are arbitrary. The pattern occurs iff some block is all 0, since every m₁ × m₂ subarray that is not a block meets a separating or leftover row or column of 1. This is the OR of a ≥ n₁n₂/(4m₁m₂) ANDs of m₁m₂ bits each, whose quantum query complexity is Θ(√(a m₁m₂)) [6], so Ω(√(n₁n₂)). ∎

So the gap for an n × n text and an m × m pattern is now Ω(n) against O(n √m log⁴ n).

## 6. Patterns without short periods

Here the text is n × n and the pattern m × m. Copy s of the pattern holds P[z − s] at the cells z ∈ s + [m]². For b ≥ 2, all copies with shifts in F = [0, b)² cover the region C = [b − 1, m)².

**Condition (★).** The copies with shifts in F are pairwise distinct on C.

Condition (★) holds, for instance, if the central square of P on [b − 1, m − b + 1)² has no period δ with 0 < |δ|∞ < b. Two copies s and s′ = s + δ in F then differ at z = u + s′ ∈ C for a cell u of the square with P[u] ≠ P[u + δ]. Condition (★) implies that no δ with 0 < |δ|∞ < b is a period of P, so two occurrences are never closer than b in both coordinates, and for each such δ there is a *witness*, a cell u with P[u] ≠ P[u − δ] and both cells inside the pattern. When the pattern has been read, the sample below and all witnesses are known without further queries.

**Lemma 5.** Under (★) there is a sample of k ≤ 2⌈log₂ b⌉ cells z_t ∈ C with values c_t and a survivor f ∈ F such that copy f has value c_t at z_t for all t, and every copy j ∈ F other than f has a value different from c_t at some z_t.

*Proof.* As in Lemma 2. While two copies survive, take two of them, a cell of C where they differ, and keep the smallest nonempty class of survivors by their value there. This class has at most half of the survivors, and every survivor covers the cell. ∎

A start x *passes* if T[x − f + z_t] = c_t for all t; these k cells lie in the area of x. Every occurrence passes. For each coordinate i, let σᵢ = 1 if fᵢ ≥ b − 1 − fᵢ and σᵢ = −1 otherwise, and let b′ = ⌊b/2⌋.

**Lemma 6.** Let p ≠ x be passing starts with |pᵢ − xᵢ| < b′ and σᵢ(pᵢ − xᵢ) ≥ 0 for both i. Then x is not an occurrence.

*Proof.* Let j = x − p + f. If σᵢ = 1, then xᵢ − pᵢ ∈ (−b′, 0] and fᵢ ≥ (b − 1)/2 ≥ b′ − 1, so jᵢ ∈ [0, b). If σᵢ = −1, then xᵢ − pᵢ ∈ [0, b′) and fᵢ < (b − 1)/2, so again jᵢ ∈ [0, b). So j ∈ F and j ≠ f, and copy j has a value different from c_t at some z_t. The cell p − f + z_t = x + (z_t − j) holds c_t because p passes, while an occurrence at x needs the value P[z_t − j] of copy j there. ∎

**Theorem 3.** Under (★), two-dimensional pattern matching takes O(m² + n log³ m + nm/b) quantum queries. In particular, if (★) holds with b ≥ m/8, it takes O(m² + n log³ m), and O(n log³ n) for m ≤ √n.

*Proof.* Read the pattern with m² queries; compute the sample of Lemma 5 and a witness for every δ with 0 < |δ|∞ < b′. Split the starts into blocks of b′ × b′. In a block, Lemma 6 says that every occurrence is a passing start that no other passing start dominates in the order given by σ. These maximal passing starts form a front, as in Lemma 3 of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/), with "passes" in place of a 1-cell. That lemma learns the front with O(b′ log² b′) tests and constant error, so with O(b log³ m) queries, on every run. The front has at most b′ starts. A tournament over them keeps one: for the current candidate x and the next start y, one query at x + u, where u is the witness for y − x, either matches P[u] (then y is not an occurrence, since copy y has the other value there) or not (then x is not an occurrence, and y becomes the candidate). This takes fewer than b′ queries. A search for a mismatch over the m² cells of the last candidate decides the block with O(m) queries. So a block costs O(b log³ m + m) queries with bounded error, and the search with bounded-error inputs [7] over the at most (n/b′ + 1)² blocks costs O((n/b)(b log³ m + m)). ∎

Theorem 3 needs the whole pattern, which costs m² queries, and condition (★). Patterns with short periods, such as a pattern of a single letter, are covered by Theorem 1, and the all-zero pattern by the largest empty square of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/).

## Lean

`lean/PatternMatch/Blocks.lean`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- Lemma 1(a): two occurrences at distance d make d a period (`period_of_occ`), so occurrences lie at least the smallest period apart (`occ_gap`).
- Lemma 1(b): an infinite word with the periods t and L has the period gcd(t, L) (`gcd_period`), and two windows of an L-periodic word that both equal the first L letters of the pattern start in the same residue class modulo L (`residue_unique`).
- Lemmas 2 and 5: copies that are pairwise distinct on a set of cells have a sample of k cells and a survivor with 2^k at most the number of copies (`sample_exists`), by keeping the smaller class.
- Sections 2 to 4: a passing start excludes the other starts of [x − f, x − f + L) (`pass_excludes`); Lemma 3 in both cases (`two_right`, `two_left`); the cell c* of Lemma 4 (`run_cell`).
- Section 6: the exclusions of a passing start in two dimensions (`pass_excludes2`), the sides used in Lemma 6 (`side_cover`), Lemma 6 (`occ_undominated`), and one duel of the tournament (`duel`).

**Not formalized:** search [4], minimum finding [5], search with bounded-error inputs [7], the lower bound for composed functions [6], the front learner (Lemma 3 of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/)), the random choice of values in Lemma 2, the step of Lemma 4 from the run to the set X, and the counting of queries and errors in Theorems 1 and 3.

## Scripts

`sim/check_strips.py` builds the period, the sample and the blocks of Sections 2 to 4 with exact searches, and checks the sample property and the occurrence sets of every block against brute force: 20000 one-dimensional instances (periodic and aperiodic patterns over 2 and 3 letters, texts with planted and noisy copies) and 1500 two-dimensional ones. It covers both block types, with and without occurrences. It checks the combinatorics with exact searches; the sample size, the query counts, the error bounds and Theorem 2 rest on the proofs above.

`sim/check_blocks2d.py` checks Section 6 against brute force: condition (★), the sample of Lemma 5 and its size, that every occurrence of a block is on the front of its passing starts (learned by the front learner of `largest-empty-rectangle-queries/sim/check_window.py`, with its cost per depth), and that the tournament and the final check return exactly the occurrences of the block. It covers 400 random and sparse patterns with random texts and planted copies, and 300 texts with passing starts planted on chains and antichains of a block, so that fronts reach the largest possible length b′.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check scripts, and to draft the text.

## References

1. H. Ramesh, V. Vinay. String matching in Õ(√n + √m) quantum time. J. Discrete Algorithms 1, 2003. arXiv:quant-ph/0011049.
2. U. Vishkin. Deterministic sampling: a new technique for fast pattern matching. SIAM J. Comput. 20, 1991.
3. A. Montanaro. Quantum pattern matching fast on average. Algorithmica, 2017. arXiv:1408.1816.
4. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
5. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
6. B. W. Reichardt. Reflections for quantum query algorithms. SODA 2011. arXiv:1005.1601.
7. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
