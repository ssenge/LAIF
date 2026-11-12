# Two-dimensional pattern matching with quantum queries

Written 11 Nov 2026.

**Setting.** The text is an array T : [n₁] × [n₂] → Σ and the pattern an array P : [m₁] × [m₂] → Σ, with m₁ ≤ n₁, m₂ ≤ n₂ and [k] = {0, …, k − 1}. A query returns one entry of T or of P. The pattern *occurs* at (r, c) if T[r + i][c + j] = P[i][j] for all (i, j) ∈ [m₁] × [m₂]. The task is to decide whether P occurs in T, and to find an occurrence. Write N = n₁n₂.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Two-dimensional pattern matching, n × n text, m × m pattern | O(nm), by search over the positions with an inner search for a mismatch [4]; Õ(n √m), implied by [1] with rows as letters [9, 10] | O(n √m log⁴ n) | Claim; checked by script; lemmas in Lean |
| Thm 2 | Same, any n₁, n₂, m₁, m₂ | | Ω(√(n₁n₂)) for every pattern size | Claim |
| Thm 3 | Same, n × n text, m × m pattern without short periods (condition (★) of Section 6 with b ≥ m/8) | O(nm), and O(n √m log⁴ n) by Theorem 1 | O(m² + n log³ m), so O(n log³ n) for m ≤ √n | Claim; checked by script; lemmas in Lean |
| Thm 4 | Same, n × n text, m × m pattern periodic along a lattice that covers side ⌊m/2⌋ (condition (L) of Section 7) | O(nm), and O(n √m log⁴ n) by Theorem 1; O(n log² n) for constant patterns, by the largest empty square of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/) | O(m² + n log² m), so O(n log² n) for m ≤ √n; Ω(n) by Theorem 2 | Claim; checked by script; lemmas in Lean |
| Thm 5 | Same, n × n text, m × m pattern with condition (★) of Section 6 for some b ≤ (m + 1)/2 | O(nm) [4]; O(m² + n log³ m + nm/b) by Theorem 3 | O(m² + nm/b), so O(m² + n) for b ≥ m/8; O(nm/b) and O(n) if the pattern is known in advance | Claim; checked by script; uniqueness of the candidate in Lean |
| Prop 6 | Same, any sizes, every pattern that does not use some letter of Σ | | Ω(√(n₁n₂)), so Theorem 5 is optimal for every known pattern that satisfies (★) with b ≥ m/8 and does not use some letter; such patterns exist for |Σ| ≥ 3 | Claim |
| Thm 7 | Same, any sizes, pattern known in advance | O(√(n₁n₂m₁m₂)) by search with an inner search for a mismatch [4]; Õ(√(n₁n₂ min(m₁, m₂))), implied by [1] with rows as letters [9, 10]; O(n √m log⁴ n) by Theorem 1 for n × n and m × m | O(√(n₁n₂ min(m₁, m₂))), so O(n √m) for n × n and m × m, and Θ(√(n₁n₂)) in the worst case over patterns with a constant number of rows or columns; O(m₁m₂ + √(n₁n₂ min(m₁, m₂))) if the pattern is given by queries | Claim; checked by script; the step to rows and Lemmas 1 and 2 of [known-pattern-matching-queries](../known-pattern-matching-queries/) in Lean |

In one dimension the problem takes Õ(√n + √m) queries [1], by deterministic sampling [2]. In two dimensions, quantum algorithms that are fast on average are given in [3]; in the worst case, reading the rows of the pattern as letters [9, 10] in the algorithm of [1] gives Õ(n √m) for an n × n text and an m × m pattern, with polylogarithmic factors from the bounded-error comparisons of rows. Classically, Θ(n²) queries are needed in the worst case, by the same family as in Theorem 2.

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

## 7. Patterns periodic along a lattice

Here the text is n × n, the pattern m × m with m ≥ 2, and cells are points of ℤ². A *period* of P is a δ ∈ ℤ² with P[u] = P[u + δ] whenever u and u + δ are cells of the pattern. For a subgroup Λ of ℤ², write u ≡ u′ if u − u′ ∈ Λ. Say that Λ *covers* side s if every square of s × s cells contains a cell of every class of ≡.

**Condition (L).** There is a subgroup Λ of ℤ² that covers side ⌊m/2⌋ such that P[u] = P[u′] whenever u ≡ u′.

For instance, a constant pattern satisfies (L) with Λ = ℤ², and a pattern with the periods (p, 0) and (0, q) satisfies it with Λ = pℤ × qℤ when p, q ≤ ⌊m/2⌋. Both are cases of a lattice with a basis v₁, v₂ such that |v₁,ᵢ| + |v₂,ᵢ| ≤ ⌊m/2⌋ for both coordinates i: the half-open parallelogram spanned by v₁ and v₂ holds one cell of every class in each of its translates, and its projection to coordinate i is an interval of length |v₁,ᵢ| + |v₂,ᵢ| that misses an endpoint, so a suitable translate has its cells in any given square of side ⌊m/2⌋. Under (L), P extends to the array Q on ℤ² with Q[u] = P[u′] for u′ ≡ u in the pattern. Let Γ be the group of all periods of Q, that is, of the δ with Q[w + δ] = Q[w] for all w. It contains Λ, so it covers side ⌊m/2⌋ as well, and it has D ≤ ⌊m/2⌋² classes.

**Lemma 7.** Under (L), Γ is generated by the periods δ of P with |δ|∞ ≤ ⌊m/2⌋.

*Proof.* Let s = ⌊m/2⌋. A period δ of P with |δ|∞ ≤ s is a period of Q: the cells u with u and u + δ in the pattern form a rectangle with sides at least m − s ≥ s, which meets every class of Λ, so for each w there is such a u ≡ w, and Q[w] = P[u] = P[u + δ] = Q[w + δ]. Conversely every period of Q of max-norm at most s is a period of P. It remains to show that Γ is generated by its elements of max-norm at most s. Call a corner c good if every element of Γ in the square c + [s]² lies in the generated group. The corner 0 is good, since these elements have max-norm below s. If c is good and c′ differs from c by at most 1 in each coordinate, take an element z of Γ in c + [s]²; for every element q of Γ in c′ + [s]², q − z ∈ Γ has max-norm at most s, so c′ is good. Hence every corner is good, and λ ∈ Γ lies in the square with corner λ. ∎

So Γ, its classes and a representative of each class in any given square are computed from the pattern without further queries. The copies of Q at the D shifts modulo Γ are pairwise distinct, so, as in Lemma 5, there is a sample of k ≤ ⌈log₂ D⌉ classes g_t with values c_t and a survivor f: the copy shifted by j has value c_t at g_t for all t iff j ≡ f modulo Γ.

Split the starts into blocks B₀ + [K]² with K = ⌊m/2⌋. Every window x + [m]² with x in the block contains the cell c₀ = B₀ + (K − 1, K − 1) and the core c₀ + [m − K + 1]², a square of side at least ⌊m/2⌋, so the core contains a representative r(g) of every class g of Γ. Call a cell w a *defect* if T[w] ≠ T[r(w mod Γ)], and call a start x of the block *valid* if its window contains no defect.

**Lemma 8.** (a) Every occurrence in the block is valid. (b) A valid start x is an occurrence iff T[r(g + x)] = Q[g] for every class g. (c) This property depends only on the class of x, and the classes with it number at most one. (d) If φ has it, a class ψ satisfies T[r(g_t + ψ − f)] = c_t for all t iff ψ ≡ φ. So the occurrences in the block are the valid starts in the class of φ, or none if there is no such φ.

*Proof.* (a) Let x be an occurrence and u ∈ [m]². The cell r(x + u) lies in the core, hence in the window, so r(x + u) = x + u′ with u′ ≡ u, and T[r(x + u)] = P[u′] = Q[u] = P[u] = T[x + u]. (b) For x valid, T[x + u] = T[r(x + u)] for every u ∈ [m]², and P[u] = Q[u]. If x is an occurrence, take for each g a cell u of the pattern in the class g, which exists by (L); then T[r(g + x)] = T[x + u] = P[u] = Q[g]. Conversely T[x + u] = T[r(x + u)] = Q[u] = P[u]. (c) The first claim holds since r and Q depend only on classes. If x and y both have the property, then Q[g + (y − x)] = T[r(g + y)] = Q[g] for all g, so y − x ∈ Γ. (d) T[r(g_t + ψ − f)] = Q[g_t − (f + φ − ψ)], so the sample is passed iff the copy shifted by f + φ − ψ agrees with it, that is, iff φ − ψ ∈ Γ. ∎

**Theorem 4.** Under (L), two-dimensional pattern matching takes O(m² + n log² m) quantum queries, and O(n log² n) for m ≤ √n. By Theorem 2, whose pattern satisfies (L), Ω(n) queries are needed.

*Proof.* Read the pattern with m² queries and compute Γ, the sample and the representatives. In a block, the valid starts are the starts x = c₀ − a, a ∈ [0, K)², with x ∈ [0, n − m]², whose m × m rectangle with offset a around c₀ contains no defect. This is the window test of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/) with the defects as 1-cells: the four fronts of the defects at distances below m from c₀, among the cells of the text, decide it for every offset, and Lemma 3 there learns them with O(m log m log(1/δ)) queries, since a defect test takes two queries. With δ = 1/(40m(⌈log₂ m⌉ + 1)) this costs O(m log² m) queries at error at most 1/10, and the set of valid starts follows with no further queries. A search over the D phases for one that passes the sample takes O(√D log D) = O(m log m) queries at error 1/10; it finds φ if there is one, by Lemma 8(d). The block then takes any valid start in the class of the phase found, if there is one, and checks it with a search for a mismatch over its m² cells, O(m) queries at error 1/10. By Lemma 8 this decides the block with error below 1/3 and O(m log² m) queries. The search with bounded-error inputs [7] over the at most (n/K + 1)² blocks takes O(n/m) evaluations, so O(n log² m) queries. ∎

For the all-zero pattern, Theorem 4 decides whether the text has an all-zero m × m square. Patterns covered by neither Theorem 3 nor Theorem 4, such as patterns with short periods along one direction only, are covered by Theorem 1.

## 8. Identifying the window of a block

Here the text is n × n, the pattern m × m, and condition (★) of Section 6 holds for some b ≤ (m + 1)/2. Condition (★) for b implies it for every smaller b, since the set of shifts shrinks and the set C of cells grows. So (★) for a larger b gives it for b′ = min(b, ⌊(m + 1)/2⌋), and nm/b′ = O(nm/b + n).

Split the starts into blocks B + F with B a multiple of (b, b). Every start B + s with s ∈ F covers the region B + C, and an occurrence at B + s forces the text on B + C to equal the *window* W_s = (P[z − s])_{z ∈ C}. By (★) the b² windows are pairwise distinct. So the text on B + C, which we call M, determines at most one start of the block that can be an occurrence.

**Theorem 5.** Under (★) with b ≤ (m + 1)/2, two-dimensional pattern matching takes O(m² + nm/b) quantum queries, and O(nm/b) if the pattern is known in advance. For b ≥ m/8 this is O(m² + n), and O(n) for a known pattern.

*Proof.* If the pattern is not known, read it with m² queries. Fix a block. Its windows are b² distinct strings on the |C| = (m − b + 1)² ≥ b² cells of C. Encode a cell z by the bits [T[z] = a] for the letters a of P. The windows become b² distinct strings of N′ ≥ |C| ≥ b² bits, each bit answered by two queries to the text, and for at most N′ strings the unknown one is identified with O(b) queries [8, Proposition 2]. Run this on M. If M equals no window, the output is some s all the same, and the next step rejects it. If B + s is a start of the text, verify it by a search for a mismatch over its m² cells, which contain B + C, with O(m) queries [4]; otherwise the block has no occurrence. Each of the two steps is repeated a constant number of times to error at most 1/10, so the block is decided with O(m) queries and error at most 1/5. Search with a bounded-error test [7] over the at most (⌊(n − m)/b⌋ + 1)² blocks finds a block with an occurrence, if there is one, with O(n/b + 1) evaluations. That is O(nm/b + m) = O(nm/b) queries, since b ≤ n. ∎

Theorem 5 needs neither the sample nor the tournament of Theorem 3, and it applies to a known pattern without reading it.

**Proposition 6.** Let P be an m₁ × m₂ pattern that does not use the letter # ∈ Σ. Then deciding whether P occurs in an n₁ × n₂ text needs Ω(√(n₁n₂)) quantum queries.

*Proof.* Fill T with #, and place a ⌊(n₁ + 1)/(m₁ + 1)⌋ × ⌊(n₂ + 1)/(m₂ + 1)⌋ grid of m₁ × m₂ blocks, separated by single rows and columns of #. Each cell of a block holds either the letter of P at that cell or #. An occurrence contains no #, so it lies inside one block and equals it. So P occurs iff some block has no #, the OR of a ≥ n₁n₂/(4m₁m₂) ANDs of m₁m₂ bits each, which needs Ω(√(a m₁m₂)) = Ω(√(n₁n₂)) queries [6]. ∎

## 9. Rows as letters

The rows of a two-dimensional pattern can be read as letters of a one-dimensional pattern, as in [9, 10]. With the one-dimensional algorithm of [known-pattern-matching-queries](../known-pattern-matching-queries/), whose block decision only needs searches over cells, this gives a bound for every known pattern, without the polylogarithmic factors of the same reading with [1].

**Theorem 7.** For every known m₁ × m₂ pattern P and every n₁ × n₂ text, two-dimensional pattern matching takes O(√(n₁n₂ min(m₁, m₂))) quantum queries. If P is given by queries, O(m₁m₂ + √(n₁n₂ min(m₁, m₂))) queries suffice.

*Proof.* By symmetry let the bound be O(√(n₁n₂m₂)). Fix a column offset c ∈ [0, n₂ − m₂]. The rows x_r = T[r][c, c + m₂) of the strip form a string x of length n₁ over the alphabet Σ^{m₂}, and the rows of P form a string y of length m₁. P occurs at (r, c) iff y occurs in x at r. Theorem 1 of [known-pattern-matching-queries](../known-pattern-matching-queries/) splits the starts r into K ≤ 7(n₁ − m₁)/m₁ + 1 ≤ 8n₁/m₁ blocks of w = max(1, ⌊m₁/4⌋) starts and decides each block by Lemmas 1 and 2 there, which hold over every alphabet. Its steps, read on cells:

1. The identification of the common part M, which has L = m₁ − w + 1 rows, among at most w windows. Encode a cell by the bits [T[z] = a] for the letters a of P. Then the windows are at most w strings of N′ ≥ L ≥ w bits, and the identification takes O(√w) queries [8, Proposition 2].
2. The check of the identified window, and the verification of a start: searches for a mismatch over at most m₁m₂ cells, with O(√(m₁m₂)) queries [4].
3. The breaks: λ is the largest row j ∈ [max(0, s − m₁), s) with x_j ≠ x_{j+q}, if there is one, that is, the largest first coordinate among the pairs (j, k) ∈ [max(0, s − m₁), s) × [0, m₂) with T[j][c + k] ≠ T[j + q][c + k]. Maximum finding over these m₁m₂ pairs, with tests of two queries, takes O(√(m₁m₂)) queries [5]. The same holds for ρ.

So a block of a strip is decided with O(√(m₁m₂)) queries and bounded error. Search with a bounded-error test [7] over the at most (n₂ − m₂ + 1) · 8n₁/m₁ pairs of a strip and a block takes O(√(n₁n₂/m₁)) evaluations, so O(√(n₁n₂/m₁) · √(m₁m₂)) = O(√(n₁n₂m₂)) queries. Reading an unknown pattern costs m₁m₂ more. ∎

For n × n texts and m × m patterns this is O(n √m) for every known pattern, against Ω(n) by Theorem 2. For patterns with a constant number of rows or columns it is Θ(√(n₁n₂)) in the worst case over such patterns, by Theorem 2, and for each such pattern that does not use some letter, by Proposition 6.

## Lean

`lean/PatternMatch/Blocks.lean`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- Lemma 1(a): two occurrences at distance d make d a period (`period_of_occ`), so occurrences lie at least the smallest period apart (`occ_gap`).
- Lemma 1(b): an infinite word with the periods t and L has the period gcd(t, L) (`gcd_period`), and two windows of an L-periodic word that both equal the first L letters of the pattern start in the same residue class modulo L (`residue_unique`).
- Lemmas 2 and 5: copies that are pairwise distinct on a set of cells have a sample of k cells and a survivor with 2^k at most the number of copies (`sample_exists`), by keeping the smaller class.
- Sections 2 to 4: a passing start excludes the other starts of [x − f, x − f + L) (`pass_excludes`); Lemma 3 in both cases (`two_right`, `two_left`); the cell c* of Lemma 4 (`run_cell`).
- Section 6: the exclusions of a passing start in two dimensions (`pass_excludes2`), the sides used in Lemma 6 (`side_cover`), Lemma 6 (`occ_undominated`), and one duel of the tournament (`duel`).

`lean/PatternMatch/Lattice.lean`, for Section 7:

- Lemma 7: a subgroup that covers side s is generated by its elements of max-norm at most s (`closure_small`), a period of P of max-norm at most m − s is a period of Q (`period_lift`), and so the periods of Q are generated by the periods of P of max-norm at most s when 2s ≤ m (`periodGroup_eq`).
- Lemma 8: occurrences are valid (`occ_valid`), a valid start is an occurrence iff its phase matches Q (`occ_iff_phase`), two phases differ by a period of Q (`phase_unique`), and the sample is passed exactly by the class of the phase (`sample_pass`).

`lean/PatternMatch/Rows.lean`, for Sections 8 and 9:

- Section 8: an occurrence at B + s makes the text on B + C equal to the window of s (`occ_window`), condition (★) for (b₁, b₂) gives it for every smaller pair (`star_mono`), and under (★) a block has at most one start that is an occurrence (`occ_unique`).
- Section 9: P occurs at (r, c) iff the string of its rows occurs at r in the string of the rows of the strip (`occ_iff_rows`), so Lemmas 1 and 2 of [known-pattern-matching-queries](../known-pattern-matching-queries/), which are stated in Lean for every alphabet, apply with rows as letters.

**Not formalized:** search [4], minimum finding [5], search with bounded-error inputs [7], the lower bound for composed functions [6], the oracle identification [8], the maximum finding over pairs in Theorem 7, the reductions in the proofs of Theorem 2 and Proposition 6, the front learner (Lemma 3 of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/)), the random choice of values in Lemma 2, the step of Lemma 4 from the run to the set X, the sufficient condition for (L) by a basis, the use of the window test for the defects in Theorem 4 (the window test itself is in the Lean files of [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/)), and the counting of queries and errors in Theorems 1, 3, 4, 5 and 7.

## Scripts

`sim/check_strips.py` builds the period, the sample and the blocks of Sections 2 to 4 with exact searches, and checks the sample property and the occurrence sets of every block against brute force: 20000 one-dimensional instances (periodic and aperiodic patterns over 2 and 3 letters, texts with planted and noisy copies) and 1500 two-dimensional ones. It covers both block types, with and without occurrences. It checks the combinatorics with exact searches; the sample size, the query counts, the error bounds and Theorem 2 rest on the proofs above.

`sim/check_lattice.py` checks Section 7 against brute force on 1200 random instances with m from 2 to 16: lattices with a basis such that |v₁|∞ + |v₂|∞ ≤ ⌊m/2⌋, lattices in Hermite normal form whose covering of side ⌊m/2⌋ is checked by brute force (up to 64 classes), and constant patterns, over 1 to 3 letters, with texts tiled by the periodic extension at random phases and sparse noise. It checks that the lattice generated by the short periods contains the given one, that the pattern is periodic along it and that the copies on the classes are pairwise distinct, that the core of every block meets every class, the sample property and size, that the valid starts computed from the four fronts contain every occurrence, that the phase is unique and is the only class passing the sample, and that the occurrences of every block are exactly the valid starts in its class. With the seeds 1, 2 and 3 it covers about 20000 blocks, 7900 of them with occurrences.

`sim/check_blocks2d.py` checks Section 6 against brute force: condition (★), the sample of Lemma 5 and its size, that every occurrence of a block is on the front of its passing starts (learned by the front learner of `largest-empty-rectangle-queries/sim/check_window.py`, with its cost per depth), and that the tournament and the final check return exactly the occurrences of the block. It covers 400 random and sparse patterns with random texts and planted copies, and 300 texts with passing starts planted on chains and antichains of a block, so that fronts reach the largest possible length b′.

`sim/check_identify2d.py` checks the block decision of Theorem 5 against brute force: that the text on B + C matches at most one window, and that verifying that window's start decides the block. It covers random patterns of up to 10 × 10 cells over alphabets of size 2 to 4 that satisfy (★) for every b₁ ≤ (m₁ + 1)/2 and b₂ ≤ (m₂ + 1)/2, the largest such b for most of them, and random texts with planted copies, some with one cell changed: 10 000 patterns, 6850 of them with b₁b₂ ≥ 4, and about 166 000 blocks.

`sim/check_rows.py` checks Theorem 7 against brute force: for every column offset it runs the block decision of the one-dimensional algorithm on the string of rows and compares it with the occurrences of P in each block. It covers 20 000 random patterns of up to 16 × 4 cells over alphabets of size 2 and 3, half of them with periodic rows, some with one row changed, and texts with long periodic runs of rows and planted copies, about 930 000 blocks of all four kinds (no window, one window, a break, the periodic case).

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
8. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
9. R. S. Bird. Two dimensional pattern matching. Information Processing Letters 6, 1977.
10. T. P. Baker. A technique for extending rapid exact-match string matching to arrays of more than one dimension. SIAM J. Comput. 7, 1978.
