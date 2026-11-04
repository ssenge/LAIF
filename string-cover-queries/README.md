# Covers of a string with quantum queries

Sebastian Senge, Independent Researcher. Written 4 Nov 2026.

S is a nonempty string of length n, and a query returns one character. A string C **covers** S if every position of S lies in an occurrence of C. A **border** of S is a string that is both a prefix and a suffix. A cover of S is a border of S, and S covers itself. Identify a border with its length.

| | Problem | Quantum queries | Classical randomized | Status |
|---|---|---|---|---|
| Thm 1 | Shortest cover | O(√n log⁴ n), Ω(√n) | Θ(n) | Combinatorics and cost arithmetic in Lean; the composition is a claim |
| Thm 2 | All covers, as O(log n) arithmetic progressions | O(√n log⁵ n), Ω(√n) | Θ(n) | Same |

The algorithm is explicit. It is a minor result: see below. These are query counts on a noiseless model, and the constant is large, so reading the string stays cheaper until about n ≈ 10¹¹ or later.

**Earlier work.** This is a minor result: close to a short corollary of published classical structure, with Grover search over the windows and explicit logarithms. To our knowledge no quantum result on covers has been stated before. These parts already exist:

- Few candidates: Crochemore et al. (arXiv:2007.13471, Proposition 4.2) note that the shortest cover is aperiodic, so only the shortest border of each progression can be it. Lemma 1 is also the parenthetical in Radoszewski and Zuba's Lemma 4 (arXiv:2409.14559), and follows from Lemma 8 of Kikuchi et al. (arXiv:2002.06764).
- Covers in a progression are a prefix, with a cut-off: Radoszewski and Zuba's Lemma 4.
- Testing by local windows with internal pattern matching: arXiv:2007.13471, Lemma 3.2, and the same Lemma 4.
- All borders in O(1) progressions per dyadic range: the Period Query of Kociumaka et al. (arXiv:1311.6235).
- The sample, with extreme survivors and a fair coin: Wang and Ying (arXiv:2012.09376), Algorithm 4. The gcd restart here differs from theirs. Quantum pattern matching is from Ramesh and Vinay. Quantum internal pattern matching and LCE at Õ(√m) are also available (arXiv:2402.14550, arXiv:2410.06808).

Radoszewski and Zuba's Ω(n/log n) in the PILLAR model rules out a pure PILLAR corollary, as Grover over blocks is not a PILLAR operation. Classically the shortest cover takes O(n) time (Apostolico, Farach, Iliopoulos 1991, from memory; not read).

## 1. Few candidates

**Fact (transitivity).** If A covers B and B covers S, then A covers S. Each position of S lies in an occurrence of B, and that position of B lies in an occurrence of A.

**Lemma 1.** Let u, v be borders of S with |u| ≤ |v| < 2|u|. Then u covers v.

*Proof.* u is a prefix of v, and a suffix of v since both are suffixes of S. Its two occurrences in v start at 0 and at |v| − |u| < |u|, so they leave no gap. ∎

**Corollary.** For each k let b_k be the shortest border with length in [2^k, 2^{k+1}). The shortest cover is the first b_k that covers S. Within one range, the covers are exactly the first few borders in increasing length.

*Proof.* Let C be the shortest cover, in the range of k. Then b_k covers C by Lemma 1, so it covers S by transitivity, and it is not longer than C, so b_k = C. Smaller k's have no cover at all. For the last claim, if a border v in the range covers S, and u is a shorter border in the range, then u covers v, so u covers S. ∎

So only O(log n) strings need testing for the shortest cover, and a bisection in each range gives all of them.

## 2. Occurrences in a short range

Fix a prefix P of S of length ℓ ≥ 16. An **alignment** a places a copy of P at offset a. The **sample** follows Wang and Ying's Algorithm 4. Keep a list of columns (x, c). Alignment a survives if P[x − a] = c for all columns. Find the lowest and highest survivors a < b by minimum finding. Search for a column x where they differ, in their overlap [b, a + ℓ). Then every survivor is defined at x. Append (x, c) with c a fair choice of the two characters. The smaller class has at most half the survivors, so the survivors halve with probability at least 1/2. Stop when one survivor s is left. If this takes more than C log n columns, redraw, so a sample has O(log n) columns and each draw succeeds with high probability.

If a and b agree on the whole overlap, then d = b − a is a period of P. Then set w to d, or to the gcd of d and the period known so far, and restart with no columns. With alignments [0, w) and w ≤ ℓ/8, any periods in use sum to at most ℓ, so by Fine and Wilf every such d is a multiple of the smallest period p, and the gcd is again a period, at most half the last one.

**Lemma 2.** If the sample ends with w and one survivor, then p ≥ w. If in addition w is a period, then p = w.

*Proof.* Suppose p < w, and let U be the current survivors. We keep this invariant: U is closed under ±p within [0, w), min U < w − p, and max U ≥ p. It holds at the start. A new column lies in the overlap of the extremes a < b, so all survivors are defined there, and alignments differing by p have the same character. So the closure persists. The kept class contains a or b. If a, then a + p also survives and the minimum stays. If b, then b − p ≤ w − 1 − p survives and the maximum stays. Either way |U| ≥ 2, so one survivor is impossible. Only the last phase matters, since a restart clears the columns. ∎

**Lemma 3 (Vishkin).** Suppose position t of the text passes the sample, that is, S[t + x − s] = c for all columns. Then no t′ ≠ t in [t − s, t − s + w) is an occurrence of P. So in a block of at most w consecutive starts, only the leftmost and rightmost passing starts can be occurrences.

*Proof.* Let a = t′ − t + s ∈ [0, w), a ≠ s. Take the first column (x, c) that rejects a. Alignment a was a survivor just before, so it lies between the extremes and is defined at x, and P[x − a] ≠ c. But an occurrence at t′ would put P[x − a] at text position t′ + x − a = t + x − s, which holds c. Now let t₁ ≤ t₂ be the extremes, with t₂ − t₁ < w. A start y strictly between lies in the range of t₁ if y < t₁ − s + w, and otherwise y ≥ t₁ − s + w > t₂ − s, so it lies in the range of t₂. ∎

**Occurrence search.** Let B be a range of at most ⌈ℓ/2⌉ starts, with largest element z.

*Prepare.* Compute a sample with w = ⌊ℓ/8⌋. If no period appears, then p ≥ w by Lemma 2, and we are in the first case below. If one appears, it is p by Lemma 2, with p ≤ ℓ/8. Take Q as the prefix of length 4p and compute its sample with w = p. Q has smallest period p, as a smaller period of Q would extend to P, since Q is at least one period long and P has period p.

*No period appeared.* B is at most 6 blocks of w. In each, take the two extremes by Lemma 3, and verify them with a search. Output these.

*A period appeared.* If t ∈ B is an occurrence, then t + mp ∈ (z − p, z] for some m ≥ 0, and it is an occurrence of Q, since z + 4p ≤ t + (ℓ − 1)/2 + 4p < t + ℓ. Q has at most one occurrence in a range of p starts, since two would differ by a shift smaller than p, which would be a period of Q. Find it, by Lemma 3 and a verification, and call it y. If there is none, output nothing. Extend the p-periodic run around y, by first-mismatch searches: forward with a cap of at least min(z + ℓ, n) and at most O(ℓ) past y, and backward only down to the smallest element of B. Call the result [lo, hi). If |B| < p, y can lie below B. Then no occurrence lies in B, and the output is empty, which is correct. Output {t ∈ B : t ≡ y mod p, t ≥ lo, t + ℓ ≤ hi}.

**Lemma 4.** With correct searches this returns exactly the occurrences of P with start in B, at a cost of O(√ℓ · polylog) queries. Given the sample, one call costs O(√ℓ log² n), with error 1/n³ per call.

*Proof.* First case: by Lemma 3. Second case: each t in the output has S[t, t + ℓ) with period p and starting with Q, since t ≡ y inside the run, so it equals P. Conversely, an occurrence t ∈ B and y overlap in at least p positions, so t lies in the same run, and t ≡ y. For cost: a minimum finding has √ℓ applications at O(log n) queries each, for a sample of O(log n) columns, and λ = O(log n) for the error. Verifications and the capped run extensions cost O(√ℓ log n) by doubling. ∎

For ℓ < 16 read the range directly.

## 3. Testing one candidate

Let u be a border of length ℓ. Its occurrences include 0 and n − ℓ. It covers S iff consecutive occurrences differ by at most ℓ. Cut the starts into blocks of s = ⌈ℓ/2⌉.

**Predicate.** Let pred(j) hold if, using the occurrences in blocks j, j + 1, j + 2, either two consecutive ones differ by more than ℓ, or the last of them lies in block j and is not n − ℓ.

**Lemma 5.** u covers S iff no block has pred(j).

*Proof.* If pred(j) holds by the first rule, there is a gap. By the second rule, the next occurrence exists, as n − ℓ is an occurrence, and it is past block j + 2, so at distance at least 2s + 1 > ℓ. Conversely, if consecutive g, g′ differ by more than ℓ, take the block j of g. Either g′ is in the three blocks, which is the first rule, or g is the last there, which is the second. ∎

**Lemma 6.** Testing u costs O(√n log³ n) queries after a sample, with error 1/n² for λ = O(log n) with a large enough constant.

*Proof.* There are at most 2n/ℓ + 1 blocks, and pred costs O(√ℓ log² n) by Lemma 4. Grover over blocks gives O(√(n/ℓ) · √ℓ log² n · log n). The inner routine runs coherently, and an inner error δ adds up to T · O(√δ) in norm over T outer iterations, not T δ. With T ≤ √n polylog n and δ = n⁻⁶ this is below 1/n². ∎

## 4. All borders in a range

Let L = 2^k. The starts of borders in [L, 2L) lie in a range of L starts. Split it into two ranges of L/2 and search occurrences of the prefix of length L, by Lemma 4. Each output is a short list or a progression with run [lo, hi).

For a list: verify each by a search.

For a progression with step p: let f be the length of the longest prefix of S with period p, capped at 2L, by a first-mismatch search. The cap is harmless, as border lengths here are below 2L. Here the run extension must use a forward cap of 2L, since a cap of z + L would stop before n on the lower half of the range and lose borders: on a⁶⁴ with L = 16 and B = (32, 40], it stops at 56 with no break. As y ≥ n − 2L + 1, the cap 2L reaches n. If hi = n, then a start t in the progression gives a border iff n − t ≤ f. Indeed the suffix from t has period p and starts with the right p characters, so it equals the prefix iff that prefix has period p up to its length. If hi < n, the suffix has its first break of period p at offset hi − t. A prefix of length n − t > hi − t must break at the same offset. So t = hi − f is the only possibility, and it is verified by a search.

**Lemma 7.** All borders in [L, 2L) are found as O(1) progressions, in O(√L polylog) queries.

## 5. Results

**Theorem 1.** The shortest cover costs O(√n log⁴ n) quantum queries.

*Proof.* Correctness: the Corollary, Lemmas 4, 5, 7, with outer classical calls by a union bound and coherent calls as in Lemma 6. Cost: a sample has at most log w phases of O(log n) columns. A column costs O(√ℓ log n) for its mismatch search, plus two minimum findings at O(√w log² n), and w halves between phases, so those sum geometrically. The total is O(√ℓ log³ n) at error 1/poly. Over k ≤ log₂ n, finding b_k costs O(√(2^k) log³ n), and these sum geometrically. Each of the O(log n) tests costs O(√n log³ n) by Lemma 6. ∎

**Theorem 2.** All covers cost O(√n log⁵ n). In each range, covers are a prefix of the progressions of Lemma 7, so bisect with O(log n) tests. ∎

**Lower bounds.** Let S be aⁿ, or aⁿ with position i set to b, for any i. For j < n, a prefix and a suffix of length j that both contain b would place it at offsets i and i − (n − j), which differ. So the borders are a^j for j ≤ min(i, n − 1 − i), plus S. The a^j miss position i, so the only cover is S. Hence the shortest cover has length 1 iff S = aⁿ, for n ≥ 2. That is OR on n bits, which needs Ω(√n) quantum and Ω(n) randomized queries. The alphabet is binary.

## 6. Scope

The results are for covers. Gate-efficient versions are not worked out: Lemma 6 is a nested search with bounded-error inner routine, which here pays for error reduction by logarithms.

## 7. Practical reading

The constant is poor. `sim/check.log` at budget 16 has a charged cost of about 3 × 10⁵ √n on "one b" at n = 2¹⁸, and 7 × 10⁵ √n on the family with cover length near √n. With that constant frozen, this beats reading the n characters only above about n ≈ 10¹¹ to 5 × 10¹¹. The constant still grows with n, so fits put the crossover at about 10¹² to 10¹⁵. Two further effects pull in opposite directions. `search` charges 2j + 1 applications where j Grover iterations need about j, so the charge is about 2 times too high per level of nesting. And budget 16 is likely too low at that scale, which a real run would have to raise.

The charge per outer application is the fixed cap `pred_cap`. The two-way inner cost stayed below it in every run of `sim/check.py`, at most 0.65 of it for ℓ ≥ 16 up to n = 2048. Up to n = 2048 is not a proof. It is a model of a device that truncates at the cap, and the code does not enforce that truncation. The outer marked set comes from the simulator's Z array, so inner errors are not modelled in the cost runs.

The fitted exponents at n ≤ 2¹⁸ are 0.36 to 0.87. The 0.36 is an artefact of a spike at n = 4096 on the Fibonacci family, whose cause I did not investigate. The largest is on "random", where the logarithms of Theorem 1 still dominate, and it falls to about 0.70 on the last three sizes. So these runs do not show √n cleanly, only that the growth is well below linear on this cost model.

## 8. Measurements

`sim/check.py`: all 42,096 strings up to n = 14 (ternary up to 8), shortest and all covers, agree with brute force. These never reach the sample, since ℓ < 16. 384 runs on families up to n = 2048 agree too, and the inner predicate agrees with the truth on every block for short borders and a spread of borders with ℓ ≥ 16, on 564 periodic and 797 aperiodic contexts. The cost table's answers at budget 16 are checked against the truth, up to n = 2¹⁸, with 0 wrong. `sim/qiskit_check.py`: with every search a circuit, 21 runs and 35 inner predicates, 0 wrong, at most 7 qubits, 43,115 circuits. The outer search there uses a table of predicate values, not nested circuits, and those predicates exercise no periodic context. Spending far exceeds n, so it tests the construction and shows no gain.

## 9. Limits

- Queries only. The inner routine is bounded-error and pays for error reduction by logarithms. A gate count is not worked out.

## 10. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry` and no `axiom` declaration. `lake env lean Covers/Axioms.lean` prints the axioms of 73 theorems: only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

| Part | Theorems |
|---|---|
| Definitions, a cover is a border, transitivity | `Covers.isBorder`, `Covers.trans` |
| Lemma 1, Corollary | `lemma1`, `corollary_shortest`, `first_covering_rangeMin_isShortest`, `covers_downward_in_range`, `firstCover_correct` |
| Lemma 2 | `IsPhase.invariant`, `lemma2_le`, `lemma2_eq` |
| Lemma 3 | `vishkin_exclusion`, `two_extremes_block`, `IsPhase.isSample` |
| Periods | `fine_wilf`, `gcd_restart`, `smallest_period_take` |
| Lemma 4, its cases | `blocks_le_six`, `lemma4_case1`, `Q_occurrence_unique`, `output_sound`, `output_complete`, `lemma4_case2` |
| Lemma 5 | `covers_iff_no_gap`, `lemma5`, `lemma5_blocks` |
| Section 4 | `border_iff_of_run_to_end`, `border_start_of_run_break`, `cap_reaches_end`, `capped_stop_is_not_break` |
| Lower-bound fact | `oneB_shortestCover`, `shortest_lengths_differ` |
| Query counts | `theorem1_cost`, `theorem2_cost`, `coherent_error_le`, `union_bound_failure` |
| Quantum lower bound | `cover_lower_bound`, assuming `ORBound` |

**Assuming.** Named hypotheses in `lean/Covers/Model.lean`: `BBHTSearch`, `DurrHoyerMin` and `ORBound` on an explicit query model, and `GroverCorrect`, `GroverCost`, `MinCorrect`, `MinCost` for the accounting. `primitives_consistent` shows the last four can hold together, with exact classical search as its witness, so this shows logical consistency only. The charges of 2·I per predicate call and the phase and column budgets are assumed too, and a coherent nested search with these costs is not constructed.

**Not formalized.** An end-to-end success probability. The sample's O(log n) columns with high probability and the redraw: a phase ending with one survivor is a hypothesis. Lemma 4 and Lemma 7 as whole algorithms, only their combinatorial cases. The classical Ω(n) bound, and the decision tree paragraph.

## References

1. J. Radoszewski, W. Zuba. Computing string covers in sublinear time. arXiv:2409.14559.
2. M. Crochemore, C. S. Iliopoulos, J. Radoszewski, W. Rytter, J. Straszyński, T. Waleń, W. Zuba. Internal quasiperiod queries. arXiv:2007.13471.
3. N. Kikuchi, D. Hendrian, R. Yoshinaka, A. Shinohara. Computing covers under substring consistent equivalence relations. arXiv:2002.06764.
4. T. Kociumaka, J. Radoszewski, W. Rytter, T. Waleń. Internal pattern matching queries in a text and applications. arXiv:1311.6235.
5. Q. Wang, M. Ying. Quantum algorithm for lexicographically minimal string rotation. arXiv:2012.09376.
6. H. Ramesh, V. Vinay. String matching in Õ(√n + √m) quantum time. J. Discrete Algorithms 1, 2003.
7. A. Apostolico, M. Farach, C. S. Iliopoulos. Optimal superprimitivity testing for strings. Information Processing Letters 39, 1991.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
