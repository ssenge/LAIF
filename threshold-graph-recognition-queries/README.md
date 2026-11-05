# Threshold graphs, chain graphs and nested matrices with quantum queries

Written 4 Nov 2026.

**Paper:** [`paper/main.pdf`](paper/main.pdf), with its source in [`paper/`](paper/).

The input is an a × b binary matrix M, or the adjacency matrix of a graph on n vertices. A query returns one entry. M is **nested** if its rows, as subsets of the columns, form a chain under inclusion. A graph is a **threshold graph** if it can be built by repeatedly adding an isolated or a dominating vertex. Equivalently (Chvátal, Hammer 1977, and proved in Lean here) it has no **alternating 4-cycle**: vertices a, b, c, d with ab, cd edges and ac, bd non-edges. A **chain graph** is a bipartite graph whose neighbourhoods on one side are nested, plus possibly isolated vertices.

| | Problem | Quantum queries | Classical randomized | Status |
|---|---|---|---|---|
| Thm 1 | Learn a nested a × b matrix | O((a + b) log³(a + b)), and Ω(n log n) for a = b = n [1] | Θ(ab) | Lean: correctness given correct searches, and the expected count assuming BBHT. Claim: bounded error, worst case |
| Thm 2 | Is M nested? (a, b = Θ(n)) | Θ̃(n) | Θ(n²) | As Thm 1 |
| Thm 3 | Is G a threshold graph? | O(n log⁴ n), Ω(n) | Θ(n²) | As Thm 1, with Ω(n) assuming the OR bound. Classical bound: Claim |
| Thm 4 | Is G a chain graph? | Θ̃(n) | Θ(n²) | Correctness and Ω(n) as above. Cost: Claim |

Unconditional on paper, and the algorithm is explicit: Õ(n) entry reads and Grover searches, with no reduction to an adversary bound. These are query counts on a noiseless model. On "yes" inputs the quantum count only passes reading all pairs near n ≈ 1000 to 2000.

**Prior work.** Half graphs are the special case of nested matrices with all rows and all columns distinct. Mande, Sanyal and Zamaraev [1] learn them with Θ(n log n) quantum and Θ(n log n) randomized queries, by a quicksort that compares rows with Grover search. So it is equal rows and columns that make the classical problem cost Ω(ab). Learning a nested matrix is also Goswami and Jacob's bipartite sorting [2], with a classical algorithm within log³ of instance-optimal. To our knowledge, what is new here is the Õ(a + b) quantum learner with ties allowed, and the three recognition theorems. Their quicksort assumes distinct rows.

The natural baseline is Õ(n^{3/2}), since the certificate has 4 vertices. Magniez, Santha and Szegedy [3] state this for non-induced copies and monotone properties, and an alternating 4-cycle uses non-edges, so it does not apply as stated.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Quantum query complexity | Recognizing threshold graphs and chain graphs from the adjacency matrix | Θ(n²) classically; about n^{3/2} suggested by the 4-vertex certificate, not stated for these induced patterns; no quantum result known to us | O(n log⁴ n) and Õ(n), Ω(n), so Θ̃(n) against Θ(n²) | Explicit algorithm; queries only | Correctness given correct searches, and the expected count for threshold graphs: Lean, assuming BBHT and the OR bound. Bounded error and the chain cost: Claim |
| Quantum query complexity | Learning and recognizing nested a × b matrices, with equal rows allowed | Θ(n log n) for half graphs, that is with all rows and columns distinct, by Mande, Sanyal, Zamaraev; Θ(ab) classically with ties | O((a + b) log³(a + b)); recognition Θ̃(n) for a, b = Θ(n) | Explicit algorithm; queries only | As above |

## 1. Positions

**Lemma 1.** M is nested iff there are integer positions p on rows and q on columns, with p even and q odd, such that M[r, c] = 1 ⇔ p(r) > q(c).

*Proof.* Given positions, N(r) = {c : q(c) < p(r)} grows with p(r), so rows are nested. Conversely let S₀ ⊊ S₁ ⊊ … be the distinct rows. Put p(r) = 2i for N(r) = S_i. Let i(c) be the first i with c ∈ S_i, or one more than the last index if c is in no row, and put q(c) = 2i(c) − 1. Then c ∈ N(r) ⇔ i(c) ≤ index(r) ⇔ q(c) < p(r). ∎

So columns are nested too, and so is the complement matrix.

## 2. The learner

A **search** is BBHT: on N candidates, it returns a uniformly random marked one, or none, in O(√N log(1/δ)) queries, and wrongly reports none with probability at most δ. On a block of size a × b, N = ab and √N ≤ (a + b)/2. That inequality is what makes this work.

**Holding(R, C, val).** Set K := ∅. Repeat: search R × (C \ K) for an entry equal to val. If none, return K. If (r, c) is found, read row r on C, and add its val-entries to K.

**Lemma 2.** On a nested block, with correct searches, Holding returns exactly the columns having an entry val, in O(log |R|) expected rounds.

*Proof.* The set is correct by the stopping rule. By Lemma 1 for M or its complement, the sets {c : M[r, c] = val} are nested. Let U be the rows with an entry val outside K. The weight of r ∈ U, its number of val-entries outside K, grows along the chain, so the upper half of U holds at least half the marked entries. With probability at least 1/2 the found row r is in the upper half. After reading it, K contains all val-entries of every row at or below it in the chain, so |U| at least halves. ∎

**Trim(R, C).** Run Holding on columns and, on the transpose, on rows, for val = 0 and val = 1, all on this same block. A row or column missing from the val-list is constant 1 − val on the block: record those entries and remove it. Removal is one pass, relative to the block given.

**Learn(R, C).** If |R||C| ≤ 4(|R| + |C|), read everything. Otherwise pick x ∈ R and w ∈ C uniformly. Read row x on C, giving C₁ (its 1-entries) and C₀, and column w on R, giving R₁ and R₀.

- If M[x, w] = 1: record R₀ × C₀ as 0, and recurse on Learn(Trim(B)) for B = R₀ × C₁, R₁ × C₁, R₁ × C₀.
- If M[x, w] = 0: record R₁ × C₁ as 1, and recurse on Learn(Trim(B)) for B = R₀ × C₁, R₀ × C₀, R₁ × C₀.

**Lemma 3 (exact split).** On a nested block, the recorded entries are right, and the three trimmed blocks are contained in three disjoint position intervals. So every row and column survives into at most one of them.

*Proof.* Write p = p(x), q = q(w). R₀ = {p(r) < q}, R₁ = {p(r) > q}, C₁ = {q(c) < p}, C₀ = {q(c) > p}.

Case q < p, so M[x, w] = 1. On R₀ × C₀, p(r) < q < p < q(c), giving 0.
- R₀ × C₁: a column with q(c) ≥ q lies above all rows of R₀, so it is constant 0 and is trimmed. What survives lies below q.
- R₁ × C₁: a row with p(r) ≥ p lies above all columns of C₁, so it is constant 1. A column with q(c) ≤ q lies below all rows of R₁, so it is constant 1. What survives lies strictly between q and p.
- R₁ × C₀: a row with p(r) ≤ p lies below all columns of C₀, so it is constant 0. What survives lies above p.

Case p < q, so M[x, w] = 0. On R₁ × C₁, p(r) > q > p > q(c), giving 1.
- R₀ × C₁: a row with p(r) ≥ p is constant 1. What survives lies below p.
- R₀ × C₀: a row with p(r) ≤ p is constant 0, and a column with q(c) ≥ q is constant 0. What survives lies strictly between p and q.
- R₁ × C₀: a column with q(c) ≤ q is constant 1. What survives lies above q. ∎

**Lemma 4 (balance).** Let m = |R| + |C|. With probability at least 1/4 each trimmed block has at most 3m/4 rows and columns.

*Proof.* Order rows by p, breaking ties arbitrarily. A row of rank i has at most i − 1 rows strictly below it and at most a − i strictly above. Both are at most 3a/4 for a/4 ≤ i ≤ 3a/4 + 1, which is at least a/2 ranks. So x has this property with probability at least 1/2, and independently so does w with 3b/4. By Lemma 3 the surviving rows of a block lie strictly on one side of p(x), and its surviving columns strictly on one side of q(w). The case list there shows this for all six blocks. So each block has at most 3a/4 + 3b/4 rows and columns. ∎

**Theorem 1.** Learn determines a nested a × b matrix with O((a + b) log³(a + b)) expected queries and bounded error. For a = b = n at least Ω(n log n) queries are needed. Classically Ω(ab).

*Proof.* Correctness follows from Lemmas 2 and 3, by induction, and the lower bound for a = b = n is the half graph bound above. Cost: a node with m rows and columns reads m entries and does four Holding calls per block. By Lemma 2 each is expected O(log m) rounds, each costing a search O(m λ), where λ = log(1/δ), plus a read of m. By Lemma 3 the blocks at a depth are disjoint in rows and columns, and by Lemma 4 a given row or column lies in expected O(log m) levels. So the expected total is O(m log² m · λ). Base cases read at most 4 per row or column. There are polynomially many searches, so λ = O(log m) gives error 1/10 by a union bound. Truncating at ten times the expected cost adds error 1/10 and makes the bound worst case. The classical bound follows from the all-0 matrix against a single hidden 1: both are nested, and Ω(ab) reads are needed to tell them apart. ∎

Only the lists of Lemma 2 use uniformity of Grover's outcome, and BBHT provides it.

## 3. Recognition

**Check.** Learn a hypothesis H, reject if truncated or if H is not in the class, which is free. Then search all entries for a disagreement with the input, at O(√(ab)) queries. If the input is in the class, H equals it with high probability, and the answer is yes. If it is not, H ≠ input, since H is in the class, and the search finds a disagreement with high probability. So correctness does not depend on what the learner does on bad inputs.

**Hard family.** Let vertices 0, …, n − 1 have creation sequence 0, 1, 0, 1, …, so odd j is adjacent to all i < j. For even i and odd j with j ≥ i + 3, delete the edge ij. Then j, i + 2, i + 1, i is an alternating 4-cycle: j ~ i + 2, i + 1 ~ i, and j ≁ i, i + 1 ≁ i + 2. There are Θ(n²) such pairs. So deciding the class on "no deletion or one deletion" is OR on N = Θ(n²) bits with at most one 1, which needs Ω(n²) classical randomized and Ω(n) quantum queries. The bipartite part between odd and even vertices gives the same for nested matrices and chain graphs.

**Theorem 2.** Is M nested? Õ(a + b) quantum queries, and Ω(√(ab)) on the hard family with those shapes. Tight when a = Θ(b). Unbalanced shapes are not tight: for a = 2 this is subset testing, Θ(√b), while the learner reads b.

**Theorem 3.** Threshold recognition: O(n log⁴ n) quantum, Ω(n) quantum, Θ(n²) classical.

*Proof.* Split the vertices in two parts A, B. If G is a threshold graph, the cross block A × B has no 2 × 2 permutation pattern, since that would be an alternating 4-cycle, so it is nested. Learn it, and recurse on A and on B. Each pair falls in exactly one block. The cost recurrence L(n) = 2L(n/2) + O(n log³ n) gives O(n log⁴ n). All searches share one λ = O(log n) and the whole run shares one truncation, so the "error 1/10" of Theorem 1 is not applied n times. The check costs O(n). The lower bounds come from the hard family, and classically reading all pairs is enough. ∎

The split avoids the diagonal of the adjacency matrix, where no query is defined.

**Theorem 4.** Chain graph recognition: Õ(n) quantum, Ω(n) quantum, Θ(n²) classical.

*Proof.* Search for an edge (x, y). If none exists, accept. Read N(y) =: X. With Holding on rows X and all vertices, compute Y := N(X). With Holding again, compute X := N(Y). In a chain graph with sides A ∋ x and B ∋ y: X = N(y) contains the top vertex a* of A, since a* is adjacent to all non-isolated vertices of B. So Y ⊇ N(a*) is all non-isolated vertices of B, and likewise the second step gives all non-isolated vertices of A. Reject if X ∩ Y ≠ ∅. Learn X × Y, and check against the input on all pairs. ∎

## 4. Learning lower bound for larger classes

A perfect matching is a cograph, and learning a matching costs Θ(n^{3/2}) queries (van Apeldoorn et al., through [1]). So learning any class containing all matchings, such as cographs, trivially perfect, unit interval, interval, permutation and distance-hereditary graphs, needs Ω(n^{3/2}) queries. Threshold and chain graphs differ because a cross block has no 2 × 2 permutation pattern. Split graphs need Ω(n²) queries to learn.

Recognition need not go through learning. For cographs and trivially perfect graphs it is open: their "no" certificates have constant size, so adversary methods stop at O(n).

## 5. Practical reading

`sim/grover_stats.log`: at budget 16 per search and n = 1024, the recognizer spends about 454,000 queries, against 523,776 entries for reading all pairs. So it only barely wins at n = 1024, with a real margin by n = 2048 (`sim/check.log`: about 1.2M queries against 2.1M entries for the worst family). Budget 8 has wrong answers at n = 1024 (3 of 10 on "yes" inputs). Budget 16 gets 1 of 300 wrong at n = 1024 and 0 of 80 at n = 2048. A constant budget cannot hold forever, since the proof needs λ = Θ(log n). Sets of at most 16 candidates are read directly, since false nones were most frequent there. The fitted exponents at n ≤ 2048 are 1.0 to 1.4, and queries/(n log₂ n) keeps growing on `alternating` and `random`, consistent with the extra log factors of Theorem 3. On inputs far from the class it can spend far more than reading everything: 61.9M queries against 1M entries on the identity at n = 1000, in one run not kept here. A practical version would stop at the cost of reading everything and then read everything, so it would never pay more than twice the classical cost.

## 6. Measurements

`sim/check.py`: all 33,867 graphs up to n = 6, for threshold and chain, 0 wrong, against an independent classical decision; families and single flips up to n = 150 agree. `sim/grover_stats.py`: as above. `sim/qiskit_check.py`: every search a circuit, 30 runs, 0 wrong, at most 8 qubits, 3499 circuits. At these sizes it spends far more queries than there are entries (about 800 against 81), so this tests the construction and shows no gain.

## 7. Limits

- Queries only, on a noiseless model. No gate or time bound is given.
- The upper and lower bounds differ by polylogarithmic factors. The learner has Ω(n log n) from half graphs [1] and O(n log³ n) from this proof.
- Theorem 2 is not tight on unbalanced shapes.

## 8. Importance

This is a natural pair of recognition problems where a quadratic classical cost drops to about linear, below the n^{3/2} that the 4-vertex certificate suggests. The method is plain: a Grover search over an a × b block costs at most (a + b)/2, and random pivots split a nested block into disjoint position intervals. Whether more of the hierarchy of graph classes admits this is open, and Section 4 shows that learning cannot do it for any class containing all matchings.

## 9. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry`, `axiom` or `native_decide` in the sources. `lake env lean GraphClasses/Axioms.lean` prints the axioms of 49 theorems: only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

| Part | Theorems | Hypotheses |
|---|---|---|
| Lemma 1 | `nested_iff_positions`, `nestedOn_iff_positions` | |
| Lemma 3 | `lemma3_pos`, `lemma3_neg`, `split_intervals`, `split_disjoint` | |
| Holding, Trim, Learn | `holding_correct`, `trim_table`, `learn_correct` | correct searches (`SearchSpec`), a pivot rule (`PickSpec`), enough fuel |
| Lemma 2's rounds | `weight_halving`, `expRounds_le_rows` | uniform search |
| Lemma 4 | `good_card`, `good_pairs_card`, `lemma4_good` | |
| Recognition | `check_sound`, `check_complete`, `recognizeNested_iff`, `recognizeThreshold_iff`, `recognizeChain_iff` | correct searches |
| Threshold | `threshold_iff_noAlt`, `cross_block_nested`, `blocks_nested`, `pair_in_one_block` | |
| Chain sides | `discover_correct` | correct searches |
| Hard family | `hardDel_alt`, `hardG_noAlt`, `hardPairs_theta`, `hardMat_nested`, `hardChain_isChain` | |
| Cost | `expCost_le`, `expected_cost_explicit`, `theorem1_expected_cost`, `threshold_expected_cost` | `BBHTSearch` for `theorem1_expected_cost` |
| Lower bounds | `threshold_lower_bound`, `chain_lower_bound`, `nested_lower_bound` | `ORLowerBound` |

**Assuming.** `BBHTSearch` and `ORLowerBound` are named hypotheses in `lean/GraphClasses/Model.lean`, over an explicit query model `QAlg`. `exists_searchSpec` and `exists_splitSpec` show the specifications can be met.

**Not formalized.** `learn` is a classical function and its cost is accounting: `expCost` charges c·m per node, and `node_cost_le` and `base_cost_le` show which c suffices. Queries are not counted from an execution. Pivot and search randomness are not combined in one space. The union bound over searches and the truncation are absent, so "bounded error" and the worst-case forms of Theorems 1 to 4 are not covered. Also absent: the classical lower bounds, the Ω(n log n) learning bound, a cost theorem for the chain recognizer, Section 4 and the simulations.

## References

1. N. S. Mande, S. Sanyal, V. Zamaraev. Complexity of learning matchings and half graphs via edge queries. arXiv:2507.03151.
2. M. Goswami, R. Jacob. On instance-optimal algorithms for a generalization of nuts and bolts and generalized sorting. arXiv:2211.04601.
3. F. Magniez, M. Santha, M. Szegedy. Quantum algorithms for the triangle problem. SODA 2005, arXiv:quant-ph/0310134.
4. V. Chvátal, P. Hammer. Aggregation of inequalities in integer programming. Annals of Discrete Mathematics 1, 1977.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
