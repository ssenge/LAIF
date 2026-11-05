# Quantum query complexity of minimum cut in the adjacency array model

Written 5 Nov 2026.

## Result

In the adjacency array model one can query the degree of a vertex, and the name and weight of its i-th neighbour. Let G have n vertices, m edges and weights between 1 and τ. The upper bound is Õ(√(mnτ)) [1, Theorem 21]. For dense graphs the known lower bounds were Ω(n) for τ = 1, Ω(n^{3/2}) for τ > 1 and Ω(τn) for τ ≤ 5n/8 [1, 2], and this gap is Open Problem 1 of [1].

**Theorem 1.** Let 1 ≤ τ ≤ n/4 with 4 | n. Any bounded-error quantum algorithm that computes the weight of a minimum cut in the adjacency array model makes Ω(n^{3/2} √τ) queries, on graphs with Θ(n²) edges and weights in {1, τ}.

With [1, Theorem 21], the complexity on dense graphs is Θ̃(n^{3/2} √τ) for every 1 ≤ τ ≤ n/4. This is the value of the adjacency matrix model [1].

**Corollary 2 (simple graphs).** Edge connectivity of simple graphs needs Ω(n^{3/2}) adjacency array queries, so it is Θ̃(n^{3/2}) on dense simple graphs.

For τ = 1, [1] suspects Θ̃(n) in the adjacency array model. Corollary 2 gives a different answer on dense graphs. For τ > 1, [1] suspects Θ̃(√(mnτ)), and Theorem 1 confirms this at m = Θ(n²).

**Theorem 3 (all densities).** For n ≤ m ≤ n²/32 and 1 ≤ τ ≤ n/4, with τm/n at least a suitable constant, Ω(m √(τ/n)) adjacency array queries are needed. For simple graphs this gives Ω(max{n, m/√n}), the term n coming from connectivity [2]. Compared with Õ(√(mnτ)), a factor n/√m remains open below dense graphs.

**Theorem 4 (finding the cut).** Theorem 1 also holds for an algorithm that outputs the shores of a minimum cut instead of its weight.

Theorem 1 and Corollary 2 are machine-checked, assuming the degree bound for exact counting. Theorems 3 and 4 have written proofs and small brute-force checks.

## Proof of Theorem 1

**The graphs.** The family is the one of [1, Theorem 40], with many more 4-cycles. Let n = 4t, and let the vertices be four classes A, B, D, C, each indexed by Z_t. Each class is a clique of weight τ. For each cell (i, j) ∈ Z_t², take the 4-cycle A_i, B_{i+j}, D_i, C_j. An input bit x_ij selects one of its two perfect matchings, with weight 1:

- x_ij = 1: edges A_i B_{i+j} and D_i C_j;
- x_ij = 0: edges A_i C_j and B_{i+j} D_i.

Each pair of vertices lies in at most one 4-cycle, since (i, j) is determined by each of (A_i, B_{i+j}), (D_i, C_j), (A_i, C_j) and (B_{i+j}, D_i). So the graph has no parallel edges, and it is simple for τ = 1. Each vertex has t − 1 clique neighbours and t cycle neighbours for every x.

**One query reads one bit.** Fix for each vertex an order of its clique neighbours and its 4-cycles. Degrees and clique entries do not depend on x. The entry of a vertex for a 4-cycle depends only on the bit of that cell. So a T-query algorithm on the array gives a polynomial of degree at most 2T in x [3].

**The minimum cut.** Write W = |x| and N = t². Suppose 2W ≤ τ(t − 1) and 2W ≤ N. If a shore splits a class into s and t − s vertices, its weight is at least τ s(t − s) ≥ τ(t − 1) ≥ 2W. Otherwise the shore is a union of classes, and its weight depends only on W:

| Shore | Weight |
|---|---|
| A ∪ C | 2W |
| A ∪ B | 2(N − W) |
| A ∪ D | 2N |
| one class | N |

All of these are at least 2W. So the weight of a minimum cut is exactly 2W.

**Counting.** Let k = ⌊τ(t − 1)/2⌋ − 1 and take |x| ∈ {k − 1, k + 1}. For t ≥ 9 we have k ≥ 1, 2(k + 1) ≤ τ(t − 1) ≤ N and 4k ≥ τt. An algorithm for the weight of a minimum cut separates the two Hamming weights, so its acceptance polynomial has degree Ω(√(Nk)) [4, Theorem 1.1]. Hence T = Ω(√(t² · τt)) = Ω(n^{3/2} √τ). Small t is covered by the constant. ∎

## Proof of Theorem 3

Use the same construction with a base graph of degree d and edge connectivity d on each class, instead of the clique: a circulant with the d/2 nearest offsets, for even d ≤ t − 1 [5]. Use only the cells (i, j) with j in a fixed set J of d elements of Z_t, so N = td. Degrees still do not depend on x, and m = Θ(td). A shore that splits a class has weight at least τd. The table above is unchanged. With k = ⌊τd/2⌋ − 1, τ ≤ t gives 2(k + 1) ≤ N, so T = Ω(√(td · τd)) = Ω(d√(tτ)) = Ω(m √(τ/n)). ∎

## Proof of Theorem 4

Add a fifth class E, a clique of weight τ, joined to A by exactly 2k fixed edges of weight 1, on distinct pairs. These edges take no queries. Now n = 5t. If |x| = k − 1, the unique minimum cut has shores A ∪ C ∪ E and B ∪ D, of weight 2k − 2. If |x| = k + 1, the unique minimum cut has shore E, of weight 2k. All other cuts are heavier, by the table above and the bound for split classes. So the shores separate the two Hamming weights. ∎

## Machine check

Theorem 1 and Corollary 2 are checked in `lean/MinCutArray/`, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. The files contain no `sorry`, and `MinCutArray.minCut_bound` uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

`CountDegree → ∃ c > 0, ∀ t τ T S (q : QAlg (Vx t) T S), 1 ≤ τ → τ ≤ t → q.Computes τ → c · n √n √τ ≤ T + 1`, with n = 4t.

**The one hypothesis** is `CountDegree`: a real multilinear polynomial of degree D on N bits with values in [0, 1], at least 2/3 on Hamming weight k + 1 and at most 1/3 on Hamming weight k − 1, where 1 ≤ k and 2k + 1 ≤ N, has D = Ω(√(Nk)). This follows from [4, Theorem 1.1] with Δ = 2: the term √(n/Δ) covers k = 1, and the term √(m(n − m))/Δ with m = k − 1 covers k ≥ 2.

**Not machine-checked:** the upper bound of [1], which is cited, and Theorems 3 and 4.

**What the check does not cover.** Lean checks the proof against the definitions in `lean/MinCutArray/Model.lean`. There, an algorithm is a sequence of T + 1 input-independent unitaries on a finite basis, interleaved with T queries, each a fixed unit phase for each pair of basis state and answer, started in a basis state and measured in the basis. The standard oracle is of this form after a change of basis on the answer register. `q.Computes τ` asks for the correct weight with probability at least 2/3 on all graphs with weights between 1 and τ, each with any array that lists its neighbours once.

The script `sim/check_family.py` tests the minimum cut formula, the fixed degrees and Theorems 3 and 4 on small cases by enumerating all cuts.

## References

[1] S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021. arXiv:2011.09823.

[2] C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006.

[3] R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. J. ACM 48(4), 2001.

[4] A. Nayak, F. Wu. The quantum query complexity of approximating the median and related statistics. STOC 1999. arXiv:quant-ph/9804066.

[5] F. Harary. The maximum connectivity of a graph. Proc. Natl. Acad. Sci. USA 48(7), 1962.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
