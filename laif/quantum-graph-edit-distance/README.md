# Graph Edit Distance with a quantum algorithm in polynomial space

Written 24 Nov 2026.

The Graph Edit Distance of two graphs G and H is the minimum cost of a sequence of node and edge substitutions, insertions and deletions that turns G into H. With reasonable edit costs (a substitution never costs more than a deletion plus an insertion) and |V(G)| = |V(H)| = n, it is the minimum over all bijections φ: V(G) → V(H) of the induced node and edge edit costs [1, Definitions 1 to 4]; the general case reduces to this one in polynomial time [1, Appendix A]. The problem contains Subgraph Isomorphism, Maximum Common Subgraph and, with a cycle as G, the Travelling Salesman Problem.

A separator recursion of [1] solves it in time (4 + ε)^n and polynomial space when G has small balanced separators. Here the same recursion is run with nested quantum minimum finding [2].

**Theorem 1.** Let ε > 0, β ∈ (0, 1) and s(n) = o(n/log² n) non-decreasing, and let G be (β, s)-balanced-separable: every induced subgraph G[X] has a β-separator of size at most s(|X|) [1, Definitions 6 and 7]. Then the Graph Edit Distance of G and any graph H on the same number n of vertices, with reasonable rational edit costs of polynomial bit length, and an optimal node map, are computed by a quantum algorithm with bounded error in time O((2 + ε)^n), with poly(n) qubits and no quantum random access memory.

**Corollary 2.** The bound holds when G belongs to a hereditary class with strictly sublinear balanced separators [1, Corollary 22], in particular when G is planar, K_h-minor-free for a fixed h, or of bounded treewidth [1, Corollary 26]. It also holds for the Quadratic Assignment Problem of size n with symmetric distances whose network of nonzero flows is (α, O(n^{1 − δ}))-balanced-separable for constants α ∈ [1/2, 1) and δ > 0, through the reduction of [1, Theorem 28].

Status: Claim. The recursion and its correctness are those of [1, Algorithm 1, Theorem 17], used as stated (Assuming); the quantum part is nested minimum finding [2] with error reduction. The decomposition that the nesting evaluates is checked against brute force by script, and so are the exponents.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Graph Edit Distance, G (β, s)-balanced-separable with s(n) = o(n/log² n) (planar, K_h-minor-free, bounded treewidth), H arbitrary, polynomial space | (4 + ε)^n classically [1]; quantum search over all n! node maps, n^{n/2 + o(n)} | **(2 + ε)^n**, no quantum random access memory |
| Quadratic Assignment, symmetric distances, flow network (α, O(n^{1 − δ}))-balanced-separable, polynomial space | (4 + ε)^n classically [1] | **(2 + ε)^n** |

All bounds hide polynomial factors. To our knowledge no quantum bound below n^{n/2} for exact Graph Edit Distance on these classes has been stated before.

## 1. The recursion of [1]

A call on (G′, H′, c) with |V(G′)| = |V(H′)| = m ≤ 1 is solved directly. Otherwise it computes a small balanced separator S of G′, with G′ − S the disjoint union of G′[V₁] and G′[V₂], and returns

R(G′, H′, c) = min over ψ and W₁ of [ c_S(ψ) + R(G′[V₁], H′[W₁], c^ψ) + R(G′[V₂], H′[W₂], c^ψ) + c_cut(W₁) ],

where ψ ranges over the injections S → V(H′), W₁ over the subsets of V(H′) − ψ(S) of size |V₁|, and W₂ is the rest [1, Algorithm 1]. Here c_S(ψ) is the cost induced on G′[S] and H′[ψ(S)], the adapted node costs c^ψ(v, w) = c(v, w) + Σ_{s ∈ S} c_E({s, v}, {ψ(s), w}) absorb the edges at the separator, and c_cut(W₁) is the cost of inserting the edges of H′ between W₁ and W₂, since G′ has no edges between V₁ and V₂ [1, Lemmas 9, 12 and 16]. The separator is found deterministically by exhaustive search over sets of size at most c_μ · s(m), with c_μ = 2^{⌈log_β μ⌉}, which gives balance α = 1/2 + μ [1, Lemma 19]. At depth i the instance has m ≤ n_i = ⌊αⁱ n⌋ vertices, and the depth is O(log n).

## 2. The quantum algorithm

Each call runs quantum minimum finding [2] over the at most N_i ≤ n_i^{c_μ s(n_i)} · 2^{n_i} pairs (ψ, W₁). For a pair in superposition it computes the separator, the adapted costs and the cut cost reversibly in time n_i^{O(s(n_i))}, and the two recursive values by recursive calls of the same kind. Every value that a comparison uses is the median of O(n) independent runs, which brings its error below 2^{−2n}; the runs are uncomputed after the comparison. All calls of one depth have the same running time after padding to the bound of that depth. With error at most 2^{−2n} per value, the amplitude error of each of the √N_i · polylog calls is at most 2^{−n}, so each level succeeds with probability 1 − 2^{−Ω(n)}.

The time Q_i at depth i satisfies Q_i ≤ √N_i · O(n) · (2 Q_{i+1} + n_i^{O(s(n_i))}). Unrolling over the O(log n) levels gives

Q_0 ≤ 2^{Σ_i n_i / 2} · Π_i n_i^{O(s(n_i))} · (O(n))^{O(log n)} ≤ 2^{n / (2(1 − α))} · 2^{O(s(n) log² n)} · 2^{O(log² n)}.

With s(n) = o(n/log² n) the last two factors are 2^{o(n)}. Choosing μ so that 2^{1/(2(1/2 − μ))} < 2 + ε/2, as in [1, Theorem 20] with the exponent halved, gives (2 + ε)^n for large n. The workspace is a stack of O(log n) frames of polynomial size, so the algorithm uses poly(n) qubits. An optimal node map is read off by the same search with the recorded minimizers.

## 3. Measurements

[`sim/ged.py`](sim/ged.py) checks two things. First, the decomposition of Section 1 with the adapted node costs, on random instances with n ≤ 7 where G is a path, cycle, tree, ladder or sparse random graph, H is random and the costs are random and reasonable: the recursion equals brute force over all bijections on 95 instances. Second, the exponents: the sums of the classical and quantum logarithmic counts over the levels n_i = αⁱ n, with planar separators s(m) = √m, for α = 0.51, 0.55, 0.6, approach n/(1 − α) and n/(2(1 − α)), with the excess shrinking as n grows up to 10¹², and the choice of μ for given ε. Run it with `python ged.py` in `sim/`.

## 4. Limits

- The classes are those of [1]: only G needs small separators; H is arbitrary. For two trees the classical algorithm of [3] runs in time 2^{2n/3}, which is faster.
- With a cycle as G the problem is the Travelling Salesman Problem, and the bound is the 2^{n + o(n)} of quantum divide and conquer, not lower.
- The recursion of [1] is used as stated. The factors 2^{o(n)} are absorbed into (2 + ε)^n only for large n.
- Not formalized in Lean.

## References

1. L. Bülte, P. Mayer, L. Müller, P. Mutzel. A separator-based algorithm for the Graph Edit Distance problem. arXiv:2608.04583.
2. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
3. T. Akutsu, T. Tamura, D. Fukagawa, A. Takasu. Efficient exponential-time algorithms for edit distance between unordered trees. Journal of Discrete Algorithms 25, 2014.

## Use of AI

The algorithm, the proofs, the scripts and this text were produced with the help of Claude Opus 5.5.
