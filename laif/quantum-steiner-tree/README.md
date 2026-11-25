# Minimum Steiner Tree in polynomial space with a quantum algorithm

Written 22 Nov 2026.

Input: a graph G on n vertices with edge weights in {1, …, W} and a set K of k terminals. Question: the minimum weight of a tree in G that contains K.

**Theorem 1.** For every δ > 0 there is a constant f(δ) such that Minimum Steiner Tree has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(2^{(1+δ)k} · n^{f(δ)} · (log W)²).

Status: Claim. Assuming the recurrence of [1, Lemma 4.5], proved there from the separation lemma [1, Lemma 4.3] of [6], and using quantum minimum finding [5], the classical algorithm of [1, Theorem 4.2] and reversible simulation [9] as stated. The exponent of Section 2 is checked by script, and the counting of Section 3 is in Lean.

The gain is for large weights: for W ≤ poly(n), the classical polynomial-space algorithm of [7] in time 2^k · n^{O(1)} · W is faster.

## Before and after

| Model | Previous best bound | After |
|---|---|---|
| Classical, polynomial space, general weights | 4^{(1+ε)k} · n^{O(f(ε))} · log W, space n^{O(f(ε))} · log W [1, Theorem 1.3]; 6.751^k · n^{O(1)} · log W [1, Theorem 1.2]; 2^k · n^{O(1)} · W, space n^{O(1)} · log W [7] | |
| Quantum, polynomial space, no quantum random access memory, general weights | O*(2^k) stated in [3, Theorem 3], see Section 3 | **O(2^{(1+δ)k} · n^{f(δ)} · (log W)²)** |
| Quantum, exponential space with quantum random access memory | 1.812^k · poly(n) [4] | |

The algorithm is the polynomial-space algorithm of [1, Section 4.2], which unrolls a constant number of levels of a balanced recurrence and solves the leaves classically, with every level run as a quantum minimum search. The new bound is the square root of its time bound, up to the term δ.

Related work: the space-time trade-off of [3, Theorem 4] also unrolls a constant number of levels of a split recursion, the one of [2] as restated in [4], with classical polynomial-space leaves. Recursive search over a middle vertex gives quantum time O*(2^n) in polynomial space for paths in the hypercube [10], and a framework for divide-and-conquer recurrences of quantum query complexity, for decision problems, is given in [8].

## 1. The algorithm

**The recurrence** [1, Lemma 4.5]. For a set S of vertices and a partition P_S of S, let sf_G(P_S, T) be the minimum weight of a subset Steiner forest for P_S and the terminal set T: a subgraph containing S ∪ T in which every block of P_S lies in one component and the component of every terminal contains a block of P_S. Minimum Steiner Tree is the initial call with S = ∅, as in [1, Section 4.2]. For an even constant c ≥ 4 and α = 2^{−c/2}, and for more than c terminals,

sf_G(P_S, T) = min of sf_G(P₁, T₁) + sf_G(P₂, T₂) over partitions (T₁, T₂) of T with |T₁|, |T₂| ≤ (1/2 + α)|T|, sets S′ ⊇ S with |S′ \ S| ≤ c, and partitions P₁, P₂ of S′ such that P_S refines the join of P₁ and P₂.

The proof in [1] shows both directions: the union of two forests on the right is a subset Steiner forest for (P_S, T) [1, Lemma 4.4], and an optimal forest splits along a separator of at most c vertices from [1, Lemma 4.3] into two forests that appear on the right.

**Nested minimum finding.** Fix c and a depth D, both depending only on δ. Along any path from the root, S grows by at most c per level, so |S| ≤ cD and there are at most B² partitions P₁, P₂ per choice, with B the Bell number of cD, a constant. A call with m > c terminals at depth below D searches its N ≤ 2^m (n + 1)^c B² choices (T₁, S′, P₁, P₂) by quantum minimum finding [5]. For each choice it computes the two values on the right, by recursive calls on at most r(m) = ⌊(1/2 + α)m⌋ terminals, and compares their sum with the current threshold. Each child value is computed by L = O(m + c log n + log k) parallel copies of the child call and the minimum of their outputs, which brings its error below 1/(N k)², then copied, and the copies are uncomputed. The minimum is the right combination: every value a call returns is the weight of a subset Steiner forest for its arguments, so an error can only overestimate, and the minimum of L copies is wrong only if every copy is wrong, which happens with probability at most 3^{−L}. The comparison oracle is then exact up to an error that is negligible over the O(√N · log N) calls of minimum finding, and the search runs coherently with its measurements deferred. A call holds its own registers, the set S′ and the partitions of its path from the root, and 2L copies of the workspace of a child call, so its workspace is S(m) ≤ 2L · S(r(m)) + poly(n). Over the constant depth D this is (2L)^D · poly(n) = poly(k, n).

**Leaves.** At depth D, or with at most c terminals, the call computes sf_G(P_S, T) with the classical polynomial-space algorithm of [1, Theorem 4.2], for a partition of at most cD vertices, in time T = 7.97^m · n^{O(1)} · log(nW) and space n^{O(1)} · log(nW) · log k. A reversible simulation [9] runs it in time T^{1+ε} and space O(S log T) for any fixed ε > 0, which is polynomial; moving the algorithm to the machine model of [9] costs a factor poly(n), which enters n^{f(δ)}. The factor log(nW) of T becomes (log(nW))^{1+ε} ≤ (log(nW))².

## 2. Analysis

Along a path of calls the terminal counts satisfy m_l ≤ (1/2 + α)^l k. The square roots of the search spaces multiply along the path, the two children and the L copies contribute a factor (2L · O(log N))^D = poly(k, n), and the searches over S′ contribute n^{(c/2)D}. The time is therefore

2^{e · k} · poly(k, n) · n^{(c/2)D + O(1)} · (log(nW))², with e = (1 − (1/2 + α)^D)/(1 − 2α) + (1 + ε) log₂(7.97) · (1/2 + α)^D,

where the first term of e sums m_l/2 over the D search levels and the second is the leaf. For D and c large enough and ε small enough, e ≤ 1 + δ/2, and the remaining poly(k) factor is at most a constant times 2^{(δ/2)k}. This gives time O(2^{(1+δ)k} · n^{f(δ)} · (log W)²) with f(δ) = (c/2)D + O(D) + O(1), where the O(D) comes from the copies and the O(1) from [1, Theorem 4.2] and the simulation, in polynomial space.

## 3. A remark on [3]

The superposition of [3, Section 3.3, Figure 2 and Appendix B] gives every node of the unrolled recursion its own split of its terminal set and its own vertex set A ⊆ V with |A| ≤ ⌈log 1/ε⌉. For k a power of two and exact halving, the splits of the terminal sets alone already give k! index states, counted with the vertex sets left out. The count used for the amplitude amplification in the proofs of Theorems 3 and 4 of [3] is the square root of ∏_{l=1}^{log k} C(k/2^{l−1}, k/2^l), one binomial coefficient per level, which is at most 2^{2k}. This count of the splits exceeds the product from k = 4 on and exceeds 2^{2k} from k = 16 on. The choices of the vertex sets add further index states.

This hints at a possible counting gap in the proof of Theorem 3 of [3]: the square root of the number of split choices alone is about √(k!), which grows faster than any c^k, so the bound O*(2^k) would need a smaller search space or a different argument. The bound 1.812^k with quantum random access memory [4] is not affected, and Theorem 1 above reaches 2^{(1+δ)k} by nested search instead.

## 4. Measurements

- `sim/nested.py` checks e ≤ 1 + δ/2 in exact rational arithmetic for δ = 0.5, 0.25, 0.1, 0.05 (c = 12, 16, 20, 24 and depth D = 4, 5, 6, 7, with log₂ 7.97 rounded up), so the part of the n-exponent that comes from the searches over S′ is (c/2)D = 24, 40, 60 and 84. It also checks m_l ≤ (1/2 + α)^l k and the total along the integer recursion for k up to 10⁶.
- `sim/support.py` counts the index states of Section 3 by brute force for k = 2, 4, 8, checks the closed form N(k) = C(k, k/2) N(k/2)² = k! up to k = 256, and checks both comparisons with asserts.

Run them with `python nested.py` and `python support.py` in `sim/`. Each exits nonzero on a failed check.

## 5. Lean

`lean/SteinerCount.lean` proves, with only the standard axioms (`lean/axioms.txt`), for k = 2^m terminals, with N(m) the number of index states of the terminal splits under exact halving, N(m + 1) = C(2^{m+1}, 2^m) · N(m)², and S(m) the product of one binomial coefficient per level, S(m + 1) = C(2^{m+1}, 2^m) · S(m):

- `N_eq_factorial`: N(m) = (2^m)!, that is k! index states.
- `S_le`: S(m) ≤ 4^{2^m}, so the product is at most 2^{2k}.
- `four_pow_lt_N`: 4^{2^m} < N(m) for m ≥ 4, so the count exceeds 2^{2k} from k = 16 on.
- `N_three_lt_four_pow`, `S_two`, `N_two`: N(3) = 8! < 4^8, so the range m ≥ 4 of `four_pow_lt_N` is needed and the bound is not met for all m; S(2) = 12 and N(2) = 24 = 4!.

Lean 4 v4.36.0-rc1 with Mathlib at revision d875a8de5222f62cf1c2fafc7984588adadc990a. Run `lake exe cache get` and then `lake build` in `lean/`.

Not formalized: Theorem 1, the comparison of the count with the product for 4 ≤ k < 16 (checked by script), and the correspondence between the state of [3] and the recursion for N.

## 6. Limits

- The recurrence of [1, Lemma 4.5] and the leaf algorithm of [1, Theorem 4.2] are used as stated there. The constants n^{O(1)} of [1, Theorem 4.2] and of the copies enter f(δ) unevaluated, f(δ) is not optimized, and there is no gate count.
- The gain over [7] is for weights W above poly(n).
- The count of Section 3 is for the state as defined in [3], with independent split registers at the nodes; a different encoding with fewer index states is not ruled out.

## References

1. F. V. Fomin, P. Kaski, D. Lokshtanov, F. Panolan, S. Saurabh. Parameterized single-exponential time polynomial space algorithm for Steiner Tree. SIAM Journal on Discrete Mathematics 33(1), 2019.
2. B. Fuchs, W. Kern, X. Wang. Speeding up the Dreyfus–Wagner algorithm for minimum Steiner trees. Mathematical Methods of Operations Research 66(1), 2007.
3. L. Meng, D. S. Novo, A. H. Werner, S. Bhatt. Quantum algorithms for the Minimum Steiner Tree problem with application to Binary Near-Perfect Phylogenies. arXiv:2510.09911.
4. M. Miyamoto, M. Iwamura, K. Kise, F. Le Gall. Quantum speedup for the minimum Steiner tree problem. arXiv:1904.03581.
5. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
6. F. V. Fomin, F. Grandoni, D. Lokshtanov, S. Saurabh. Sharp separation and applications to exact and parameterized algorithms. Algorithmica 63, 2012.
7. D. Lokshtanov, J. Nederlof. Saving space by algebraization. STOC 2010.
8. A. M. Childs, R. Kothari, M. Kovacs-Deak, A. Sundaram, D. Wang. Quantum divide and conquer. arXiv:2210.06419.
9. C. H. Bennett. Time/space trade-offs for reversible computation. SIAM Journal on Computing 18(4), 1989.
10. S. Caroppo, J. Vihrovs, D. Zajakina, A. Zajakins. Quantum time-space tradeoffs for exponential dynamic programming. arXiv:2604.02233.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the analysis and the counting, to write the simulation scripts, and to draft the text.
