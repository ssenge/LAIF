# Minimum Steiner Tree in polynomial space with a quantum algorithm

Written 22 Nov 2026.

Input: a graph G on n vertices with edge weights in {1, …, W} and a set K of k terminals. Question: the minimum weight of a tree in G that contains K.

**Theorem 1.** For every δ > 0 there is a constant f(δ) such that Minimum Steiner Tree has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(2^{(1+δ)k} · n^{f(δ)} · (log W)²).

Status: Claim. The split theorem of [2] is used as stated (Assuming), for terminal sets with at least 1/η terminals, and quantum minimum finding [5], the classical algorithm of [1, Theorem 1.2] and reversible simulation [9] as stated. The exponent of Section 2 is checked by script.

The gain is for large weights: for W ≤ poly(n), the classical polynomial-space algorithm of [7] in time 2^k · n^{O(1)} · W is faster.

## Before and after

| Model | Previous best bound | After |
|---|---|---|
| Classical, polynomial space, general weights | 4^{(1+ε)k} · n^{O(f(ε))} · log W, space n^{O(f(ε))} · log W [1, Theorem 1.3]; 6.751^k · n^{O(1)} · log W [1, Theorem 1.2]; 2^k · n^{O(1)} · W, space n^{O(1)} · log W [7] | |
| Quantum, polynomial space, no quantum random access memory, general weights | O*(2^k) stated in [3, Theorem 3], see Section 3 | **O(2^{(1+δ)k} · n^{f(δ)} · (log W)²)** |
| Quantum, exponential space with quantum random access memory | 1.812^k · poly(n) [4] | |

The new bound is the square root of the classical trade-off of [1, Theorem 1.3], up to the term δ.

Related work: recursive search over a middle vertex gives quantum time O*(2^n) in polynomial space for paths in the hypercube [10], and a framework for divide-and-conquer recurrences of quantum query complexity, for decision problems, is given in [8]. The closest design is the space-time trade-off of [3, Theorem 4], which also unrolls a constant number of levels of the split recursion with the classical polynomial-space algorithm at the leaves. Theorem 1 runs this design as a nested search, so that the cost of each level is the square root of its own search space.

## 1. The algorithm

**The split theorem** [2, Theorem 4, restated as Lemma 3 and Theorem 4 of [4]]. Let η > 0 and s = ⌈log₂(1/η)⌉. For every minimum Steiner tree T for K there is a partition of its edges into a subtree T₁ and a forest, meeting in a set A of at most s vertices, such that K₁ = K ∩ V(T₁) \ A has (1/2 ± η)|K| terminals. T₁ is a minimum Steiner tree for K₁ ∪ A in G, and the forest becomes a minimum Steiner tree for K₂ ∪ {v_A} in the graph G/A in which A is contracted to one vertex v_A, with K₂ = K \ (K₁ ∪ A). Since the union of any tree for K₁ ∪ A and any tree for K₂ ∪ {v_A} in G/A connects K, this gives

W_G(K) = min over K₁ with |K₁| = (1/2 ± η)|K| and A ⊆ V with |A| ≤ s of W_G(K₁ ∪ A) + W_{G/A}(K₂ ∪ {v_A}).

**Nested minimum finding.** Fix η and a depth D, both depending only on δ. A call with m ≥ 1/η terminals at depth below D searches its N ≤ 2^m (n + 1)^s choices (K₁, A) by quantum minimum finding [5]. For each choice it computes the two values on the right, by recursive calls on at most r(m) = ⌊(1/2 + η)m⌋ + s + 1 terminals, and compares their sum with the current threshold. Each child value is computed by L = O(m + s log n + log k) parallel copies of the child call and the minimum of their outputs, which brings its error below 1/(N k)², then copied, and the copies are uncomputed. The minimum is the right combination: every value a call returns is the weight of a connected subgraph that contains its terminals, so an error can only overestimate, and the minimum of L copies is wrong only if every copy is wrong, which happens with probability at most 3^{−L}. The comparison oracle is then exact up to an error that is negligible over the O(√N · log N) calls of minimum finding, and the search runs coherently with its measurements deferred. A call holds its own registers, the contracted graph of its path from the root, and 2L copies of the workspace of a child call, so its workspace is S(m) ≤ 2L · S(r(m)) + poly(n). Over the constant depth D this is (2L)^D · poly(n) = poly(k, n).

**Leaves.** At depth D, or with fewer than 1/η terminals, the call computes the value with the classical polynomial-space algorithm of [1, Theorem 1.2] in time T = 6.751^m · n^{O(1)} · log W and space n^{O(1)} · log W. A reversible simulation [9] runs it in time T^{1+ε} and space O(S log T) for any fixed ε > 0, which is polynomial; moving the algorithm to the machine model of [9] costs a factor poly(n), which enters n^{f(δ)}. The factor log W of T becomes (log W)^{1+ε} ≤ (log W)².

## 2. Analysis

Along a path of calls the terminal counts satisfy m_l ≤ (1/2 + η)^l k + R with R = (s + 1)/(1/2 − η). The square roots of the search spaces multiply along the path, the two children and the L copies contribute a factor (2L · O(log N))^D = poly(k, n), and the searches over A contribute n^{(s/2)D}. The time is therefore

2^{e · k} · poly(k, n) · n^{(s/2)D + O(1)} · (log W)², with e = (1 − (1/2 + η)^D)/(1 − 2η) + (1 + ε) log₂(6.751) · (1/2 + η)^D,

where the first term of e sums m_l/2 over the D search levels and the second is the leaf. Additive terms R per level and the constant cost below 1/η terminals enter only as constant factors. For D large enough and η, ε small enough, e ≤ 1 + δ/2, and the remaining poly(k) factor is at most a constant times 2^{(δ/2)k}. This gives time O(2^{(1+δ)k} · n^{f(δ)} · (log W)²) with f(δ) = (s/2)D + O(D) + O(1), where the O(D) comes from the copies and the O(1) from [1, Theorem 1.2] and the simulation, in polynomial space.

## 3. A remark on [3]

The superposition of [3, Section 3.3, Figure 2 and Appendix B] gives every node of the unrolled recursion its own split of its terminal set and its own vertex set A ⊆ V with |A| ≤ ⌈log 1/ε⌉. For k a power of two and exact halving, the splits of the terminal sets alone already give k! index states, counted with the vertex sets left out. The count used for the amplitude amplification in the proofs of Theorems 3 and 4 of [3] is the square root of ∏_{l=1}^{log k} C(k/2^{l−1}, k/2^l), one binomial coefficient per level, which is at most 2^{2k}. This count of the splits exceeds the product from k = 4 on and exceeds 2^{2k} from k = 16 on. The choices of the vertex sets add further index states.

This hints at a possible counting gap in the proof of Theorem 3 of [3]: the square root of the number of split choices alone is about √(k!), which grows faster than any c^k, so the bound O*(2^k) would need a smaller search space or a different argument. The bound 1.812^k with quantum random access memory [4] is not affected, and Theorem 1 above reaches 2^{(1+δ)k} by nested search instead.

## 4. Measurements

- `sim/nested.py` checks e ≤ 1 + δ/2 in exact rational arithmetic for δ = 0.5, 0.25, 0.1, 0.05 (depth D = 4, 5, 6, 7, with ε = 0.1 and log₂ 6.751 rounded up), so the part of the n-exponent that comes from the searches over A is (s/2)D = 12, 17.5, 27 and 38.5. It also checks the closed-form bound on every m_l and the total along the integer recursion for k up to 10⁶.
- `sim/support.py` counts the index states of Section 3 by brute force for k = 2, 4, 8, checks the closed form N(k) = C(k, k/2) N(k/2)² = k! up to k = 256, and checks both comparisons with asserts.

Run them with `python nested.py` and `python support.py` in `sim/`. Each exits nonzero on a failed check.

## 5. Limits

- The split theorem of [2] is used as stated in [4], for at least 1/η terminals. The constants n^{O(1)} of [1, Theorem 1.2] and of the copies enter f(δ) unevaluated, f(δ) is not optimized, and there is no gate count.
- The gain over [7] is for weights W above poly(n).
- The cut at 1/η terminals is a constant 6.751^{1/η}, large for small δ.
- The count of Section 3 is for the state as defined in [3], with independent split registers at the nodes; a different encoding with fewer index states is not ruled out.

## References

1. F. V. Fomin, P. Kaski, D. Lokshtanov, F. Panolan, S. Saurabh. Parameterized single-exponential time polynomial space algorithm for Steiner Tree. SIAM Journal on Discrete Mathematics 33(1), 2019.
2. B. Fuchs, W. Kern, X. Wang. Speeding up the Dreyfus–Wagner algorithm for minimum Steiner trees. Mathematical Methods of Operations Research 66(1), 2007.
3. L. Meng, D. S. Novo, A. H. Werner, S. Bhatt. Quantum algorithms for the Minimum Steiner Tree problem with application to Binary Near-Perfect Phylogenies. arXiv:2510.09911.
4. M. Miyamoto, M. Iwamura, K. Kise, F. Le Gall. Quantum speedup for the minimum Steiner tree problem. arXiv:1904.03581.
5. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
6. S. E. Dreyfus, R. A. Wagner. The Steiner problem in graphs. Networks 1(3), 1971.
7. D. Lokshtanov, J. Nederlof. Saving space by algebraization. STOC 2010.
8. A. M. Childs, R. Kothari, M. Kovacs-Deak, A. Sundaram, D. Wang. Quantum divide and conquer. arXiv:2210.06419.
9. C. H. Bennett. Time/space trade-offs for reversible computation. SIAM Journal on Computing 18(4), 1989.
10. S. Caroppo, J. Vihrovs, D. Zajakina, A. Zajakins. Quantum time-space tradeoffs for exponential dynamic programming. arXiv:2604.02233.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the analysis and the counting, to write the simulation scripts, and to draft the text.
