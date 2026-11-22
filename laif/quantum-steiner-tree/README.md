# Minimum Steiner Tree in polynomial space with a quantum algorithm

Written 22 Nov 2026.

Input: a graph G on n vertices with edge weights in {1, …, W} and a set K of k terminals. Question: the minimum weight of a tree in G that contains K.

**Theorem 1.** For every δ > 0 there is a constant f(δ) such that Minimum Steiner Tree has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(2^{(1+δ)k} · n^{f(δ)} · log W).

Status: Claim. The split theorem of [2] is used as stated (Assuming), for terminal sets with at least 1/η terminals, and quantum minimum finding [5] and search with bounded-error inputs [8] as stated. The cost model of Section 2 is evaluated by script.

The gain is for large weights: for W ≤ poly(n), the classical polynomial-space algorithm of [7] in time 2^k · n^{O(1)} · W is faster.

## Before and after

| Model | Previous best bound | After |
|---|---|---|
| Classical, polynomial space, general weights | 4^{(1+ε)k} · n^{O(f(ε))} · log W, space n^{O(f(ε))} · log W [1, Theorem 1.3]; 6.751^k · n^{O(1)} · log W [1, Theorem 1.2]; 2^k · n^{O(1)} · W, space n^{O(1)} · log W [7] | |
| Quantum, polynomial space, no quantum random access memory, general weights | O*(2^k) stated in [3, Theorem 3], see Section 3 | **O(2^{(1+δ)k} · n^{f(δ)} · log W)** |
| Quantum, exponential space with quantum random access memory | 1.812^k · poly(n) [4] | |

The new bound is the square root of the classical trade-off of [1, Theorem 1.3], up to the term δ.

## 1. The algorithm

**The split theorem** [2, Theorem 4, restated as Lemma 3 and Theorem 4 of [4]]. Let η > 0 and s = ⌈log₂(1/η)⌉. For every minimum Steiner tree T for K there is a partition of its edges into a subtree T₁ and a forest, meeting in a set A of at most s vertices, such that K₁ = K ∩ V(T₁) \ A has (1/2 ± η)|K| terminals. T₁ is a minimum Steiner tree for K₁ ∪ A in G, and the forest becomes a minimum Steiner tree for K₂ ∪ {v_A} in the graph G/A in which A is contracted to one vertex v_A, with K₂ = K \ (K₁ ∪ A). Since the union of any tree for K₁ ∪ A and any tree for K₂ ∪ {v_A} in G/A connects K, this gives

W_G(K) = min over K₁ with |K₁| = (1/2 ± η)|K| and A ⊆ V with |A| ≤ s of W_G(K₁ ∪ A) + W_{G/A}(K₂ ∪ {v_A}).

**Nested minimum finding.** A call with m terminals searches its at most 2^m (n + 1)^s choices (K₁, A) by quantum minimum finding [5]. For each choice it computes the two values on the right one after the other, by recursive calls on at most r(m) = ⌊(1/2 + η)m⌋ + s + 1 terminals, and adds them. Each recursive value is computed by a constant number c of parallel copies and the median of their outputs, which brings its error below 1/10, and the comparison of the sum with the current threshold is then a bounded-error oracle. Minimum finding [5], with search with bounded-error inputs [8] in each of its O(log N) threshold stages, needs O(√N · log N) calls to such an oracle for N choices and has bounded error. Every call runs coherently, with its measurements deferred and its work uncomputed. A call holds its choice, the contracted graph of its path from the root, the weights and the c copies of each of its two children, so its workspace is S(m) ≤ 2c · S(r(m)) + poly(n). Over the depth D = O(log k) this gives (2c)^D · poly(n) = poly(k, n).

**Cutoff.** At m ≤ m₀ = max(⌈log₂ n⌉, M(η)) terminals, with M(η) = max(⌈2(s + 2)/(1 − 2η)⌉, ⌈1/η⌉) the constant above which r(m) < m and the range (1/2 ± η)m contains an integer, the call computes the value classically by the subset dynamic program of [6] in time 3^m · poly(n) and space 2^m · n, which is polynomial. The cutoff is what keeps the polynomial factor bounded: below it no further levels of search over A ⊆ V are needed.

## 2. Analysis

With L(m) = 2cC · (m + s log₂(n + 1)) per level, where C is the constant of minimum finding, the cost satisfies

log₂ Q(m) ≤ m/2 + (s/2) log₂(n + 1) + log₂ L(m) + log₂ Q(r(m)), and log₂ Q(m) ≤ m log₂ 3 + O(log n) for m ≤ m₀.

The terminal counts along a path of calls shrink by the factor 1/2 + η plus s + 1, so they sum to at most k/(1/2 − η) + O(sD), where D = O(log(k/m₀)) is the depth. The square root halves this, which gives 2^{k/(1−2η) + O(sD)}. The search over A contributes n^{s/2} per level, so n^{(s/2)D} in total. Write k = t · log₂ n. For t ≤ t₀ the depth is at most a constant D₀(t₀, η), and the factors are n^{O(s D₀)} and (k + log n)^{O(D₀)}, both polynomial. For t > t₀ the factor n^{(s/2)D} = 2^{k · O(s log t / t)} is at most 2^{(δ/3)k} once t₀ is large enough, and the factors L(m) contribute (O(k + log n))^D = 2^{O(log² k)}, which is 2^{o(k)}. Choosing η with 1/(1 − 2η) ≤ 1 + δ/3 then gives time O(2^{(1+δ)k} · n^{f(δ)}), times log W for the arithmetic on weights.

## 3. A remark on [3]

The superposition of [3, Section 3.3, Figure 2 and Appendix B] gives every node of the unrolled recursion its own split of its terminal set and its own vertex set A ⊆ V with |A| ≤ ⌈log 1/ε⌉. For k a power of two and exact halving, the splits of the terminal sets alone already give k! index states, counted with the vertex sets left out. The count used for the amplitude amplification in the proofs of Theorems 3 and 4 of [3] is the square root of ∏_{l=1}^{log k} C(k/2^{l−1}, k/2^l), one binomial coefficient per level, which is at most 2^{2k}. This count of the splits exceeds the product from k = 4 on and exceeds 2^{2k} from k = 16 on. The choices of the vertex sets add further index states.

This hints at a possible counting gap in the proof of Theorem 3 of [3]: the square root of the number of split choices alone is about √(k!), which grows faster than any c^k, so the bound O*(2^k) would need a smaller search space or a different argument. The bound 1.812^k with quantum random access memory [4] is not affected, and Theorem 1 above reaches 2^{(1+δ)k} by nested search instead.

## 4. Measurements

- `sim/nested.py` evaluates the recursion of Section 2 for δ = 0.5, 0.25, 0.1, 0.05 on a grid of k up to 10⁷ and n up to 2⁴⁰, and checks log₂ Q(k) ≤ (1 + δ)k + f · log₂ n for n ≥ 16 with f at most 38, 29, 37 and 77 (with c = 8 and C = 64), the space factor (2c)^D ≤ k^6, the shrinking condition and integer split sizes above M(η), and that the exponent per terminal tends to 1/(1 − 2η).
- `sim/support.py` counts the index states of Section 3 by brute force for k = 2, 4, 8, checks the closed form N(k) = C(k, k/2) N(k/2)² = k! up to k = 256, and checks both comparisons with asserts.

Run them with `python nested.py` and `python support.py` in `sim/`. Each exits nonzero on a failed check.

## 5. Limits

- The split theorem of [2] is used as stated in [4], and the constant f(δ) is not optimized. The values above come from a cost model with fixed constants c and C, evaluated on a grid; the bound for all k and n rests on the argument of Section 2.
- The polynomial factor n^{f(δ)} is large for small δ, and there is no gate count.
- The count of Section 3 is for the state as defined in [3], with independent split registers at the nodes; a different encoding with fewer index states is not ruled out.

## References

1. F. V. Fomin, P. Kaski, D. Lokshtanov, F. Panolan, S. Saurabh. Parameterized single-exponential time polynomial space algorithm for Steiner Tree. SIAM Journal on Discrete Mathematics 33(1), 2019.
2. B. Fuchs, W. Kern, X. Wang. Speeding up the Dreyfus–Wagner algorithm for minimum Steiner trees. Mathematical Methods of Operations Research 66(1), 2007.
3. L. Meng, D. S. Novo, A. H. Werner, S. Bhatt. Quantum algorithms for the Minimum Steiner Tree problem with application to Binary Near-Perfect Phylogenies. arXiv:2510.09911.
4. M. Miyamoto, M. Iwamura, K. Kise, F. Le Gall. Quantum speedup for the minimum Steiner tree problem. arXiv:1904.03581.
5. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
6. S. E. Dreyfus, R. A. Wagner. The Steiner problem in graphs. Networks 1(3), 1971.
7. D. Lokshtanov, J. Nederlof. Saving space by algebraization. STOC 2010.
8. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003, arXiv:quant-ph/0304052.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the analysis and the counting, to write the simulation scripts, and to draft the text.
