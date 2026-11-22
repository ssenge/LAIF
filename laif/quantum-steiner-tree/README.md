# Minimum Steiner Tree in polynomial space with a quantum algorithm: the support of the unrolled recursion

Written 22 Nov 2026.

Input: a graph G on n vertices with edge weights and a set K of k terminals. Question: the minimum weight of a tree in G that contains K. In [1] a quantum algorithm in polynomial space and without quantum random access memory is given, by one amplitude amplification with minimum finding over a superposition that indexes all choices of the split recursion of [2] at once [1, Section 3.3, Figure 2, Appendix B]. Its Theorem 3 states the time O*(2^k).

**Observation.** In the superposition of [1], every node of the unrolled recursion carries its own split of its terminal set and its own vertex set A ⊆ V with |A| ≤ ⌈log 1/ε⌉ [1, Figure 2 and Appendix B, levels I to III]. For k a power of two, exact halving and every A empty, the support already has k! index states. The count used for the amplitude amplification in the proofs of Theorems 3 and 4 of [1] is the square root of ∏_{l=1}^{log k} C(k/2^{l−1}, k/2^l), one binomial coefficient per level, which is at most 2^{2k}. The support exceeds this product from k = 4 on and exceeds 2^{2k} from k = 16 on, and the vertex sets add a factor of at least (n + 1)^{k−1} as soon as one vertex per set is allowed.

This hints at a possible counting gap in the proof of Theorem 3 of [1]: the square root of the support of this state is at least √(k!), and at least √(k!) · (n + 1)^{(k−1)/2} once each A may hold one vertex, so the bound O*(2^k) would need a smaller search space or a different argument. The bound 1.812^k with quantum random access memory [3] is not affected.

## Measurements

`sim/support.py` counts the index states by brute force for k = 2, 4, 8, checks the closed form N(k) = C(k, k/2) N(k/2)² = k! up to k = 256, and checks both comparisons above with asserts. Run it with `python support.py` in `sim/`. It exits nonzero on a failed check.

## Limits

- The support is counted for the state as defined in [1]; a different encoding with fewer index states is not ruled out.
- The count is a lower bound: it fixes α = 1/2, η = 0 and A = ∅, and every other choice only enlarges the support.

## References

1. L. Meng, D. S. Novo, A. H. Werner, S. Bhatt. Quantum algorithms for the Minimum Steiner Tree problem with application to Binary Near-Perfect Phylogenies. arXiv:2510.09911.
2. S. E. Dreyfus, R. A. Wagner. The Steiner problem in graphs. Networks 1(3), 1971.
3. M. Miyamoto, M. Iwamura, K. Kise, F. Le Gall. Quantum speedup for the minimum Steiner tree problem. arXiv:1904.03581.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to check the counting, to write the simulation script, and to draft the text.
