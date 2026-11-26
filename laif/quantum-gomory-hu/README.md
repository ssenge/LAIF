# All-pairs minimum cut in the adjacency-matrix model

Written 26 Nov 2026.

A Gomory–Hu tree of an undirected graph G on n vertices is a weighted tree on the same vertices such that, for every pair u, v, the smallest edge weight on the tree path from u to v equals λ(u, v), the value of a minimum u–v cut in G. Here G is simple and unweighted, and it is given by its adjacency matrix: a query names a pair {u, v} and returns whether uv is an edge. Reading the whole matrix costs O(n²) queries, and with it any Gomory–Hu tree can be computed offline. Global minimum cut has quantum query complexity Θ̃(n^{3/2}) in this model [1, 2].

**Theorem 1.** Every bounded-error quantum algorithm that, given the adjacency matrix of a simple graph on n vertices, outputs all values λ(u, v) makes Ω(n²) queries. The same holds for the values λ(r, v), v ≠ r, from a single fixed source r, and therefore for computing a Gomory–Hu tree. The bound holds on graphs with at least n²/16 edges in which every value equals min(deg u, deg v). So the quantum query complexity of these problems in the adjacency-matrix model is Θ(n²).

Status: Claim, with the cut lemma and the recovery step checked by script.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| All-pairs and single-source minimum cut values, Gomory–Hu tree, adjacency matrix, simple graphs | O(n²) by reading the matrix; no quantum lower bound for all pairs known to us; global minimum cut Θ̃(n^{3/2}) [1, 2] | Ω(n²), so Θ(n²), on dense graphs |

## The hard family

Let 3 ≤ s < h and n = 2(h + s). The vertex set is L ∪ R with L = L₁ ∪ L₂ and R = R₁ ∪ R₂, where |L₁| = |R₁| = s and |L₂| = |R₂| = h. The sets L and R are cliques, every vertex of L₂ is adjacent to every vertex of R₂, and B ⊆ L₁ × R₁ is an arbitrary set of further edges. Write N = h + s and Δ = 2h + s − 1. Vertices of L₂ ∪ R₂ have degree Δ, and a vertex x ∈ L₁ ∪ R₁ has degree N − 1 + deg_B(x) ≤ h + 2s − 1 < Δ.

**Lemma 2.** Every cut (S, T) with |S| ≥ 2 and |T| ≥ 2 has at least Δ crossing edges.

*Proof.* Let a = |S ∩ L| and b = |S ∩ R|. The clique on L contributes a(N − a) crossing edges and the clique on R contributes b(N − b).
- If 1 ≤ a ≤ N − 1 and 1 ≤ b ≤ N − 1, the value is at least 2(N − 1) = 2h + 2s − 2 ≥ Δ.
- Let S split L but not R. Exchanging S and T if needed, S ∩ R is empty, so S ⊆ L and a ≥ 2. For 2 ≤ a ≤ N − 2 the value is at least a(N − a) ≥ 2N − 4 ≥ Δ, since s ≥ 3. For a = N − 1, the side S misses one vertex w of L, and the value is at least (N − 1) + h(h − 1) ≥ Δ, counting the edges from L₂ ∖ {w} to R₂.
- If S splits neither L nor R, then S = L or S = R, and the value is at least |L₂ × R₂| = h² ≥ Δ.
- If S splits R but not L, the same argument applies with L and R exchanged. ∎

For u ≠ v, the cuts ({u}, V ∖ {u}) and ({v}, V ∖ {v}) have values deg u and deg v, and every other u–v cut has value at least Δ ≥ max(deg u, deg v) by Lemma 2. Hence λ(u, v) = min(deg u, deg v) for every pair. Fix r ∈ L₂. For x ∈ L₁, deg x < Δ = deg r, so λ(r, x) = deg x, and

|B| = Σ_{x ∈ L₁} (λ(r, x) − (N − 1)).

*Proof of Theorem 1.* The single-source values from r determine |B|, where B ranges over all subsets of the s² pairs of L₁ × R₁ and every other entry of the matrix is fixed. Deciding whether a string of M = s² bits has Hamming weight t or t + 1, with t = ⌊M/2⌋, needs Ω(√((t + 1)(M − t))) = Ω(M) quantum queries, by the adversary bound of [3] applied to the pairs of strings that differ in one bit. With h = ⌈n/4⌉ + 1 and s = n/2 − h, so s ≥ n/4 − 2 (n ≥ 24 even), this is Ω(n²) for even n ≥ 24; for odd n an isolated vertex is added, which changes no value λ(u, v) between the other vertices. The graph has at least h² ≥ n²/16 edges. ∎

The proof uses only that degrees are expensive in the adjacency-matrix model. In the adjacency-array model, where the degree of a vertex is one query, every value of this family is known after n queries, and Theorem 1 says nothing about that model.

## Numerical checks

`sim/matrix_lb.py` (output in `sim/out_matrix_lb.txt`) checks Lemma 2 by brute force over all cuts for n = 16 and random B, computes Gomory–Hu trees for random B at n = 20, 26 and 40, asserts that every value equals min(deg u, deg v) and that |B| is recovered from the single-source values, and checks that the claim fails once the block L₂ × R₂ is removed.

## Not formalized

Lemma 2 and the reduction are written proofs, not checked in Lean.

## References

[1] S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021. arXiv:2011.09823.

[2] T. Lu, R. Ren, S. Liu. Tight quantum query bounds for minimum cut and multicut on dense graphs. arXiv:2611.17845.

[3] A. Ambainis. Quantum lower bounds by quantum arguments. J. Comput. Syst. Sci. 64(4), 2002. arXiv:quant-ph/0002066.

## Use of AI

The proofs, the scripts and this text were produced with the help of Claude Opus 5.5.
