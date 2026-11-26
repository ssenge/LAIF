# Quantum time for exact s-t minimum cut on dense graphs

Written 26 Nov 2026.

Given an undirected graph G with n vertices, m edges and integer edge weights in [1, W], and two vertices s and t, the task is to compute the weight λ_st(G) of a minimum s-t cut and one shore of such a cut. Classically this takes m^{1+o(1)} time by almost-linear maximum flow [5], and a randomized classical algorithm needs Ω(m) adjacency-list queries even to decide whether s and t are connected [1, Theorem 19]. A quantum algorithm with Õ(√m n^{5/6} W^{1/3}) queries, so Õ(n^{11/6}) on simple graphs, is given in [1], and Õ(n^{3/2}) queries suffice on simple graphs [7]. Both bounds count queries only. In [1, Remark 9] the computation of a k-strong partition is named as the step that keeps the algorithm from being time efficient, and a time-efficient quantum algorithm is stated as an open problem in [2].

Here the k-strong partition is replaced by the classes of k-edge-connectivity of the same auxiliary graph. They are read off a Gomory-Hu tree, which takes almost-linear time [3].

**Theorem 1.** Let W ≤ n^{O(1)}. In the quantum time model with classical memory readable in superposition, λ_st(G) and the shore of a minimum s-t cut can be computed with high probability in time

Õ(√m n^{5/6} W^{1/3}) + (n^{5/3} W^{2/3})^{1+o(1)}

with adjacency-list access to G, and in time Õ(n^{11/6} W^{1/3}) + (n^{5/3} W^{2/3})^{1+o(1)} with adjacency-matrix access. On simple graphs both are Õ(n^{11/6}).

**Theorem 2.** On simple graphs with adjacency-list access, in the same model, λ_st(G), the shore of a minimum s-t cut and a maximum s-t flow of G can be computed with high probability in time Õ(n + √(mn(f + 1))) + (n(f + 1))^{1+o(1)}, where f = λ_st(G). On dense graphs this is n^{3/2}√(f + 1) · polylog n + (nf)^{1+o(1)}, which is below n² whenever f ≤ n^{1−δ} for a constant δ > 0, and below the bound of Theorem 1 when f ≤ n^{1/3−δ}.

Status: Claim. The boundary bound of Lemma 1 is checked in Lean, and the contraction step by a script with asserts on random small graphs.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Exact s-t minimum cut, simple graphs with m = Θ(n²), time | m^{1+o(1)} = n^{2+o(1)} classically [5]; quantum Õ(n^{11/6}) [1] and Õ(n^{3/2}) [7] queries, with time left open [1, 2] | quantum time Õ(n^{11/6}) |
| Exact s-t minimum cut, integer weights in [1, W], adjacency list, time | m^{1+o(1)} classically [5] | quantum time Õ(√m n^{5/6} W^{1/3}) + (n^{5/3} W^{2/3})^{1+o(1)}, below m^{1+o(1)} when m ≥ n^{5/3+δ} W^{2/3} for a constant δ > 0 |
| Maximum s-t flow (the flow itself), simple graphs, adjacency list, f = λ_st, time | m^{1+o(1)} classically [5]; quantum Õ(n + √(mn(f + 1))) queries [10] | quantum time Õ(n + √(mn(f + 1))) + (n(f + 1))^{1+o(1)}, below n² on dense graphs for f ≤ n^{1−δ} |

## 1. The algorithm

This is Algorithm 1 of [1], which follows the cut-query algorithm of [6], with one step changed. Let ε = (nW)^{−1/3} and k = 3εnW.

1. Find the largest weight W by quantum maximum finding [9].
2. Compute an ε-cut sparsifier H of G with Õ(n/ε²) edges and integer weights at most Õ(ε²nW) by the quantum algorithm of [4], as in [1, Theorem 4].
3. Compute a maximum s-t flow F in H that is integral and has no flow cycles, and let H′ have the weights w_H(e) − F(e). These are integers in [0, Õ(ε²nW)].
4. **(Changed.)** Compute a Gomory-Hu tree T of H′ (edges of weight 0 dropped), delete the tree edges of weight below k, and let P = {A_1, …, A_t} be the vertex sets of the remaining components. Then u and v lie in the same part exactly when λ_{H′}(u, v) ≥ k.
5. Contract every part of P in G to get G′, learn the edges of G that join different parts by quantum enumeration, and compute a minimum a-b cut of G′, where a and b are the parts of s and t. Return its value and the union of the parts on the side of a.

In [1] step 4 uses a k-strong partition instead: a partition whose parts induce k-connected subgraphs of H′.

## 2. Correctness

Let X be the shore of a minimum s-t cut of G. The proof of [1, Claim 12] shows that τ = w_{H′}(δ X) < k, and it uses only the cut sparsifier and the flow. If two vertices u, v of one part of P were on different sides of X, then λ_{H′}(u, v) ≤ τ < k, against the choice of P. So no minimum s-t cut of G splits a part of P. In particular s and t lie in different parts, because λ_{H′}(s, t) ≤ τ < k. The proof of [1, Claim 13] then applies unchanged: λ_ab(G′) = λ_st(G), and the union of the parts on the side of a of a minimum a-b cut of G′ is the shore of a minimum s-t cut of G.

## 3. Size of the contracted graph

**Lemma 1.** Σ_i w_{H′}(δ A_i) < 2k(t − 1).

*Proof.* Call a tree edge light if its weight is below k. Removing a light edge e from T splits V into S_e and V \ S_e, with w_{H′}(δ S_e) = w_T(e) < k. Take an edge xy of H′ with x ∈ A_i and y ∉ A_i. The path from x to y in T leaves A_i through a light edge e incident to A_i, and e separates x from y in T, so xy ∈ δ S_e. Hence δ A_i lies in the union of the cuts δ S_e over the light edges e incident to A_i, and w_{H′}(δ A_i) < k times their number. There are t − 1 light edges, and each is incident to two parts. ∎

This bound takes the place of [1, Theorem 10], which gives k(t − 1) for a k-strong partition. With t ≤ n, the proof of [1, Claim 14] gives Σ_i w_G(δ A_i) = Õ(εn²W): the H′ part is O(kn) = O(εn²W), and the flow part is at most 10 n √(λ_st(H) W_H) = Õ(εn²W) by [6, Lemma 5.4], which holds for any flow without cycles and any partition. So G′ has Õ(εn²W) edges.

## 4. Time

1. Step 1 takes Õ(√m) time, or Õ(n) with the matrix.
2. Step 2 takes Õ(√(mn)/ε) time, or Õ(n^{3/2}/ε) with the matrix [4].
3. Step 3 is a maximum flow on Õ(n/ε²) edges with polynomial integer weights, in (n/ε²)^{1+o(1)} time [5]. Cycles of an integral flow are cancelled in O(m log n) time with dynamic trees [8].
4. Step 4 builds a Gomory-Hu tree of a graph with Õ(n/ε²) edges and integer weights in [1, Õ(ε²nW)], which are polynomial in n, in (n/ε²)^{1+o(1)} time [3, Theorem 1.1]. The parts follow in O(n) time.
5. In step 5 the n part labels are stored in classical memory readable in superposition. An edge slot is marked if it joins two parts. Two label lookups answer a query to the mark. Quantum enumeration with an abort above Õ(εn²W) marks, as in [1, Theorem 2], finds all marked slots in Õ(n√(mεW)) time, or Õ(n²√(εW)) with the matrix. G′ is then built in Õ(εn²W) time, and its minimum a-b cut takes (εn²W)^{1+o(1)} time [5].

With ε = (nW)^{−1/3}, steps 2 and 5 cost Õ(√m n^{5/6} W^{1/3}), or Õ(n^{11/6} W^{1/3}) with the matrix. Steps 3 to 5 also cost (n^{5/3} W^{2/3})^{1+o(1)}, which is n^{5/3+o(1)} for W = 1.

## 5. Proof of Theorem 2

The query algorithm of [10, Theorem 5] builds the forests F_1, …, F_k of a scan-first search with labels capped at k, for k = 1, 2, 4, …, and stops at the first k with λ_st(H_k) < k, where H_k = F_1 ∪ … ∪ F_k has at most kn edges. Then λ_st(H_k) = f, and a maximum s-t flow of H_k is one of G, since the certificate preserves every cut of value below k [10, Lemma 1]. Its query bound is Õ(n + √(mn(f + 1))), and k ≤ 2f + 2.

Each query step of [10, Theorem 4] is a Grover search over the list of the scanned vertex for entries that are not yet found and lead to an unscanned vertex w with r(w) < k. The scan state (the flags, the counters r and, per vertex, the sorted list of found positions) is kept in classical memory readable in superposition and updated classically after each Grover search, so one evaluation of the predicate costs one neighbour query and O(log n) time. The choice of the next vertex, one of largest label, takes O(log n) time with a heap. So the forests take the query bound times O(log n) in time. At stage k the test λ_st(H_k) < k and the flow are computed by an exact maximum flow on H_k, in (kn)^{1+o(1)} time [5]. Summing over the O(log f) stages gives the bound of Theorem 2.

## 6. Measurements

[`sim/gh_classes.py`](sim/gh_classes.py) draws 4000 random simple graphs on 5 to 10 vertices, reweights each edge by a factor in [0.85, 1.15], and computes the exact sparsifier error ε of this reweighting H over all cuts. It runs steps 3 and 4 with k = 3εn, and asserts that no minimum s-t cut of G splits a part, that the contracted graph has the same minimum s-t cut value, and that Lemma 1 holds. In 2609 of the instances the contraction is nontrivial. Run it with `python gh_classes.py` in `sim/` (NetworkX needed).

## 7. Lean

[`lean/StCutClasses.lean`](lean/StCutClasses.lean), with [`lean/StCutClassesAxioms.lean`](lean/StCutClassesAxioms.lean) and its output in [`lean/axioms.txt`](lean/axioms.txt). A rooted tree is given by a root, a parent map and a depth that drops along every parent edge; the side of the edge from v to its parent is the set of vertices below v, and v is light if the weight of the ordered pairs leaving its side is below k. The parts are the fibres of rep, where rep u is the first vertex on the way from u to the root that is the root or light.

- `anc_iff`, `eq_root_of_iterate_eq`, `rep_spec`: the ancestors of u are its iterated parents, only the root lies on a cycle of the parent map, and rep u is the first root or light vertex on the way up.
- `sep`: if rep x ≠ rep y, the side of rep x or of rep y is light and separates x from y (the path argument of Lemma 1).
- `crossing_eq`: the crossing weight is the sum over the parts of the weight of the ordered pairs leaving them.
- `image_rep`, `boundary_le`: there is one part per light vertex plus one, and for symmetric weights the crossing weight is at most 2(k − 1)(t − 1) over ordered pairs, which is Lemma 1 for integer weights.
- `boundary_tight` (non-vacuity): on two vertices joined by an edge of weight one, with k = 2, the vertex 1 is light, t = 2, and the crossing weight 2 attains the bound.

For a Gomory-Hu tree the weight of a side equals the weight of its tree edge, so light vertices are the tree edges of weight below k. This property, and the fact that the parts are then the classes of λ_{H′}(u, v) ≥ k, are taken from [3] and are not formalized.

Lean 4 v4.36.0-rc1, Mathlib rev d875a8de5222f62cf1c2fafc7984588adadc990a.

## 8. Limits

- Memory is classical memory readable in superposition, with unit cost per access, as in [1].
- On simple graphs, a Gomory-Hu tree in quantum time min(m√Δ/δ, √(mn)Δ^{1/4}) · n^{o(1)} ≤ n^{7/4+o(1)} [11] also gives λ_st and a minimum s-t cut, below the bound of Theorem 1 up to the factor n^{o(1)}; Theorem 1 covers integer weights in [1, W] and has only polylogarithmic factors in its first term.
- The weights are integers polynomial in n, as required by [3] and [5].
- Theorem 1 outputs the value and a shore of a minimum cut, not a maximum flow of G; Theorem 2 outputs a flow but is below n² on dense graphs only for f ≤ n^{1−δ}.
- On simple graphs the query bound Õ(n^{3/2}) of [7] stays below the time bound here.
- Not formalized: the algorithms, their correctness and time analysis, and the properties of Gomory-Hu trees; Lean covers Lemma 1 on a given rooted tree.

## References

1. S. Apers, A. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.
2. A. P. Auza. Query algorithms for graph connectivity and st-minimum cut. PhD thesis, University of Technology Sydney, 2023.
3. A. Abboud, R. Kyng, J. Li, D. Panigrahi, M. Probst Gutenberg, T. Saranurak, W. Yuan, W. Yuan. Deterministic almost-linear-time Gomory-Hu trees. arXiv:2507.20354.
4. S. Apers, R. de Wolf. Quantum speedup for graph sparsification, cut approximation and Laplacian solving. FOCS 2020.
5. L. Chen, R. Kyng, Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva. Maximum flow and minimum-cost flow in almost-linear time. FOCS 2022, arXiv:2203.00671.
6. A. Rubinstein, T. Schramm, S. M. Weinberg. Computing exact minimum cuts without knowing the graph. ITCS 2018.
7. T. Lu, R. Ren, S. Liu. Tight quantum query bounds for minimum cut and multicut on dense graphs. arXiv:2611.17845.
8. D. D. Sleator, R. E. Tarjan. A data structure for dynamic trees. Journal of Computer and System Sciences, 1983.
9. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
10. Small cuts and flows with adjacency-array queries. [`laif/small-cuts-array-queries`](../small-cuts-array-queries/), 21 Nov 2026.
11. Quantum time for Gomory-Hu trees of simple graphs. [`laif/quantum-gomory-hu-time`](../quantum-gomory-hu-time/), 26 Nov 2026.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
