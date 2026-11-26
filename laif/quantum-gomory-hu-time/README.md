# Quantum time for Gomory-Hu trees of simple graphs

Written 26 Nov 2026.

A Gomory-Hu tree of an undirected graph G on n vertices is a weighted tree on the same vertices such that, for every pair u, v, the smallest edge weight on the tree path from u to v equals λ(u, v), the value of a minimum u-v cut, and the two sides left after removing that edge form a minimum u-v cut. Here G is simple, with m edges, minimum degree δ and maximum degree Δ, and it is given in the adjacency-array model (degree and neighbour queries). Classically a Gomory-Hu tree takes m^{1+o(1)} time [2], and the classical randomized query complexity of the global minimum cut alone is Θ̃(m) [3]. A quantum algorithm with Õ(min(m√Δ/δ, √(mn)Δ^{1/4})) queries, so Õ(n^{7/4}) on every graph, is given in [1] ([`quantum-gomory-hu`](../quantum-gomory-hu/)), with its offline computation left unbounded.

Here the offline steps of [1] are carried out in almost-linear time. The cluster decomposition becomes a deterministic weighted expander decomposition with vertex demands [4], and the final tree a deterministic almost-linear Gomory-Hu tree [2].

**Theorem 1.** In the quantum time model with classical memory readable in superposition, a Gomory-Hu tree of G can be computed with high probability in time

(m √Δ / δ) · n^{o(1)} and (√(mn) · Δ^{1/4}) · n^{o(1)},

whichever is smaller. More generally, for every threshold D ≥ √Δ the time is (vol(L_D) + √(mn) + m√Δ/D) · n^{o(1)}, where vol(L_D) is the sum of the degrees below D. This is n^{7/4+o(1)} on every graph, (√(mn))^{1+o(1)} when Δ = O(δ), and n^{3/2+o(1)} on dense near-regular graphs, where it matches the quantum query lower bound Ω(n^{3/2}) for one global minimum cut [5] up to the factor n^{o(1)}.

Status: Claim. The merge step that reduces the tree to the original vertices is checked in Lean, and the whole reduction by a script with asserts.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Gomory-Hu tree of a simple graph, adjacency array, time | m^{1+o(1)} classically [2], n^{2+o(1)} on dense graphs; quantum Õ(n^{7/4}) queries [1] | quantum time n^{7/4+o(1)} on every graph, below m^{1+o(1)} when m ≥ n^{7/4+δ}; n^{3/2+o(1)} on dense near-regular graphs |

## 1. The algorithm

The algorithm is Theorem 1 of [1] with steps 2 and 5 made explicit. Let φ = 200Δ/δ² (or 200Δ/D² for the threshold version), and let γ = n^{o(1)} be the approximation factor of [4, Corollary 2.5] with r chosen so that (mU)^{O(1/r)} and (log m)^{O(r⁴)} are both n^{o(1)}.

1. Query all degrees and compute a (1 ± 1/10) spectral sparsifier H of G with Õ(n) edges by the quantum algorithm of [6], in time Õ(√(mn)). Its weights are positive integers bounded by a polynomial in n, as in [7, Theorem 4].
2. **(Explicit.)** Give every vertex x the demand d(x) = d_H(x), its full weighted degree in H, and compute a (γφ, φ)-expander decomposition of H by [4, Corollary 2.5], separately in every connected component. For every cluster C, H[C] then has d|_C-sparsity at least φ, that is, e_H(X, C ∖ X) ≥ φ · min(vol_H(X), vol_H(C ∖ X)) for every X ⊆ C with full volumes vol_H, which is the condition of step 2 of [1]. The weight between clusters is at most γφ · vol_H(V). This takes Õ(n) · n^{o(1)} time. If γφ > 1, the algorithm reads the graph instead.
3. Store the cluster label of every vertex in classical memory readable in superposition. Estimate d_C(x)/d_x for every vertex by amplitude estimation, as in [1], form the cores C″ = C ∖ Z_C, and store the core label of every vertex (none for the vertices of Z_C).
4. For every vertex x, find all neighbours outside the core of x by Grover search, as in [1]; each query to the predicate costs one neighbour query and two label lookups.
5. **(Explicit.)** Build the star model G̃ of [1] and compute a Gomory-Hu tree T of G̃ on all its vertices, including one extra vertex K per core, in m̃^{1+o(1)} time [2, Theorem 1.1], where m̃ is the number of edges of G̃. Then merge every node of T that holds no vertex of V into its neighbour along its heaviest tree edge, until every node holds exactly one vertex of V. The result is a Gomory-Hu tree of G̃ for the terminals V, and by [1] one of G.

The threshold version reads the neighbours of the vertices of degree below D and runs steps 2 to 5 on V ∖ L_D, with the demands still the full weighted degrees in H, as in [1].

## 2. Correctness

Steps 1, 3 and 4 are those of [1]. Step 2 gives exactly the guarantee that the proof of [1, Lemma 3] uses: for every cluster C and every X ⊆ C, e_H(X, C ∖ X) ≥ φ min(vol_H(X), vol_H(C ∖ X)) with the volumes of H. So Lemma 3 and the star model of [1] hold unchanged.

For step 5, let y be a node of T that holds no vertex of V, and let e* be its heaviest tree edge, to z. Take two terminals u, v. If their tree path avoids y, merging changes nothing on it. If it passes y through edges e₁ and e₂, then either e* is one of them and the path loses e*, whose weight is at least that of the other one, or the path keeps e₁ and e₂, now at z. In both cases the smallest weight on the path is unchanged. The sides of every remaining tree edge are unions of the old sides, so they are still minimum cuts. Repeating this gives a tree on the terminals with both properties of a Gomory-Hu tree.

## 3. Time

1. Step 1 takes Õ(√(mn)) time [6].
2. Step 2 runs on a graph with Õ(n) edges and integer weights and demands in [1, n^{O(1)}], in n^{1+o(1)} time [4]. Its inter-cluster weight is γφ vol_H(V) instead of O(φ vol_H(V) log n) in [1], so the quantity W = Σ_x out_x of [1] grows to O(γ Δ m/δ²).
3. Step 3 takes O(n log n) time.
4. Step 4 takes Õ(√(Σ_x d_x · W) + √(mn)) = Õ(m √(γΔ)/δ) time, by the Cauchy-Schwarz bound of [1].
5. Step 5: G̃ has at most W/2 + n edges and integer weights at most n, so the tree takes (W + n)^{1+o(1)} time and the merging O(n).

The sum is (m √Δ/δ) · n^{o(1)}, using m√Δ/δ ≥ √(mn/2). The threshold version adds vol(L_D) for reading the low-degree vertices and gives (vol(L_D) + √(mn) + m√Δ/D) · n^{o(1)}; the choice of D in [1] gives the second bound.

## 4. Measurements

[`sim/terminal_tree.py`](sim/terminal_tree.py) draws 1500 random weighted graphs with 3 to 7 terminals and 1 to 4 extra vertices, computes a Gomory-Hu tree of each on all vertices, merges the extra vertices as in step 5, and asserts for all 16357 pairs of terminals that the smallest path weight is the minimum cut value and that the side of that edge is a minimum cut. Run it with `python terminal_tree.py` in `sim/` (NetworkX needed). The star model and Lemma 3 are checked by the scripts of [1].

## 5. Lean

[`lean/GHMerge.lean`](lean/GHMerge.lean), with [`lean/GHMergeAxioms.lean`](lean/GHMergeAxioms.lean) and its output in [`lean/axioms.txt`](lean/axioms.txt). T is a tree (Mathlib's `SimpleGraph.IsTree`) on a type N with weights w on its edges, y is a node and yz a heaviest edge at y. The merged graph lives on the nodes other than y: `proj` sends y to z, the edge yz disappears, and every other edge ab becomes the edge between proj a and proj b.

- `path_thr`: in an acyclic graph, all edges of the path from u to v weigh at least k exactly when u and v are joined by edges of weight at least k.
- `merge_isTree`, `mergeW_eq`: the merged graph is a tree, and each of its edges comes from exactly one edge ab ≠ yz of T and has its weight.
- `path_min_iff`: for nodes u, v ≠ y and every k, all edges of the u-v path in T weigh at least k exactly when all edges of the path from proj u to proj v in the merged tree do. So both paths have the same minimum weight.
- `side_iff`: for every edge ab ≠ yz of T, two nodes lie on the same side of ab in T exactly when their images lie on the same side of the merged edge. So each remaining edge splits the nodes as before, with y on the side of z.
- `hyps_hold`, `heaviest_needed` (non-vacuity): on the path 0, 1, 2 with weights 3 and 5, merging 1 into 2 meets every hypothesis. Merging 1 into 0 along the lighter edge joins 0 and 2 by an edge of weight 5 although their tree path has an edge of weight 3, so the heaviest-edge condition is needed.

Lean 4 v4.36.0-rc1, Mathlib rev d875a8de5222f62cf1c2fafc7984588adadc990a.

## 6. Limits

- Memory is classical memory readable in superposition, with unit cost per access, as for the sparsifier of [6].
- The time is below m, the cost of reading the graph, when m√Δ/δ or √(mn)Δ^{1/4} is below m up to the factor n^{o(1)}, for example when m ≥ n^{7/4+δ} for a constant δ > 0; on sparser graphs it matches reading the graph up to that factor.
- The factor n^{o(1)} comes from the approximation factor of [4] and the time bounds of [2, 4].
- In the adjacency-matrix model a Gomory-Hu tree needs Ω(n²) queries [1, Theorem 2].
- Not formalized: the algorithm and its analysis, the star model and the Gomory-Hu theorem; Lean covers the merge step on a given weighted tree.

## References

1. Quantum query complexity of Gomory-Hu trees. [`laif/quantum-gomory-hu`](../quantum-gomory-hu/), 26 Nov 2026.
2. A. Abboud, R. Kyng, J. Li, D. Panigrahi, M. Probst Gutenberg, T. Saranurak, W. Yuan, W. Yuan. Deterministic almost-linear-time Gomory-Hu trees. arXiv:2507.20354.
3. S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021, arXiv:2011.09823.
4. J. Li, T. Saranurak. Deterministic weighted expander decomposition in almost-linear time. arXiv:2106.01567.
5. T. Lu, R. Ren, S. Liu. Tight quantum query bounds for minimum cut and multicut on dense graphs. arXiv:2611.17845.
6. S. Apers, R. de Wolf. Quantum speedup for graph sparsification, cut approximation and Laplacian solving. FOCS 2020, arXiv:1911.07306.
7. S. Apers, A. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
