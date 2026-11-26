# Quantum query complexity of vertex connectivity

Written 26 Nov 2026.

**Setting.** G = (V, E) is a simple undirected graph with n vertices, given by its adjacency matrix: a query asks whether two vertices are adjacent. Only queries are counted, not time. The vertex connectivity κ(G) is the least number of vertices whose removal leaves a disconnected graph or a single vertex, so κ(K_n) = n − 1. For a vertex set L write N(L) = (⋃_{v∈L} N(v)) ∖ L, and N[v] = N(v) ∪ {v}. Õ hides factors polylogarithmic in n.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | κ(G) in the adjacency matrix model | O(n²) queries for general κ (read the matrix); Õ((κ+1) n^{3/2}) by scan-first search forests, implied by [1] and [9]; Ω(n^{3/2}), implied by [1] | Õ(n^{7/4}) queries | Claim; Lean for Lemmas 4 and 5 |

To our knowledge no o(n²) quantum query algorithm for vertex connectivity was known in this model. The lower bound Ω(n^{3/2}) holds because, for n ≥ 2, κ(G) ≥ 1 exactly when G is connected, and connectivity needs Ω(n^{3/2}) queries [1]. For edge connectivity the complexity in this model is Θ̃(n^{3/2}) [7]; whether vertex connectivity needs more is open. In two-party communication, global vertex connectivity needs Θ̃(n^{3/2}) bits while s-t vertex connectivity needs Õ(n) [3]. For small κ, the capped scan of [8, Section 5] also runs on the rows of the matrix: scanning v, the marked entries of its row are found with O(√(n t_v) + √n log n) queries, so k-vertex-connectivity is decided with O(n^{3/2}(√k + log n)) queries, which is below n^{7/4} for κ < √n. In the adjacency array model, see Corollary 6 of [8].

The algorithm follows the structure of the communication protocol of [3]: a reduction from global vertex connectivity to one sink, s-t vertex connectivity calls for large sides, and neighbourhood differences for small sides. The contribution here is its implementation with quantum queries.

## The tools

**Lemma 2 (s-t vertex connectivity as a matching).** Let s, t be non-adjacent, C = N(s) ∩ N(t), A = N(s) ∖ N(t), B = N(t) ∖ N(s), V₀ = V ∖ ({s, t} ∪ C) and W = V₀ ∖ (A ∪ B). Let H be the bipartite graph with left vertices x_v for v ∈ V₀ ∖ B, right vertices y_v for v ∈ V₀ ∖ A, the edges x_v y_v for v ∈ W, and the edges x_u y_w for every edge uw of G with u, w ∈ V₀, u ∉ B, w ∉ A (in both orientations). Then κ(s, t) = |C| + ν(H) − |W|, where ν is the size of a maximum matching.

*Proof.* Every s-t separator contains C, and the paths s, c, t for c ∈ C are internally disjoint, so κ(s, t) = |C| + p, where p is the largest number of vertex-disjoint A-B paths in G₀ = G[V₀], by the vertex form of Menger's theorem. Such paths may be shortened so that only their first vertex lies in A and only their last lies in B. Given p of them, match x_u y_w along every edge uw of each path, directed from A to B, and match x_v y_v for every vertex of W on no path. A path with k ≥ 1 edges uses k matching edges and k − 1 vertices of W, so the matching has |W| + p edges. Conversely, in a matching M the edges x_u y_w with u ≠ w form directed paths and cycles, since each vertex has at most one outgoing and one incoming such edge. |M| counts the matched left vertices: those of A, which are the starts of paths beginning in A, and those of W. A vertex w ∈ W that ends a path has y_w used, so x_w is unmatched. Paths that begin in A and end outside B end in W, so |M| ≤ |W| + (number of paths from A to B) ≤ |W| + p. ∎

Every entry of H is either fixed or one entry of the adjacency matrix of G, and H has at most 2n vertices. With the rows of s and t read (2n queries), the algorithm of [2] gives κ(s, t) with Õ(n^{3/2}) queries.

**Lemma 3 (one sink, following [3, Lemma 10.4]).** Let δ be the minimum degree, let G be non-complete, and let s_1, …, s_z be vertices. Build G₂: a vertex s*, a copy u′ of each u ∈ V joined to s*, and for each i a copy B_i of V ∖ N[s_i], with (i, v)(i, w) an edge when vw ∈ E, and (i, v)u′ an edge when vu ∈ E and u ∈ N(s_i). Let U = ⋃_i B_i and μ = min{|N(L)| : L ⊆ U, L ≠ ∅}, taken in G₂. Then μ ≥ κ(G), with equality if some s_i lies on the larger side of a minimum vertex cut of G. If U = ∅, put μ = ∞.

As printed in [3], B_i is joined to the copies of all neighbours; we use the copies of the neighbours in N(s_i), which gives the stated cut.

*Proof.* Let L ⊆ U be nonempty and t = (i, v) ∈ L. The vertices v and s_i are non-adjacent, so G has κ(v, s_i) ≥ κ(G) paths from v to s_i that share only their ends. Each enters N[s_i] first at an inner vertex u ∈ N(s_i), since V ∖ N[s_i] has no neighbour of s_i. Its part before u lies in V ∖ N[s_i], and the copy of that part in B_i, followed by u′ and s*, is a path in G₂. These paths share only t and s*. Since s* ∉ L ∪ N(L), each of them meets N(L), so |N(L)| ≥ κ(G). Now let (L, S, R) be a minimum vertex cut of G with s_i ∈ R. Then L ⊆ V ∖ N[s_i], and the copy L_i of L in B_i has N(L_i) = {(i, w) : w ∈ N(L) ∖ N(s_i)} ∪ {u′ : u ∈ N(L) ∩ N(s_i)}, of size |N(L)| ≤ |S| = κ(G). ∎

Since δ ≥ κ(G), the two sides of a minimum cut have n − κ(G) ≥ n − δ vertices together, so the larger side R has at least (n − δ)/2. Hence z = ⌈4n ln n/(n − δ)⌉ uniform samples hit R with probability at least 1 − n^{−2}, and G₂ has at most 1 + n + z(n − δ − 1) = O(n log n) vertices. Given the sets N(s_i), every entry of the adjacency matrix of G₂ is fixed or costs one query to G.

**Lemma 4 (as in [3, Lemma 3.1]).** For any graph and vertex set U, if L ⊆ U is nonempty and |N(L)| = μ is the minimum of |N(L′)| over nonempty L′ ⊆ U, then |N(u) △ N(v)| ≤ 2|L| for all u, v ∈ L.

*Proof.* Each {u} is a candidate, so |N(u)| ≥ μ, and N(u) ∪ N(v) ⊆ L ∪ N(L). Hence |N(u) △ N(v)| = 2|N(u) ∪ N(v)| − |N(u)| − |N(v)| ≤ 2(|L| + μ) − 2μ. ∎

**Lemma 5 (a cluster with a centre, in the spirit of [3, Claim 9.5]).** Let C be a vertex set, c ∈ C and D_C = ⋃_{v∈C} (N(c) △ N(v)). For every nonempty L ⊆ C, N(L) ∖ (D_C ∪ C) = N(c) ∖ (D_C ∪ C). So |N(L)| = a_C + |N(L) ∩ (D_C ∪ C)| with a_C = |N(c) ∖ (D_C ∪ C)|, which does not depend on L.

*Proof.* For x ∉ D_C ∪ C and v ∈ C, x ∈ N(v) exactly when x ∈ N(c), and x ∉ L. ∎

## Theorem 1, the algorithm

**Theorem 1.** With bounded error, κ(G) can be computed with Õ(n^{7/4}) adjacency matrix queries.

1. **Minimum degree and sinks.** Compute δ by minimum finding [5] over the n exact degrees, each read with n queries: O(n^{3/2}) queries. If δ = n − 1, output n − 1. Otherwise sample z sinks as above, and find all non-neighbours of each s_i by search for all marked items [6], each search amplified to error n^{−3}. There are at most n − δ − 1 of them, so this costs Õ(z√(n(n − δ))) = Õ(n^{3/2}) queries. By Lemma 3 it remains to compute μ in G₂, which has n₂ = O(n log n) vertices; put ℓ₀ = ⌈√n₂⌉. Fix a set L attaining μ.
2. **Phase 1, |L| ≥ ℓ₀.** Sample a set P of ⌈3√n₂ ln n₂⌉ uniform vertices of U, which meets L with probability at least 1 − n₂^{−3}. For v ∈ U, the component of v in G₂ minus a minimum v-s* separator X contains no copy u′, since every u′ is adjacent to s*, so it lies in U and has N inside X. Hence κ_{G₂}(v, s*) ≥ μ for all v ∈ U, with equality for v ∈ L, since N(L) separates v from s*. Compute min_{v∈P} κ_{G₂}(v, s*) by minimum finding [5] over the |P| values, each from Lemma 2 and [2] with error amplified to n₂^{−3}: Õ(|P|^{1/2} n₂^{3/2}) = Õ(n^{7/4}) queries.
3. **Phase 2, |L| < ℓ₀.**
   - *Sketch.* Put each vertex of G₂ into a set T independently with probability q = min{1, 48 ln n₂/ℓ₀}, and read all entries between U and T: Õ(n₂²/ℓ₀) = Õ(n^{3/2}) queries. Join u, v ∈ U in a graph G_d when |(N(u) △ N(v)) ∩ T| ≤ 3qℓ₀. By the Chernoff bound, with probability 1 − O(n₂^{−4}) every pair with |N(u) △ N(v)| ≤ 2ℓ₀ is joined and every joined pair has |N(u) △ N(v)| ≤ 4ℓ₀.
   - *Clusters.* Take a sparse neighbourhood cover of G_d [4]: clusters of diameter O(log n₂) in G_d such that each vertex lies in O(log n₂) clusters and each closed neighbourhood in G_d lies in some cluster. This step needs no queries.
   - *Differences.* In each cluster C fix a centre c. Every v ∈ C has |N(c) △ N(v)| = O(ℓ₀ log n₂) by the triangle inequality along a path in G_d. Find all of N(c) △ N(v) by search for all marked items [6], where x is marked when the entries (c, x) and (v, x) differ, amplified to error n₂^{−3} and stopped after its stated number of queries: Õ(√(n₂ ℓ₀)) = Õ(n^{3/4}) queries per v, and Õ(n^{7/4}) in total, since the clusters have total size O(n₂ log n₂). Then read the entries (c, x) for x ∈ D_C ∪ C, which is Õ(n^{3/2}) queries in total; now every entry (v, x) with v ∈ C and x ∈ D_C ∪ C is known.
   - *Minimum.* By Lemma 5, β_C = min{|N(L′) ∩ (D_C ∪ C)| : L′ ⊆ C, L′ ≠ ∅} is known without further queries, and the least |N(L′)| over nonempty L′ ⊆ C is a_C + β_C, with a_C = deg(c) − |N(c) ∩ (D_C ∪ C)|. Compute min_C (a_C + β_C) by minimum finding [5], reading deg(c) with n₂ queries: Õ(n^{3/2}) queries.
4. Output the smaller of the two phase values. (If U = ∅, which has probability at most n^{−2}, output n − 1.)

*Correctness.* Both phase values are values |N(L′)| for nonempty L′ ⊆ U, so they are at least μ. If |L| ≥ ℓ₀, Phase 1 attains μ when P meets L. If |L| < ℓ₀, Lemma 4 gives |N(u) △ N(v)| ≤ 2|L| < 2ℓ₀ for u, v ∈ L, so L is a clique of G_d, lies in the closed neighbourhood of any of its vertices, and so in some cluster, where Phase 2 attains μ. With Lemma 3 and the union bound over the steps, the output is κ(G) with probability at least 2/3. ∎

Only the value of κ(G) is computed.

## Lean

The library `VertexConn` in `lean/` (Lean 4, Mathlib at the revision pinned in `lean/lakefile.toml`) proves, with only the standard axioms (`lean/axioms.txt`), for a graph given by a neighbourhood function `N : V → Finset V` and `nbhd N L = (⋃_{v∈L} N v) ∖ L`:

- `VertexConn.twin_bound` (Lemma 4): if `N` has no loops, `L ⊆ U` is nonempty and `|nbhd N L|` is least among the nonempty subsets of `U`, then `|N u △ N v| ≤ 2|L|` for all `u, v ∈ L`;
- `VertexConn.cluster_outside` and `VertexConn.cluster_card` (Lemma 5): for a set `C`, a vertex `c` and `D = ⋃_{v∈C} (N c △ N v)`, every nonempty `L ⊆ C` has `nbhd N L ∖ (D ∪ C) = N c ∖ (D ∪ C)`, so `|nbhd N L| = a_C + |nbhd N L ∩ (D ∪ C)|`;
- `VertexConn.nbhd_singleton`, `VertexConn.card_sdiffs_add`: the neighbourhood of a single vertex, and the count of a symmetric difference;
- content of the statements, in `lean/VertexConn/NonVacuity.lean`: on the path with four vertices the hypotheses of `twin_bound` hold; on the star with six vertices a non-minimal set violates the bound, so the minimality hypothesis is needed; and the term `a_C` of `cluster_card` can be positive.

## Scripts

`sim/check_pipeline.py` runs the steps classically on random graphs with 6 to 12 vertices and on dense graphs with a planted small side. It asserts Lemma 2 on every non-adjacent pair, Lemma 3 with all vertices as sinks (equality) and with two random sinks (lower bound), Lemma 5 on all subsets of random 5-vertex sets, Lemma 4 on every minimizer of every sink, and, for every sink t, that both phases are never below the minimum t-sink cut, that Phase 1 attains it when a sampled source lies in a minimizer, and that Phase 2 attains it when a minimizer is small. Phase 2 runs on exact differences (the sketch is a probability statement and is not simulated) with closed G_d-neighbourhoods as clusters. Three mutations must fail: Lemma 2 without the common neighbours, Lemma 3 with B_i joined to the copies of all neighbours, and Lemma 5 without the term a_C.

**Not formalized:** Lemmas 2 and 3, the algorithm and its query count. The algorithm of [2], minimum finding [5], search for all marked items [6] and sparse neighbourhood covers [4] are used as stated there.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.

## References

[1] C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006. arXiv:quant-ph/0401091.

[2] J. Blikstad, J. van den Brand, Y. Efron, S. Mukhopadhyay, D. Nanongkai. Nearly optimal communication and query complexity of bipartite matching. FOCS 2022. arXiv:2208.02526.

[3] J. Blikstad, Y. Jiang, S. Mukhopadhyay, S. Yingchareonthawornchai. Global vs. s-t vertex connectivity beyond sequential: almost-perfect reductions and near-optimal separations. arXiv:2503.20366.

[4] B. Awerbuch, B. Berger, L. Cowen, D. Peleg. Near-linear time construction of sparse neighborhood covers. SIAM J. Comput. 28(1), 1998.

[5] C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.

[6] M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46(4-5), 1998. arXiv:quant-ph/9605034.

[7] S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021. arXiv:2011.09823.

[8] Small cuts and flows with adjacency array queries, `laif/small-cuts-array-queries` in this repository.

[9] J. Cheriyan, M.-Y. Kao, R. Thurimella. Scan-first search and sparse certificates: an improved parallel algorithm for k-vertex connectivity. SIAM J. Comput. 22(1), 1993.
