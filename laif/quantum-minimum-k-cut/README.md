# Quantum minimum k-cut

Written 26 Nov 2026.

In the minimum k-cut problem, an undirected graph G with n vertices and nonnegative integer edge weights is split into at least k connected components by deleting edges of least total weight λ_k. For fixed k, recursive contraction runs in time n^k (log n)^{O(k²)} [1, Theorem 3], and a reduction from max-weight (k − 1)-clique is noted in [1]. On graphs with m edges, the bound is k^{O(k²)} n^{k−2}(m + n) log³ n [7]. On dense graphs it is k^{O(k²)} n^{k−1} log² n [8], which is n² log² n for k = 3. For k ≤ 6 there is also a bound of O(m n^{k−2} log³ n) [2]. For k = 2, the minimum cut, the quantum query and time complexity in the adjacency matrix model is Õ(n^{3/2} √τ) for weights in [1, τ], and Ω(n^{3/2} √τ) quantum queries are needed for integers 1 ≤ τ ≤ n [3].

Here the recursive contraction of [1] is run with fixed-point amplitude amplification [4] at every level. A minimum k-cut survives contraction from n to i vertices with probability about (i/n)^k, and amplification pays only the square root of its inverse. The level sizes are chosen so that every level costs the same.

**Theorem 1.** Let k ≥ 3 be fixed, and let the weight matrix of G, with integer entries in {0, …, W}, be given by a quantum oracle. A quantum circuit with no quantum random access memory makes n² queries and computes λ_k with probability at least 1 − 1/n using

1. n^{k/2} (log n)^{O_k(1)} poly(log W) gates if k ≥ 5, and
2. n^{2+o(1)} poly(log W) gates if k = 3 or k = 4.

**Theorem 2.** For every fixed k ≥ 2, computing λ_k for graphs with n vertices and weights in {0, 1, n} in the adjacency matrix model needs Ω(n²) quantum queries, and so Ω(n²) time. So part 2 of Theorem 1 is optimal up to a factor n^{o(1)} for such weights.

**Hypothesis H_r** (quantum max-weight clique). For a fixed r ≥ 5 there is a constant c such that no quantum algorithm with classical memory readable in superposition computes, for a complete graph with N vertices and integer edge weights in {0, …, N^c} given by an oracle, the largest total weight of the edges inside an r-set of vertices in time O(N^{r/2 − δ}) for any δ > 0.

Quantum search over the r-sets meets this bound up to logarithmic factors, and to our knowledge no faster quantum algorithm is known. Edges of weight 0 play the role of non-edges, so the problem contains max-weight r-clique after adding a large constant to the weights of the edges.

**Theorem 3.** Let k ≥ 6. Under H_{k−1}, no quantum algorithm with classical memory readable in superposition computes λ_k for graphs with n vertices and integer weights in {0, …, n^{c+3}} in time O(n^{(k−1)/2 − δ}) for any δ > 0. For k = 5, Theorem 2 gives Ω(n²) = Ω(n^{(k−1)/2}) without a hypothesis. So the exponent k/2 of part 1 of Theorem 1 is within 1/2 of optimal for every k ≥ 5, under H_{k−1} for k ≥ 6.

Status: Claim. The cost exponent of the level schedule is evaluated by a script with asserts, and the level-cost inequalities and the padding identity of Section 4 are checked in Lean. The gadget of Section 5 is checked by brute force on small graphs.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Minimum k-cut, weighted, fixed k ≥ 5 | k^{O(k²)} n^{k−1} log² n [8]; k^{O(k²)} n^{k−2}(m + n) log³ n [7] | n^{k/2} (log n)^{O_k(1)} |
| Minimum 4-cut, weighted | n³ polylog n [8]; O(m n² log³ n) [2] | n^{2+o(1)}, optimal up to n^{o(1)} for weights up to n |

## 1. Contraction by exponential clocks

The Contraction Algorithm to i vertices contracts a uniformly random edge of a multigraph, deletes the self-loops and repeats until i vertices remain [1]. An integer weight w_e counts as w_e parallel edges [1, Section 1.1].

Give each edge e an independent key x_e with the exponential distribution of rate w_e, which is the minimum of w_e unit-rate clocks on its parallel copies. The order of the copies by their clocks is a uniformly random permutation. Kruskal's process runs through this order and joins the two components of a copy whenever they differ. Given its history, the next copy it uses is uniform among the remaining copies between different components, which is the rule of the Contraction Algorithm. Stopped at i components, Kruskal's process on the keys is therefore the Contraction Algorithm to i vertices.

The keys are computed from uniformly random seed bits with b = O(k log n + k² log k + log W) bits of precision, and ties are broken by the index of the edge. Two keys of rates at most n² W change their order by rounding with probability O(n² W 2^{−b}). Over the at most n⁴ pairs, this changes the probability of any event by less than half of the bound in the next paragraph.

**Survival** [1, Lemma 17]. Let K be a minimum k-cut and n ≥ i ≥ 8k² + 2k. Then no edge of K is contracted down to i vertices with probability at least (n/i)^{−k} ψ_k, where ψ_k = k^{−O(k²)}.

## 2. One contraction as a circuit

Let c be the number of components of G and i ≥ c the target. Pairs of weight 0 get the key +∞ and are never chosen. Keys are compared as pairs (key, edge index), so they are distinct. Each step below reads and writes registers at fixed positions, so the circuit needs no quantum random access memory.

1. Compute a minimum spanning forest F for the keys by Borůvka's algorithm in O(log n) rounds. In each round, every vertex scans its row for the edge of least key to a vertex with another label, and every label keeps the least of these edges over its vertices. Each label points to the label at the other end of its kept edge. Since keys are distinct, the only cycles are pairs of labels that kept the same edge, and in each pair the smaller label becomes the root. The labels are then merged by O(log n) steps of pointer jumping, and each kept edge is recorded once in F. The per-label minima and the pointer steps use sorting networks [5] on n records. F is stored as n − 1 records, padded with key +∞.
2. Sort the records of F by key, and let θ be the key of the (n − i)-th lightest.
3. Compute the components of the edges with key at most θ, by the connectivity part of step 1. Kruskal's process joins exactly the edges of F, in key order, so these are its i components after n − i joins.
4. Number the components 1, …, i. Sort the n² triples (component of u, component of v, w_uv) and add up equal pairs by a segmented prefix sum. The result is the weight matrix of the contracted graph.

The circuit has O(n² polylog n · poly(b)) gates. It makes no queries, since the weight matrix of G is read into registers once, with n² queries, before the recursion starts, and every contracted graph is held in registers too.

## 3. The recursion

For k ≥ 5 the level sizes are n_0 = n and n_{ℓ+1} = max(⌈n_ℓ^{4/k}⌉, ⌈20k²⌉), down to the last level T with n_T = ⌈20k²⌉. For k = 3, 4 the exponent 4/k becomes 1 − ε with ε = 1/log log n.

For a graph H on n_ℓ vertices and a threshold Λ, the procedure A_ℓ(H, Λ) is a unitary with an accept flag:

- If ℓ = T, it accepts if and only if some partition of H into k parts costs at most Λ. It tries all k^{n_T} = k^{O(k²)} partitions.
- If ℓ < T, let B prepare uniform seed bits, contract H to n_{ℓ+1} vertices (Section 2) and run A_{ℓ+1} on the result. Then A_ℓ is fixed-point amplitude amplification [4] of B, with lower bound q_ℓ = (3/8)(n_ℓ/n_{ℓ+1})^{−k} ψ_k and δ = 1/2.

**Lemma.** If λ_k(H) > Λ, then A_ℓ(H, Λ) accepts with probability 0. If λ_k(H) ≤ Λ, it accepts with probability at least 3/4.

*Proof.* The proof is by induction from level T, where A_T is exact.

- *Case λ_k(H) > Λ.* Every k-cut of a contracted graph is a k-cut of H with the same weight, so every contracted graph has λ_k > Λ. By induction B never accepts, and amplitude amplification of a procedure whose accepting amplitude is zero keeps that amplitude at zero.
- *Case λ_k(H) ≤ Λ.* Fix a minimum k-cut K of H. Since n_ℓ ≥ n_{ℓ+1} ≥ 8k² + 2k, the survival bound and the precision of Section 1 show that K survives with probability at least (1/2)(n_ℓ/n_{ℓ+1})^{−k} ψ_k. The contracted graph then has a k-cut of weight at most Λ, and A_{ℓ+1} accepts it with probability at least 3/4. So B accepts with probability at least q_ℓ. Fixed-point amplification with O(log(2/δ)/√q_ℓ) uses of B and its inverse then succeeds with probability at least 1 − δ² = 3/4 [4]. ∎

**Top level.** If c ≥ k, then λ_k = 0, which the connectivity circuit detects. Otherwise c < k ≤ n_T, so every contraction target is at least c. A binary search finds the least Λ in {0, …, n² W} that A_0(G, Λ) accepts. Each call is repeated r = O(log n + log log(nW)) times and accepted if any repetition accepts. A Λ below λ_k is never accepted. A Λ at or above λ_k is rejected with probability at most 4^{−r}. A union bound over the O(log(nW)) calls gives success probability at least 1 − 1/n.

**Cost.** Let Q_ℓ be the cost of A_ℓ. Then Q_ℓ = O(q_ℓ^{−1/2}) (n_ℓ² polylog + Q_{ℓ+1}). Unrolled, Q_0 is a sum over ℓ of C^{ℓ+1} (n/n_{ℓ+1})^{k/2} n_ℓ² polylog, where C = O(ψ_k^{−1/2} 2^{O(k)}) depends only on k.

- *k ≥ 5.* Here n_{ℓ+1}^{k/2} ≥ n_ℓ², so every term is at most C^{ℓ+1} n^{k/2} polylog. With T = O(log log n / log(k/4)) levels, C^T = (log n)^{O_k(1)}.
- *k = 3, 4.* Here n_ℓ = n^a with a ≤ 1, and the term has exponent k/2 + a(2 − k/2 + kε/2) ≤ 2 + kε/2. There are T = O((log log n)²) levels, so C^T = 2^{O_k((log log n)²)}. Both C^T and n^{kε/2} are n^{o(1)}.

The schedule matters. With the schedule n_{ℓ+1} = n_ℓ^{2/k} of the classical recursion [1, Theorem 20], the term at ℓ = 0 is n^{k/2+1}.

## 4. Proof of Theorem 2

Add k − 2 isolated vertices to G. A partition into k parts that keeps all of V(G) in one part would need k − 1 more nonempty parts made of isolated vertices, and there are only k − 2 of them. So every such partition splits V(G) and costs at least the minimum cut λ_2(G). A minimum cut of G together with the k − 2 singletons costs exactly λ_2(G). Hence λ_k of the padded graph equals λ_2(G).

The padded graph has n + k − 2 vertices, and each of its queries is answered by at most one query to G. In the adjacency matrix model, [3] shows that Ω(n^{3/2} √τ) quantum queries are needed for minimum cut on graphs with edge weights 1 and τ, for integers 1 ≤ τ ≤ n. With τ = n and k fixed, this gives Ω(n²). Time is at least the number of queries.

## 5. Proof of Theorem 3

The reduction from max-weight (k − 1)-clique to k-cut noted in [1] is carried out here with one extra vertex. Let H be a complete graph with N vertices and weights w(u, v) in {0, …, N^c}. Let Δ be its largest weighted degree, and set D = kΔ + 1. The graph G has the vertices and weights of H and one hub b with w(v, b) = D − deg(v), which is at least (k − 1)Δ + 1.

In a partition of G into k parts, the k − 1 parts without b contain t ≥ k − 1 vertices of H. If t ≥ k, the hub edges alone cost at least k(D − Δ) > (k − 1)D. If t = k − 1, the parts are singletons {v} for v in a set S, and the cut contains the hub edges of S and every edge of H at S. Since the degrees in S count each edge inside S twice, the cost is

Σ_{v∈S} (D − deg v) + Σ_{v∈S} deg v − w(S) = (k − 1)D − w(S),

where w(S) is the weight inside S. This is at most (k − 1)D, so λ_k(G) = (k − 1)D − max over (k − 1)-sets S of w(S).

G has n = N + 1 vertices and weights at most D ≤ kN^{c+1} + 1 ≤ n^{c+3} once N is large. An entry of its weight matrix is answered by one query to H or, for a hub entry, by a lookup in a table of the N degrees. The table is computed in O(N²) time and held in classical memory readable in superposition, so an algorithm for λ_k that uses only oracle access to its input can be run on G. An algorithm for λ_k in time O(n^{(k−1)/2 − δ}) would therefore find the largest (k − 1)-clique weight in time O(N² + N^{(k−1)/2 − δ}). For k ≥ 6 this is O(N^{(k−1)/2 − δ'}) for some δ' > 0, which H_{k−1} excludes.

## 6. Measurements

[`sim/recursion.py`](sim/recursion.py) evaluates the largest per-level exponent, the maximum over ℓ of (1 − e_{ℓ+1}) k/2 + e_ℓ c, where n_ℓ = n^{e_ℓ} and c is the exponent of one contraction. It asserts the following:

- for c = 2 and c = 2.371177, the schedule e_{ℓ+1} = (2c/k) e_ℓ gives exponent k/2 for 5 ≤ k ≤ 10 with k > 2c;
- the schedule e_{ℓ+1} = (2/k) e_ℓ gives k/2 + c − 1;
- for k = 3, 4, the schedule e_{ℓ+1} = (1 − ε) e_ℓ gives at most c + kε/2.

Run it with `python recursion.py` in `sim/`.

[`sim/clique_gadget.py`](sim/clique_gadget.py) builds the graph G of Section 5 for 276 random graphs H with 3 to 6 vertices and k = 3, 4, 5 (at most 5 vertices for k = 5). It asserts that the minimum k-cut of G, by brute force over all partitions, equals (k − 1)D minus the largest weight inside a (k − 1)-set.

## 7. Lean

[`lean/KCutExponent.lean`](lean/KCutExponent.lean), with [`lean/KCutExponentAxioms.lean`](lean/KCutExponentAxioms.lean) and its output in [`lean/axioms.txt`](lean/axioms.txt). A level that contracts x = n_ℓ vertices to y = n_{ℓ+1} enters with the cost (n/y)^{k/2} x², and a partition is a map into Fin k whose cost is the weight of the ordered pairs it separates.

- `schedule_hyp`, `level_cost_le`: if y ≥ x^{4/k}, then x² ≤ y^{k/2}, and then (n/y)^{k/2} x² ≤ n^{k/2}, so every level of the schedule for k ≥ 5 costs at most n^{k/2} (Section 3).
- `level_cost_eq`, `level_cost_can_fail`: the bound is attained when x² = y^{k/2}, and it fails for k = 4, n = x = 2, y = 1, where the hypothesis fails.
- `small_k_exponent`: for 0 ≤ k ≤ 4, a ≤ 1 and ε ≥ 0, k/2 + a(2 − k/2 + kε/2) ≤ 2 + kε/2 (Section 3, k = 3, 4).
- `pad_ge`, `pad_le`: after adding k − 2 vertices of weight zero, every surjective map into Fin k costs at least some surjective map of the old vertices into Fin 2, and every surjective map into Fin 2 extends to a surjective map into Fin k of the same cost (Section 4). `cost_pad` computes the cost on the padded graph, and `cost_example` shows that a cost can be positive.

Lean 4 v4.36.0-rc1, Mathlib rev d875a8de5222f62cf1c2fafc7984588adadc990a.

## 8. Limits

- k is fixed. The factor per level, k^{O(k²)}, is not explicit in [1], and the exponent of the polylogarithmic factor grows like k² log k / log(k/4).
- For k = 3, the classical bound n² log² n of [8] is at least as good as part 2 of Theorem 1.
- Weights are integers, so rational weights are scaled first. The gate count grows polynomially in log W.
- The table compares weighted graphs. For simple unweighted graphs, faster classical algorithms are known [6, 7], with Õ(n^{55/19}) for k = 4 and Õ(n^{4.112007}) for k = 5 [7]; Theorem 1 is below these as well.
- Theorem 3 is conditional on H_{k−1}, a hypothesis on quantum algorithms for weighted cliques. Its model has classical memory readable in superposition, which is more than Theorem 1 uses.
- Not formalized: the algorithm, the survival bound of [1], the quantum costs, the bound of [3] and the gadget of Section 5; Lean covers the level-cost arithmetic of Section 3 and the padding identity of Section 4.

## References

1. A. Gupta, D. G. Harris, E. Lee, J. Li. Optimal bounds for the k-cut problem. arXiv:2005.08301.
2. M. S. Levine. Algorithms for connectivity problems in undirected graphs: maximum flow and minimum k-way cut. PhD thesis, Massachusetts Institute of Technology, 2002.
3. S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021, arXiv:2011.09823.
4. T. J. Yoder, G. H. Low, I. L. Chuang. Fixed-point quantum search with an optimal number of queries. Physical Review Letters 113, 210501 (2014), arXiv:1409.3305.
5. K. E. Batcher. Sorting networks and their applications. AFIPS Spring Joint Computer Conference, 1968.
6. J. Li. Faster minimum k-cut of a simple graph. FOCS 2019.
7. J. Li, T. Vaughn. Faster minimum k-cut I: simple and sparse weighted graphs. arXiv:2609.27781.
8. T. Vaughn. Faster minimum k-cut II: improved randomized and deterministic algorithms for weighted graphs. arXiv:2609.27797.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
