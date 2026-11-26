# Quantum minimum k-cut

Written 26 Nov 2026.

In the minimum k-cut problem, an undirected graph G with n vertices and nonnegative integer edge weights is split into at least k connected components by deleting edges of least total weight λ_k. For fixed k the best classical algorithm runs in time n^k (log n)^{O(k²)} [1, Theorem 3], which is optimal up to a factor n^{o(k)} if max-weight clique needs n^{(1−o(1))k} time [1]. For k ≤ 6 there is also a bound of O(m n^{k−2} log³ n) for graphs with m edges [2]. For k = 2, the minimum cut, the quantum query and time complexity in the adjacency matrix model is Õ(n^{3/2} √τ) for weights in [1, τ], and Ω(τ n) quantum queries are needed for 1 ≤ τ ≤ n [3].

Here the recursive contraction of [1] is run with fixed-point amplitude amplification [4] at every level. A minimum k-cut survives contraction from n to i vertices with probability about (i/n)^k, and amplification pays only the square root of its inverse. The level sizes are chosen so that every level costs the same.

**Theorem 1.** Let k ≥ 3 be fixed, and let the weight matrix of G, with integer entries in {0, …, W}, be given by a quantum oracle. A quantum circuit with no quantum random access memory computes λ_k with probability at least 1 − 1/n using

1. n^{k/2} (log n)^{O_k(1)} poly(log W) gates and queries if k ≥ 5, and
2. n^{2+o(1)} poly(log W) gates and queries if k = 3 or k = 4.

**Theorem 2.** For every k ≥ 2, computing λ_k for graphs with n vertices and weights in {0} ∪ [1, n] in the adjacency matrix model needs Ω(n²) quantum queries. So part 2 of Theorem 1 is optimal up to a factor n^{o(1)} for such weights.

Status: Claim. The cost exponent of the level schedule is evaluated by a script with asserts.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Minimum k-cut, weighted, fixed k ≥ 5 | n^k (log n)^{O(k²)} [1]; for k = 5, 6 also O(m n^{k−2} log³ n) [2] | n^{k/2} (log n)^{O_k(1)} |
| Minimum 3-cut and 4-cut, weighted | O(m n log³ n) and O(m n² log³ n) [2] | n^{2+o(1)}, with Ω(n²) queries needed for weights up to n |

## 1. Contraction by exponential clocks

The Contraction Algorithm to i vertices contracts a uniformly random edge of a multigraph, deletes the self-loops and repeats until i vertices remain [1]. An integer weight w_e counts as w_e parallel edges [1, Section 1.1].

Give each edge e an independent key x_e with the exponential distribution of rate w_e, which is the minimum of w_e unit-rate clocks on its parallel copies. The order of the copies by their clocks is a uniformly random permutation. Kruskal's process runs through this order and joins the two components of a copy whenever they differ. Given its history, the next copy it uses is uniform among the remaining copies between different components, which is the rule of the Contraction Algorithm. Stopped at i components, Kruskal's process on the keys is therefore the Contraction Algorithm to i vertices.

The keys are computed from uniformly random seed bits with b = O(k log n + k² log k + log W) bits of precision. Then ties and rounding change the probability of any event by less than half of the bound in the next paragraph.

**Survival** [1, Lemma 17]. Let K be a minimum k-cut and n ≥ i ≥ 8k² + 2k. Then no edge of K is contracted down to i vertices with probability at least (n/i)^{−k} ψ_k, where ψ_k = k^{−O(k²)}.

## 2. One contraction as a circuit

Let c be the number of components of G and i ≥ c the target. Each step below reads and writes registers at fixed positions, so the circuit needs no quantum random access memory.

1. Compute a minimum spanning forest F for the keys by Borůvka's algorithm in O(log n) rounds. In each round, every vertex scans its row for the edge of least key to a vertex with another label, and every label keeps the least of these edges over its vertices. The kept edges hook the labels, which are then merged by O(log n) steps of pointer jumping. Distinct keys make the kept edges a forest. The per-label minima and the pointer steps use sorting networks [5] on n records.
2. Sort the n − c edges of F by key, and let θ be the key of the (n − i)-th lightest.
3. Compute the components of the edges with key at most θ, by the connectivity part of step 1. Kruskal's process joins exactly the edges of F, in key order, so these are its i components after n − i joins.
4. Number the components 1, …, i. Sort the n² triples (component of u, component of v, w_uv) and add up equal pairs by a segmented prefix sum. The result is the weight matrix of the contracted graph.

The circuit has O(n² polylog n · poly(b)) gates. On G itself it makes n² queries. On a contracted graph it makes none, since that graph is held in registers.

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

Only the contractions at level 0 query the oracle, n² times each. There are O(q_0^{−1/2}) polylog of them, so the query count is n² (n/n_1)^{k/2} polylog. That is at most n^{k/2} polylog for k ≥ 5 and n^{2+o(1)} for k = 3, 4.

The schedule matters. With the schedule n_{ℓ+1} = n_ℓ^{2/k} of the classical recursion [1, Theorem 20], the term at ℓ = 0 is n^{k/2+1}.

## 4. Proof of Theorem 2

Add k − 2 isolated vertices to G. A partition into k parts that keeps all of V(G) in one part would need k − 1 more nonempty parts made of isolated vertices, and there are only k − 2 of them. So every such partition splits V(G) and costs at least the minimum cut λ_2(G). A minimum cut of G together with the k − 2 singletons costs exactly λ_2(G). Hence λ_k of the padded graph equals λ_2(G).

The padded graph has n + k − 2 vertices, and each of its queries is answered by at most one query to G. The bound Ω(τ n) of [3] for dense graphs with τ = n then gives Ω(n²).

## 5. Measurements

[`sim/recursion.py`](sim/recursion.py) evaluates the largest per-level exponent, the maximum over ℓ of (1 − e_{ℓ+1}) k/2 + e_ℓ c, where n_ℓ = n^{e_ℓ} and c is the exponent of one contraction. It asserts the following:

- for c = 2 and c = 2.371177, the schedule e_{ℓ+1} = (2c/k) e_ℓ gives exponent k/2 for 5 ≤ k ≤ 10 with k > 2c;
- the schedule e_{ℓ+1} = (2/k) e_ℓ gives k/2 + c − 1;
- for k = 3, 4, the schedule e_{ℓ+1} = (1 − ε) e_ℓ gives at most c + kε/2.

Run it with `python recursion.py` in `sim/`.

## 6. Limits

- k is fixed. The factor per level, k^{O(k²)}, is not explicit in [1], and the exponent of the polylogarithmic factor grows like k² log k / log(k/4).
- For k = 3 on graphs with n^{1+o(1)} edges, the classical bound O(m n log³ n) of [2] is as good.
- Weights are integers, so rational weights are scaled first. The gate count grows polynomially in log W.
- The table compares weighted graphs. For simple unweighted graphs, faster classical algorithms are known [6].
- Not formalized: the algorithm, its analysis and Theorem 2.

## References

1. A. Gupta, D. G. Harris, E. Lee, J. Li. Optimal bounds for the k-cut problem. arXiv:2005.08301.
2. M. S. Levine. Algorithms for connectivity problems in undirected graphs: maximum flow and minimum k-way cut. PhD thesis, Massachusetts Institute of Technology, 2002.
3. S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021, arXiv:2011.09823.
4. T. J. Yoder, G. H. Low, I. L. Chuang. Fixed-point quantum search with an optimal number of queries. Physical Review Letters 113, 210501 (2014), arXiv:1409.3305.
5. K. E. Batcher. Sorting networks and their applications. AFIPS Spring Joint Computer Conference, 1968.
6. J. Li. Faster minimum k-cut of a simple graph. FOCS 2019.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
