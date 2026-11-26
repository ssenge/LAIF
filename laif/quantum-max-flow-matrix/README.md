# Quantum query complexity of maximum flow in the adjacency matrix model

Written 26 Nov 2026.

Let G be a simple directed graph on n vertices, with no loops and at most one arc for each ordered pair of vertices (two opposite arcs between the same two vertices are allowed). Every arc has capacity 1, and G is given by adjacency matrix queries: a query (u, v) returns whether u → v is an arc. For two vertices s ≠ t let f be the value of a maximum s-t flow. Simple undirected graphs are included, with each edge read as two opposite arcs.

**Theorem 1.** With bounded error, a maximum s-t flow of G, together with its value f, can be computed with

Õ(n^{3/2} · √(min{f, n^{2/3}} + 1))

quantum queries, without knowledge of f. This is Õ(n^{11/6}) on every graph, and Õ(n^{3/2}) for bounded f, which matches the lower bound Ω(n^{3/2}) for deciding whether s and t are connected [1].

**Theorem 2.** Let λ be the edge connectivity of G (the least number of arcs leaving a nonempty proper subset of the vertices) and δ the least in- or out-degree. If δ ≥ 1, there is a quantum algorithm that with probability at least 2/3 outputs λ and a minimum cut after at most

Õ(n² · √(min{λ + 1, n^{2/3}} / δ))

queries. On digraphs with δ = Ω(n) this is Õ(n^{3/2} √(min{λ + 1, n^{2/3}})), at most Õ(n^{11/6}). If δ = 0, then λ = 0, which Õ(n^{3/2}) queries detect.

Status: Claim. The query count of the classical part and the cut structure behind Theorem 2 are checked by scripts with asserts, and the counting steps of Lemmas 3 and 4 and Lemma 5 for the side that the cut arcs leave are proved in Lean.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Maximum s-t flow, simple directed graph, adjacency matrix | O(n²) by reading the matrix; Õ((f+1) n^{3/2}) by f + 1 searches for augmenting paths, each a directed reachability search with O(n^{3/2}) queries [1]; Ω(n^{3/2}) [1] | Õ(n^{3/2} √(min{f, n^{2/3}} + 1)), so Õ(n^{11/6}) |
| Maximum s-t flow, simple undirected graph, adjacency matrix | Õ((f+1) n^{3/2}) as above; for the value f and a minimum cut, not the flow: Õ(n^{11/6}) [3], and Õ(n^{3/2}) with adjacency array queries [8] | the same bound for the flow |
| Edge connectivity λ, simple directed graph, adjacency matrix | O(n²) by reading the matrix; Ω(n^{3/2}) from strong connectivity [1]; for undirected graphs Θ̃(n^{3/2}) [7] | Õ(n² √(min{λ+1, n^{2/3}}/δ)), δ ≥ 1 the least degree |

The quantum algorithm of [4] for directed maximum flow uses adjacency lists, and on dense graphs its bound is above n². For the adjacency array model see [`small-cuts-array-queries`](../small-cuts-array-queries/), and for running time [`quantum-st-minimum-cut-time`](../quantum-st-minimum-cut-time/), Theorem 2.

## 1. OR-queries

An OR-query names a set S of ordered pairs and returns whether S contains an arc of G. The theorem combines a classical algorithm that uses few OR-queries with the following conversion.

**Lemma 1 (from [2, Lemma 2.17]).** An algorithm that makes at most q adaptively chosen OR-queries can be simulated with Õ(n √q) quantum queries, with bounded error.

*Proof.* Keep the set E^c of pairs known to be non-arcs. For a query S, split S ∖ E^c into blocks of at most k pairs and ask the blocks in order until one contains an arc; a block that contains no arc adds its pairs to E^c. Every query ends with one charged block, and every other block has k pairs that are new to E^c, so at most q + n²/k blocks are asked in total [2, Lemma 2.17]. A block is one OR over at most k bits, which Grover search decides with O(√k) queries; repeating each search O(log(q + n²/k)) times makes the total error at most 1/3. With k = ⌈n²/q⌉ the cost is Õ((q + n²/k)√k) = Õ(n√q). If q is not known, run the algorithm with q_i = 2^i n for i = 0, 1, 2, ..., stopping a run once it exceeds its budget of q_i OR-queries; the costs grow geometrically in √q_i, so the total is Õ(n√q) for the true q. ∎

## 2. Blocking flows with OR-queries

The classical algorithm is the blocking-flow method of [5]. It keeps an integral flow f: arcs → {0, 1}, with no flow on both arcs of an opposite pair, and the set of pairs already found to be arcs. The residual graph has an arc u → v if u → v is an arc with f(u, v) = 0, or if f(v, u) = 1; arcs of the second kind are known without queries. A phase does the following.

1. *Levels.* Breadth-first search from s in the residual graph. When u is taken from the queue, first add the known residual arcs to unvisited vertices, then ask OR-queries on {u} × (unvisited vertices v with f(u, v) = 0 and (u, v) not known to be a non-arc). Each answer "yes" is followed by a binary search, O(log n) OR-queries, which finds one new vertex; the answer "no" ends the work at u. If t is not reached, the flow is maximum and the algorithm stops.
2. *Blocking flow.* Depth-first search from s in the level graph, using only vertices that are still alive. At a vertex u of level i, look for a residual arc to an alive vertex of level i + 1: known arcs first, otherwise an OR-query on the remaining candidates and a binary search. If there is none, u dies and the search steps back. When t is reached, push one unit along the path, and start again at s. The phase ends when s dies.

**Lemma 2.** A phase in which the flow grows by f_j along paths of length d_j uses O((n + f_j d_j) log n) OR-queries.

*Proof.* The breadth-first search reaches every vertex at most once and ends the work at every vertex at most once, so it makes at most n "yes" answers, each followed by a binary search, and at most n "no" answers. In the depth-first search every "no" answer kills a vertex, at most n times. Every step forward along an arc ends either on a completed path, which happens for f_j d_j arcs, or at a vertex that later dies, at most n times. ∎

**Lemma 3.** After d phases the remaining flow is at most min{f, 8n²/d²}. Hence there are at most min{f, O(n^{2/3})} phases.

*Proof.* Every phase increases the distance from s to t in the residual graph [5]. After d phases the distance is at least d, so the breadth-first levels V_0, ..., V_d of the next phase are nonempty. Fewer than d/2 of these d + 1 levels have more than 2n/d vertices, and each of them touches at most two of the d pairs (V_i, V_{i+1}), so some pair has |V_i|, |V_{i+1}| ≤ 2n/d. A residual arc rises by at most one level, so every residual s-t path uses an arc from V_i to V_{i+1}. Each ordered pair carries residual capacity at most 2 (its own arc and the reverse of a flow arc), so the cut between levels ≤ i and levels ≥ i + 1 has residual capacity at most 2 (2n/d)² = 8n²/d², which bounds the remaining flow. Every phase adds at least one unit, so the number of phases is at most d + 8n²/d² for every d, which is O(n^{2/3}) at d = n^{2/3}, and at most f. ∎

**Lemma 4.** Σ_j f_j d_j = O(n √(f + 1)).

*Proof.* Let R(d) be the flow that is still missing when the distance first reaches d, so R(d) ≤ min{f, 8n²/d²} by Lemma 3. Every unit pushed along a path of length d_j is missing at each distance 1, ..., d_j, so Σ_j f_j d_j ≤ Σ_{d ≥ 1} R(d). The terms with d ≤ n√(8/f) add up to at most √8 n√f, and the rest to at most Σ_{d > n√(8/f)} 8n²/d² ≤ √8 n√f + f. ∎

*Proof of Theorem 1.* By Lemmas 2 to 4, together with one final breadth-first search, the algorithm makes q = O((n · min{f + 1, n^{2/3}} + n√(f + 1)) log n) = Õ(n · min{f + 1, n^{2/3}}) OR-queries and outputs a maximum flow. Lemma 1 turns this into Õ(n √q) = Õ(n^{3/2} √(min{f, n^{2/3}} + 1)) quantum queries. For an undirected simple graph, run the algorithm on the two opposite arcs of every edge, where one matrix query answers both, and cancel opposite flows at the end. ∎

## 3. Edge connectivity of digraphs

The algorithm samples sinks, using a standard count for simple digraphs, which we prove for completeness.

**Lemma 5.** If λ < δ, both sides of every minimum cut have at least δ + 1 vertices.

*Proof.* Let S be the side that the λ cut arcs leave, and s = |S|. Every vertex of S has at least δ out-arcs, at most s − 1 of them inside S, so if s ≤ δ at least s(δ + 1 − s) arcs leave S. For 1 ≤ s ≤ δ, s(δ + 1 − s) − δ = (s − 1)(δ − s) ≥ 0, so λ ≥ δ, a contradiction. Hence s ≥ δ + 1. The same count with in-arcs gives the bound for the other side. ∎

*Proof of Theorem 2.* First compute δ: exact quantum counting finds a degree with O(n) queries, and minimum finding over the 2n in- and out-degrees uses Õ(√n) such counts, Õ(n^{3/2}) queries in total. If δ = 0, then λ = 0. Otherwise fix a vertex r and let X be a set of min{n, ⌈3 (n/δ) ln n⌉} uniformly random vertices. For k = 1, 2, 4, ..., run the algorithm of Section 2 from r to u and from u to r for every u ∈ X ∖ {r}, stopping each run once its flow reaches k, and let μ_k be the least value found. Stop at the first k with μ_k < k or k ≥ δ, and output min{δ, μ_k} with the cut of the final breadth-first search of the run that gave μ_k, or a vertex of degree δ.

Since λ ≤ δ always, it remains to see that the output is λ. Every value found is at least λ, so the output is at least λ, and it equals δ = λ when λ = δ. If λ < δ, take a minimum cut. By Lemma 5 its side without r has at least δ + 1 vertices, so X meets it with probability at least 1 − n^{−3}, and a vertex u there gives a flow of value λ from r to u or from u to r. Then μ_k = λ for every k > λ and μ_k = k for k ≤ λ, so the loop stops at some k ≤ 2(λ + 1) and outputs λ.

A run stopped at value k has at most k phases, and by Lemmas 2 to 4 with f replaced by k it uses Õ(n · min{k + 1, n^{2/3}}) OR-queries. Summed over the at most 2|X| = Õ(n/δ) runs and the doubling of k, the whole algorithm makes q = Õ((n/δ) · n · min{λ + 1, n^{2/3}}) OR-queries. All runs ask about the same matrix, so one application of Lemma 1 to the whole algorithm gives Õ(n√q) = Õ(n² √(min{λ + 1, n^{2/3}}/δ)) quantum queries, which is at least n^{3/2} and so also covers the computation of δ. The bound holds whenever X meets the side of a minimum cut without r, with probability at least 1 − n^{−3}; together with the errors of Lemma 1 and of the computation of δ, the total failure probability is at most 1/3. ∎

## Remarks

- The same bound follows from the decision-tree method of [6] with T ≤ n² queries and G = Õ(n · min{f + 1, n^{2/3}}) wrong guesses (guess "no arc" for every pair).
- Up to logarithmic factors, the bound improves on f + 1 augmenting path searches by the factor √(f + 1) for f ≤ n^{2/3}, and it is below n² for every f. For undirected graphs the value f alone is easier: [8] computes it and a minimum cut with Õ(n^{3/2}) adjacency array queries, and Theorem 1 matches this for bounded f while also giving the flow.
- Theorem 2 is below n² when δ is larger than min{λ + 1, n^{2/3}} by more than a polylogarithmic factor; for λ close to δ it gives n² up to logarithmic factors.
- Only the classical algorithm uses unbounded computation; the bound is a query bound.

## Scripts

[`sim/maxflow_or.py`](sim/maxflow_or.py) (output in [`sim/out_maxflow_or.txt`](sim/out_maxflow_or.txt)) runs the algorithm of Section 2 on 96 random digraphs with up to 45 vertices, and on 12 digraphs made of s-t paths of lengths 1, ..., L with extra arcs that create no shorter path, which force L phases (up to 18). It asserts that the output is a feasible 0/1 flow (capacities, conservation, no flow on both arcs of a pair) whose value equals that of a shortest-augmenting-path computation on the full matrix, that the number of phases is at most min{f, 3n^{2/3} + 1}, and that the number of found arcs plus "no" answers is at most 3(Pn + n√(f + 1)) for P phases (largest ratio 1.70). A mutation that keeps dead ends alive is caught. Run it with `python maxflow_or.py` in `sim/`.

[`sim/dir_lambda.py`](sim/dir_lambda.py) (output in [`sim/out_dir_lambda.txt`](sim/out_dir_lambda.txt)) checks Lemma 5 and the sampling step of Theorem 2 by brute force over all vertex sets of 240 digraphs with up to 10 vertices, half of them made of two dense blocks joined by one or two arcs in each direction (40 of them have λ < δ). It asserts that every minimum cut has both sides of size at least δ + 1 when λ < δ, and that the least flow value between a fixed root and the vertices of either side of a minimum cut is λ. A mutation to δ + 2 is caught.

## Lean

The folder [`lean/`](lean/) holds the library `MaxFlowOR` (Lean 4 with Mathlib), with only the standard axioms ([`lean/axioms.txt`](lean/axioms.txt)).

- `Levels.lean`: `exists_small_pair` (among levels a_0, ..., a_d of total size at most n, two consecutive levels have d · a_i ≤ 2n), `cut_le_levels` (if every arc with positive residual capacity rises by at most one level and every pair carries at most 2, the cut after level i has capacity at most 2 |level i| |level i+1|) and `cut_bound` (together they give at most 8n²/d²). These are the counting steps of Lemma 3.
- `Sum.lean`: `charging` (Σ_j F_j D_j = Σ_d Σ_{j: D_j > d} F_j), `tail_le` (Σ_{k<m} 1/(K+k+1)² ≤ 1/K − 1/(K+m)), `sum_R_le` and `sum_FD_le` (if the flow pushed after distance d is at most f and at most 8n²/(d+1)², then Σ_j F_j D_j ≤ K f + 8n²/K for every K ≥ 1). With K = ⌈n√(8/f)⌉ this is Lemma 4.
- `DirCut.lean`: `side_large`, Lemma 5 for the side that the cut arcs leave (applied to the reversed digraph it gives the other side), with `card_leaving`.
- `NonVacuity.lean`: the hypotheses of each lemma hold on small instances. Levels 1, 2, 1, 2, 1 show that the factor 2 in `exists_small_pair` is needed. A capacity-2 arc between two vertices makes `cut_le_levels` tight, and it fails without the rise condition. Two complete digraphs on four vertices joined by one arc each way make `side_large` tight.

## Not formalized

Theorems 1 and 2, Lemmas 1 and 2, and the parts of Lemmas 3 and 4 outside the Lean statements below are written proofs. Grover search, exact quantum counting, minimum finding, the conversion of [2, Lemma 2.17] and the distance property of blocking flows [5] are used as stated there.

## References

1. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006. arXiv:quant-ph/0401091.
2. J. Blikstad, J. van den Brand, Y. Efron, S. Mukhopadhyay, D. Nanongkai. Nearly optimal communication and query complexity of bipartite matching. FOCS 2022. arXiv:2208.02526.
3. S. Apers, A. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.
4. A. Ambainis, R. Špalek. Quantum algorithms for matching and network flows. STACS 2006. arXiv:quant-ph/0508205.
5. E. A. Dinic. Algorithm for solution of a problem of maximum flow in networks with power estimation. Soviet Math. Doklady 11, 1970. S. Even, R. E. Tarjan. Network flow and testing graph connectivity. SIAM J. Comput. 4(4), 1975.
6. C. Y.-Y. Lin, H.-H. Lin. Upper bounds on quantum query complexity inspired by the Elitzur-Vaidman bomb tester. CCC 2015. arXiv:1410.0932. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. Quantum 4, 2020. arXiv:1905.13095.
7. S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021. arXiv:2011.09823.
8. T. Lu, R. Ren, S. Liu. Tight quantum query bounds for minimum cut and multicut on dense graphs. arXiv:2611.17845.

## Use of AI

The algorithm, the proofs, the script and this text were produced with the help of Claude Opus 5.5.
