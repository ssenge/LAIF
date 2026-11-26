# Quantum query complexity of maximum flow in the adjacency matrix model

Written 26 Nov 2026.

Let G be a simple directed graph on n vertices, with no loops and at most one arc for each ordered pair of vertices (two opposite arcs between the same two vertices are allowed). Every arc has capacity 1, and G is given by adjacency matrix queries: a query (u, v) returns whether u → v is an arc. For two vertices s ≠ t let f be the value of a maximum s-t flow. Simple undirected graphs are included, with each edge read as two opposite arcs.

**Theorem 1.** With bounded error, a maximum s-t flow of G, together with its value f, can be computed with

Õ(n^{3/2} · √(min{f, n^{2/3}} + 1))

quantum queries, without knowledge of f. This is Õ(n^{11/6}) on every graph, and Õ(n^{3/2}) for bounded f, which matches the lower bound Ω(n^{3/2}) for deciding whether s and t are connected [1].

Status: Claim. The query count of the classical part is checked by a script with asserts.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Maximum s-t flow, simple directed graph, adjacency matrix | O(n²) by reading the matrix; Õ((f+1) n^{3/2}) by f + 1 searches for augmenting paths, each a directed reachability search with O(n^{3/2}) queries [1]; Ω(n^{3/2}) [1] | Õ(n^{3/2} √(min{f, n^{2/3}} + 1)), so Õ(n^{11/6}) |
| Maximum s-t flow, simple undirected graph, adjacency matrix | Õ((f+1) n^{3/2}) as above; Õ(n^{11/6}) for the value f and a minimum cut, not the flow [3] | the same bound for the flow |

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

## Remarks

- The same bound follows from the decision-tree method of [6] with T ≤ n² queries and G = Õ(n · min{f + 1, n^{2/3}}) wrong guesses (guess "no arc" for every pair).
- The bound improves on f + 1 augmenting path searches for every f ≥ 1, and it is below n² for every f.
- Only the classical algorithm uses unbounded computation; the bound is a query bound.

## Scripts

[`sim/maxflow_or.py`](sim/maxflow_or.py) (output in [`sim/out_maxflow_or.txt`](sim/out_maxflow_or.txt)) runs the algorithm of Section 2 on 96 random digraphs with up to 45 vertices. It asserts that the flow value equals that of a shortest-augmenting-path computation on the full matrix, that the number of phases is at most min{f, 3n^{2/3} + 1}, and that the number of found arcs plus "no" answers is at most 3(Pn + n√(f + 1)) for P phases (largest ratio 1.70). A mutation that keeps dead ends alive is caught. Run it with `python maxflow_or.py` in `sim/`.

## Not formalized

Theorem 1 and Lemmas 1 to 4 are written proofs, not checked in Lean. Grover search, the conversion of [2, Lemma 2.17] and the distance property of blocking flows [5] are used as stated there.

## References

1. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006. arXiv:quant-ph/0401091.
2. J. Blikstad, J. van den Brand, Y. Efron, S. Mukhopadhyay, D. Nanongkai. Nearly optimal communication and query complexity of bipartite matching. FOCS 2022. arXiv:2208.02526.
3. S. Apers, A. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.
4. A. Ambainis, R. Špalek. Quantum algorithms for matching and network flows. STACS 2006. arXiv:quant-ph/0508205.
5. E. A. Dinic. Algorithm for solution of a problem of maximum flow in networks with power estimation. Soviet Math. Doklady 11, 1970. S. Even, R. E. Tarjan. Network flow and testing graph connectivity. SIAM J. Comput. 4(4), 1975.
6. C. Y.-Y. Lin, H.-H. Lin. Upper bounds on quantum query complexity inspired by the Elitzur-Vaidman bomb tester. CCC 2015. arXiv:1410.0932. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. Quantum 4, 2020. arXiv:1905.13095.

## Use of AI

The algorithm, the proofs, the script and this text were produced with the help of Claude Opus 5.5.
