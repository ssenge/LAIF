# Vertex cover with a parameter: an LP kernel bound in the adjacency matrix model

Written 22 Nov 2026.

**Setting.** The input is a graph G on n vertices, given by its adjacency matrix: a query names a pair {u, w} and returns whether uw is an edge. For an integer k, the task is to output a vertex cover of size at most k or to decide that none exists, with probability at least 2/3.

| | Previous best bound | This folder | Status |
|---|---|---|---|
| Upper | O(√k n + k^{3/2} √n) [1, Thm 1.1] | O(n^{3/2} log² n + k²) | Claim; checked by script |
| Lower | Ω(√k n) for k ≤ (1 − ε)n [1, Thm 1.2] | | |

Together with [1], the query complexity is O(min{√k n + k^{3/2} √n, n^{3/2} log² n + k²}). The new bound is smaller when C n^{2/3} log^{4/3} n ≤ k ≤ n/C for a large constant C. At k = n^{3/4} it is O(n^{3/2} log² n), against Θ(n^{13/8}) from [1]. The bound of [1] uses a kernel built from a maximal matching and the vertices of degree above k. The bound here uses the half-integral LP kernel [3] instead, with a maximum matching of the bipartite double cover found by the algorithm of [2].

A graph has a vertex cover of size at most k exactly when its complement has a clique of size at least n − k, and a query to the complement is a query to G. So the same bounds hold for finding a clique of size at least n − k.

## Theorem 1

**Theorem 1.** There is a quantum algorithm that, given G in the adjacency matrix model and an integer k, outputs a vertex cover of size at most k or decides that none exists, with probability at least 2/3, using O(n^{3/2} log² n + k²) queries.

**Algorithm.**

1. Let H be the bipartite double cover of G: its sides are L = {v_L} and R = {v_R}, and v_L w_R is an edge of H exactly when vw is an edge of G. A query to H is one query to G.
2. Find a maximum matching M of H with O(n^{3/2} log² n) queries [2, Lemma 2.10 and Claim 2.18].
3. Let Z be the set of vertices reachable from the unmatched vertices of L by alternating paths, which leave L along edges outside M and leave R along edges of M. Compute Z by a search that starts at the unmatched vertices of L. For each vertex u ∈ L ∩ Z, it finds all vertices w ∈ R that are not yet reached, are adjacent to u and are not matched to u, and then adds w and its partner M(w). Let C = (L ∖ Z) ∪ (R ∩ Z).
4. Let x_v = |C ∩ {v_L, v_R}|/2 and V_i = {v : x_v = i} for i ∈ {0, 1/2, 1}. Let k′ = k − |V_1|. If k′ < 0 or |V_{1/2}| > 2k′, decide that no vertex cover of size at most k exists.
5. Otherwise query all pairs inside V_{1/2}. Compute a minimum vertex cover S of G[V_{1/2}] without queries. If |S| ≤ k′, output V_1 ∪ S, and otherwise decide that none exists.

*Proof.* Step 2 is correct with high probability by [2].

*The cover C.* The alternating search never reaches an unmatched vertex of R, since that would give an augmenting path, so every vertex of R ∩ Z is matched and its partner lies in Z. A matched vertex u ∈ L enters Z only through its partner, so u ∈ Z exactly when M(u) ∈ Z, and every edge of M has exactly one endpoint in C. Every vertex of C is matched, so |C| = |M|. An edge u w of H with u ∈ L ∩ Z and w ∈ R ∖ Z would be found by the search, so every edge of H meets C. Every vertex cover of H has at least |M| vertices, so C is a minimum vertex cover of H.

*Search cost.* Each vertex w ∈ R is added once, from one vertex u ∈ L. If t_u vertices are added from u, then finding them costs O(√(n (t_u + 1))) queries in expectation [4], and O(√(n (t_u + 1)) log n) for failure probability 1/n² [5]. Since Σ_u √a_u ≤ √(n Σ_u a_u) for n nonnegative terms a_u, Σ_u √(n (t_u + 1)) ≤ √n · √(n · Σ_u (t_u + 1)) ≤ √2 · n^{3/2}. Step 3 therefore makes O(n^{3/2} log n) queries.

*The kernel.* The vector x is an optimal solution of the vertex cover LP of G, since the LP optimum of G is half the minimum vertex cover of H [3]. By [3], G has a minimum vertex cover that contains V_1 and avoids V_0. Hence G has a vertex cover of size at most k exactly when G[V_{1/2}] has one of size at most k′. The constant vector 1/2 is an optimal LP solution of G[V_{1/2}], because x is optimal for G, so every vertex cover of G[V_{1/2}] has at least |V_{1/2}|/2 vertices. If |V_{1/2}| > 2k′ the answer is therefore no, which justifies step 4.

*The output.* Let S be a vertex cover of G[V_{1/2}]. Every edge of G has x-weight at least 1 at its endpoints, so no edge lies inside V_0 or joins V_0 to V_{1/2}. An edge with an endpoint in V_1 is covered by V_1, and the remaining edges lie inside V_{1/2} and are covered by S. So V_1 ∪ S is a vertex cover of G.

*Queries.* Step 5 makes at most |V_{1/2}|²/2 ≤ 2k² queries. With steps 2 and 3 the total is O(n^{3/2} log² n + k²). ∎

The term k² is the cost of reading the kernel. On the kernel the LP optimum is half the number of vertices, so a smaller cost there would need an algorithm for minimum vertex cover on 2k′ vertices with o(k′²) queries. The best known upper bound for minimum vertex cover is the trivial O(n²), and the best known lower bound is Ω(n^{3/2}) [1].

## Script

`sim/check_kernel.py` checks the classical steps on 400 random graphs with at most 10 vertices. These steps are the maximum matching of the double cover, the cover C and its size, the optimality of x against an LP solver, the kernel equivalence for every k, and the bound √2 · n^{3/2} on the search cost of step 3.

```
python sim/check_kernel.py
double cover LP, alternating cover and kernel equivalence checked on 400 random graphs, n <= 10
```

**Not formalized:** all of the folder. The matching algorithm of [2], the search algorithms of [4, 5] and the LP kernel theorem of [3] enter as known results.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. T. Terao, R. Mori. Parameterized quantum query algorithms for graph problems. arXiv:2408.03864, 2024.
2. J. Blikstad, J. van den Brand, Y. Efron, S. Mukhopadhyay, D. Nanongkai. Nearly optimal communication and query complexity of bipartite matching. FOCS 2022. arXiv:2208.02526.
3. G. L. Nemhauser, L. E. Trotter. Vertex packings: structural properties and algorithms. Mathematical Programming 8, 1975.
4. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. arXiv:quant-ph/9605034, 1996.
5. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM Journal on Computing 35(6), 2006. arXiv:quant-ph/0401091.
