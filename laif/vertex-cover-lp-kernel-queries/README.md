# Vertex cover with a parameter: an LP kernel bound in the adjacency matrix model

Written 22 Nov 2026.

**Setting.** The input is a graph G on n vertices, given by its adjacency matrix: a query names a pair {u, w} and returns whether uw is an edge. For an integer k, the task is to output a vertex cover of size at most k or to decide that none exists, with probability at least 2/3.

| | Previous best bound | This folder | Status |
|---|---|---|---|
| Upper | O(√k n + k^{3/2} √n) [1, Thm 1.1] | O(√k n + k²) | Claim; checked by script |
| Lower | Ω(√k n) for k ≤ (1 − ε)n [1, Thm 1.2] | | |

With the lower bound of [1], the query complexity is Θ(√k n) for k = O(n^{2/3}), where [1] has it for k = O(√n). For √n ≤ k ≤ n the new bound is smaller than the bound of [1] by the factor min(k/√n, √(n/k)), which is n^{1/6} at k = n^{2/3}. At k = n^{3/4} it is O(n^{3/2}), against the bound O(n^{13/8}) of [1]. The bound of [1] uses a kernel built from a maximal matching and the vertices of degree above k. The bound here uses the half-integral LP kernel [2] instead, computed from a maximum matching of the bipartite double cover, which the matching algorithms of [1] find cheaply because the matching has at most 2k edges.

A graph has a vertex cover of size at most k exactly when its complement has a clique of size at least n − k, and a query to the complement is a query to G. So the same bounds hold for finding a clique of size at least n − k.

## Theorem 1

**Theorem 1.** There is a quantum algorithm that, given G in the adjacency matrix model and an integer k, outputs a vertex cover of size at most k or decides that none exists, with probability at least 2/3, using O(√k n + k²) queries.

**Algorithm.**

1. Let H be the bipartite double cover of G: its sides are L = {v_L} and R = {v_R}, and v_L w_R is an edge of H exactly when vw is an edge of G. A query to H is one query to G, or none on the diagonal.
2. Run the k-matching procedure of [1, Thm 5.3] on H with target 2k + 1. If it finds a matching of size 2k + 1, decide that no vertex cover of size at most k exists.
3. Otherwise find a maximum matching M of H with the algorithm of [1, Thm 1.9], and let U be the set of unmatched vertices of L.
4. Let Z be the set of vertices reachable from U by alternating paths, which leave L along edges outside M and leave R along edges of M. Compute Z in two phases. First, for every matched vertex w ∈ R, search U for a neighbour of w; if there is one, add w and M(w). Then, for every vertex u ∈ L that was added, find all matched vertices w ∈ R that are not yet added and are adjacent to u, and add each such w and M(w). Let C = (L ∖ Z) ∪ (R ∩ Z).
5. Let x_v = |C ∩ {v_L, v_R}|/2 and V_i = {v : x_v = i} for i ∈ {0, 1/2, 1}. Let k′ = k − |V_1|. If k′ < 0 or |V_{1/2}| > 2k′, decide that no vertex cover of size at most k exists.
6. Otherwise query all pairs inside V_{1/2}. Compute a minimum vertex cover S of G[V_{1/2}] without queries. If |S| ≤ k′, output V_1 ∪ S, and otherwise decide that none exists.

Each step that can fail is repeated O(1) times, so that all of them succeed together with probability at least 2/3. A matching that a procedure returns can be checked edge by edge, and in step 3 the largest of the returned matchings is kept.

*Proof.* The maximum matching size of H equals the minimum vertex cover size of H, which is twice the LP optimum of G [2]. That optimum is at most the minimum vertex cover size of G. So a matching of size 2k + 1 in H proves that G has no vertex cover of size at most k, and if step 2 finds none, then p = |M| ≤ 2k.

*The set Z.* An unmatched vertex of R cannot be reached, since that would give an augmenting path. So only matched vertices of R need to be searched. A vertex of R reached from U is found in the first phase. A vertex reached later is found from the vertex u ∈ L that reaches it, and it is not matched to u, because the partner of u was added before u. Hence the two phases compute Z.

*The cover C.* A matched vertex u ∈ L enters Z only through its partner, so u ∈ Z exactly when M(u) ∈ Z, and every edge of M has exactly one endpoint in C. Every vertex of C is matched, so |C| = |M|. An edge u w of H with u ∈ L ∩ Z and w ∈ R ∖ Z would be found by the search, so every edge of H meets C. Every vertex cover of H has at least |M| vertices, so C is a minimum vertex cover of H.

*The kernel.* For an edge vw of G, the set C covers both v_L w_R and w_L v_R, so |C ∩ {v_L, v_R, w_L, w_R}| ≥ 2 and x_v + x_w ≥ 1. The value of x is |C|/2, which is the LP optimum, so x is an optimal solution of the vertex cover LP of G. By [2], G has a minimum vertex cover that contains V_1 and avoids V_0. Hence G has a vertex cover of size at most k exactly when G[V_{1/2}] has one of size at most k′. No edge joins V_0 to V_{1/2}, so an LP solution of G[V_{1/2}] with value below |V_{1/2}|/2 would improve x. Every vertex cover of G[V_{1/2}] therefore has at least |V_{1/2}|/2 vertices. If |V_{1/2}| > 2k′ the answer is no, which justifies step 5.

*The output.* Let S be a vertex cover of G[V_{1/2}]. No edge lies inside V_0 or joins V_0 to V_{1/2}. An edge with an endpoint in V_1 is covered by V_1, and the remaining edges lie inside V_{1/2} and are covered by S. So V_1 ∪ S is a vertex cover of G.

*Queries.* Steps 2 and 3 make O(√k n + k²) queries [1, Thms 5.3 and 1.9], since H has 2n vertices and p ≤ 2k. In step 4, the first phase runs one search over U for each of the p matched vertices of R, each with O(√n) queries [3]. In the second phase at most p vertices u search the set of not yet added matched vertices of R, which has at most p elements. If t_u vertices are added from u, repeating the search of [3] finds them with O(√(p (t_u + 1))) queries in expectation [3, 4]. Since Σ_u √a_u ≤ √(p Σ_u a_u) for p nonnegative terms a_u, and Σ_u (t_u + 1) ≤ 2p, the second phase costs at most √2 · p^{3/2} in expectation. With failure probability 1/(10p) for each search, step 4 makes O((p √n + p^{3/2}) log p) = O(k √n log k + k^{3/2} log k) queries. This is O(√k n + k²): if k ≤ n/log² k the first term is at most √k n, and otherwise both terms are at most k². Step 6 makes at most |V_{1/2}|²/2 ≤ 2k² queries. ∎

The term k² comes from the matching algorithm and from reading the kernel. A smaller cost for the kernel would need to decide whether a graph on at most 2k′ vertices whose LP optimum is half its vertex count has a vertex cover of size at most k′, with o(k′²) queries. For this the best known bound is O(k′²) [1].

## Script

`sim/check_kernel.py` checks the classical steps on random graphs. On 400 graphs with at most 10 vertices it checks the maximum matching of the double cover, the cover C and its size, the optimality of x against an LP solver, and the kernel equivalence for every k. On 600 graphs with at most 40 vertices it checks that the two-phase search of step 4 computes the same set Z as a full alternating search, and that its search cost is at most p √n + √2 · p^{3/2}.

```
python sim/check_kernel.py
double cover LP, alternating cover and kernel equivalence checked on 400 random graphs, n <= 10
two-phase alternating search: same Z and cost <= p sqrt(n) + sqrt(2) p^{3/2} on 600 random graphs, n <= 40
```

**Not formalized:** all of the folder. The matching algorithms of [1], the search algorithms of [3, 4] and the LP kernel theorem of [2] enter as known results.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. T. Terao, R. Mori. Parameterized quantum query algorithms for graph problems. arXiv:2408.03864, 2024.
2. G. L. Nemhauser, L. E. Trotter. Vertex packings: structural properties and algorithms. Mathematical Programming 8, 1975.
3. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. arXiv:quant-ph/9605034, 1996.
4. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM Journal on Computing 35(6), 2006. arXiv:quant-ph/0401091.
