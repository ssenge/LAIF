# Recognizing cluster graphs with quantum queries

Written 11 Nov 2026.

**Setting.** G is a graph on n vertices, given by its adjacency matrix: a query (u, v) returns whether uv is an edge. G is a *cluster graph* if it is a disjoint union of cliques. Equivalently, the relation "u = v or uv is an edge" is an equivalence relation, and G has no induced path on three vertices: no vertices a, b, c with ab and bc edges and ac a non-edge. Classically, Θ(n²) queries are needed, since the complete graph and the complete graph minus one edge differ in a single entry.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Is G a cluster graph? | Ω(n) quantum; Õ(n^{4/3}) and about n^{9/7} suggested by the general algorithms for patterns on three vertices [1, 2], not stated for induced patterns; Θ(n²) classically | Θ(n), with one-sided error | Claim; Facts 1 and 2, Lemma 3 and the success bound checked by script |

A rejection comes with an induced path on three vertices, found and checked by the algorithm, and a cluster graph is always accepted. By complementing every query, the same bound holds for complete multipartite graphs.

## 1. A vertex with many witnesses

Write N[x] for the closed neighbourhood of x and d_x for its degree.

**Fact 1.** G is a cluster graph iff it has no induced path on three vertices, iff N[x] = N[z] for every edge xz.

**Fact 2.** If xz is an edge and w ∉ {x, z} is adjacent to exactly one of x and z, then G has an induced path on three vertices: (z, x, w) if w is adjacent to x, and (x, z, w) otherwise. Such a w exists iff N[x] ≠ N[z].

Call a neighbour z of x *unequal* if N[z] ≠ N[x].

**Lemma 3.** If xz is an edge with N[x] ≠ N[z], then x or z has at least half of its neighbours unequal. So every graph that is not a cluster graph has a vertex with an unequal neighbour and with at least half of its neighbours unequal.

*Proof.* Let s_x be the number of neighbours y of x with N[y] = N[x], and u_x the number of unequal ones, so d_x = s_x + u_x. The vertex z and every neighbour y of z with N[y] = N[z] are unequal neighbours of x: x lies in N[z] = N[y] and differs from y. So u_x ≥ s_z + 1, and in the same way u_z ≥ s_x + 1. If both x and z had fewer than half of their neighbours unequal, then u_x < s_x and u_z < s_z, so s_z + 1 ≤ u_x < s_x ≤ u_z − 1 < s_z − 1, which is impossible. The second sentence follows from Fact 1. ∎

## 2. The algorithm

The base procedure has three steps.

1. Pick x uniformly.
2. Pick a neighbour z of x by a search over the other n − 1 vertices, with a number of iterations drawn uniformly from 0, …, ⌈√n⌉ and held in a register, so that the procedure stays unitary.
3. Query xz, and search the other n − 2 vertices for a vertex w adjacent to exactly one of x and z, again with a random number of iterations up to ⌈√n⌉, at two queries per iteration.

The algorithm applies amplitude amplification [4] to the event that xz is an edge and w is found, and checks the resulting path with three queries before it rejects.

**Theorem 1.** Recognizing cluster graphs takes Θ(n) quantum queries, with one-sided error.

*Proof.* A rejection always comes with a checked induced path, so cluster graphs are accepted. Suppose G is not a cluster graph, and let x be a vertex as in Lemma 3. A search over N items with t ≥ 1 marked ones and a number of iterations drawn uniformly below m finds a marked item with probability at least 1/4 when m ≥ 1/sin 2θ, where sin² θ = t/N [3, Lemma 2]. For 1 ≤ t ≤ N − 1, sin 2θ = 2√(t(N − t))/N ≥ 2√(N − 1)/N, so m = ⌈√n⌉ suffices, and for t = N every outcome is marked. The outcome is uniform over the marked items. So the base procedure picks this x with probability 1/n, an unequal neighbour z with probability at least 1/8, and then w with probability at least 1/4. Its success probability is at least 1/(32n), and it costs at most 3⌈√n⌉ + 1 ≤ 3√n + 4 queries. Amplitude amplification with an unknown success probability uses O(√n) applications [4], so O(n) queries in total.

For the lower bound, an algorithm for cluster graphs tells the complete graph from the complete graph minus any one of Θ(n²) edges, so it computes OR on Θ(n²) bits, which needs Ω(n) queries. ∎

## Scripts

`sim/check_cluster.py` checks Facts 1 and 2, Lemma 3 for every edge, and that the base procedure, with inner search steps that always succeed, succeeds with probability at least 1/(2n), on 3300 random graphs: cluster graphs with random clique sizes, perturbed by added, removed or switched edges, and dense random graphs.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.

## References

1. F. Magniez, M. Santha, M. Szegedy. Quantum algorithms for the triangle problem. SIAM J. Comput. 37(2), 2007. arXiv:quant-ph/0310134.
2. T. Lee, F. Magniez, M. Santha. Improved quantum query algorithms for triangle finding and associativity testing. SODA 2013. arXiv:1210.1014.
3. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
4. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemp. Math. 305, 2002. arXiv:quant-ph/0005055.
