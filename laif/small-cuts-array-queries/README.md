# Small cuts and flows with adjacency array queries

Written 21 Nov 2026.

**Setting.** G is a simple undirected graph with n vertices and m edges, given in the adjacency array model: a query returns the degree of a vertex, or the i-th entry of the neighbour list of a vertex, in an arbitrary fixed order. Only queries are counted, not time. Write λ for the edge connectivity of G, and f = λ_st for the minimum number of edges whose removal separates two given vertices s and t. Classically, even deciding whether s and t are connected takes Ω(m) queries in this model [4].

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | k forest certificate, k ≤ n | min{m, Õ(k√(mn))} queries, implied by [1] | O(n k^{3/2} log n) queries | Claim; Lean for the certificate and the arithmetic of the counting lemmas |
| Thm 4 | k forest certificate, k ≤ n, by a scan | min{m, Õ(k√(mn))} queries, implied by [1] | O(n + √(mnk) + √(mn) log n) queries | Claim; Lean for Lemma 4, the certificate and the count of found entries |
| Thm 2 | edge connectivity λ and a minimum cut | Õ(√(mn)) queries [2] | O(n (λ+1)^{3/2} log n) queries | Claim; Lean for the certificate |
| Thm 3 | λ_st, a minimum s-t cut and a maximum s-t flow | λ_st: Õ(n + min{m, n^{3/2}}) [3]; λ_st and flow: min{m, Õ((f+1)√(mn)), Õ(n^{7/6}√m)}, implied by [1] and from [8] | O(n (f+1)^{3/2} log n) queries | Claim; Lean for the certificate |
| Thm 5 | λ_st, a minimum s-t cut and a maximum s-t flow | as for Theorem 3 | Õ(n + √(mn(f+1))) queries | Claim; Lean for Lemma 4 and the certificate |

For bounded λ this gives Θ̃(n) queries for edge connectivity, since deciding connectivity already needs Ω(n) queries [1]. For simple graphs Θ̃(n) was suspected in [2] in this model. On dense simple graphs the complexity is Θ̃(n^{3/2}) [3, 6], so the answer depends on λ. Up to logarithmic factors, Theorem 2 uses fewer queries than [2] when λ³ < m/n.

The bounds implied by [1] come from augmenting paths: the residual out-list of a vertex is its array with known holes, so each path takes one directed path search of [1] with Õ(√(mn)) queries. Up to logarithmic factors, Theorem 3 uses fewer queries than this when f < m/n, and fewer than [3] when f < min{n^{1/3}, (m/n)^{2/3}}. It computes a maximum s-t flow with o(m) queries whenever f^{3/2} log n = o(m/n), against f = o(√(m/n)) for augmenting paths. Theorem 5 uses fewer queries than augmenting paths by a factor of about √(f+1), and fewer than [3] when f < min{m/n, n²/m}, up to logarithmic factors. It computes a maximum s-t flow with o(m) queries whenever f = o(m/n) and m/n grows faster than log⁴ n. Since f is at most the degree of s, this covers every f below the average degree up to such a factor. Theorem 3 is the smaller of the two when m > n(f+1)². The algorithms of [3, 4] compute the value and a minimum cut, and [4] asks for a sublinear quantum algorithm for a maximum flow in general. For unit capacities, also in directed graphs, a maximum flow is computed in [8] in time Õ(min{n^{7/6}√m, m√n}).

## 1. The certificate

Let F_1 be a maximal spanning forest of G_1 = G, and F_i a maximal spanning forest of G_i = G − (F_1 ∪ … ∪ F_{i−1}). Let H_k = F_1 ∪ … ∪ F_k. For a vertex set S write δ_G(S) for the set of edges of G with exactly one endpoint in S.

**Lemma 1 (certificate [5]).** For every S, |δ_{H_k}(S)| ≥ min{k, |δ_G(S)|}. If |δ_{H_k}(S)| < k, then δ_{H_k}(S) = δ_G(S).

*Proof.* If some edge of δ_G(S) lies in G_i, its endpoints are connected in F_i, so a path of F_i crosses S and F_i has an edge in δ(S). If this holds for all i ≤ k, the k forests are edge-disjoint and give k edges across S. Otherwise some G_i with i ≤ k has no edge across S, so all of δ_G(S) lies in H_{i−1} ⊆ H_k. The second claim follows since H_k ⊆ G. ∎

H_k has at most k(n − 1) edges. Since λ_st is the least |δ(S)| over the sets S that contain s and not t, λ_st(H_k) ≥ min{k, λ_st(G)} for every pair s, t.

## 2. One round with holes

Round i builds F_i from the array of G, while H_{i−1} is known. An entry of the list of u is a *hole* if it is an edge of H_{i−1}. Every edge of H_{i−1} is a known vertex pair, so reading an entry tells at once whether it is a hole. Its position in the list of one endpoint may still be unknown. Write r(u) for the number of holes in the list of u and d_i(u) = deg(u) − r(u) for the degree in G_i. Then Σ_u r(u) = 2|H_{i−1}| ≤ 2(i − 1)n. Entries read once stay known, so later rounds read them for free.

The round follows the O(n) connectivity algorithm of [1] (Lemma 10 and Theorem 11 there), with d_i in place of the degree.

**Phase 1 (stars).** While some vertex is unassigned, take an unassigned vertex v of largest d_i(v). Read its list in order, skipping holes. Each new neighbour joins v's star, until the list ends or an entry leads to a vertex of an earlier component, which the star then joins. Every read entry adds a vertex, ends a star or is a hole, so Phase 1 reads at most 2n entries plus the holes it meets. As in [1], every component C has Σ_{u∈C} d_i(u) ≤ |C|²:

- a star that ends its list has a root of degree d, with d neighbours of degree at most d, so the total is at most d + d² < (d + 1)²;
- a star of b vertices that joins a component of a vertices adds at most b·d, and a² + bd < (a + b)² when a ≥ d. Here a ≥ d + 1: a component is created by a star whose root v′ reads its whole list, so it starts with d_i(v′) + 1 vertices, where d_i(v′) ≥ d because v was unassigned when v′ was chosen, and components only grow.

**Phase 2 (searches).** Repeatedly take the unfinished component C with the fewest list entries, N_C = Σ_{u∈C} deg(u), and search its N_C entries for an edge of G_i that leaves C. Use Grover search with error at most n^{−3}, so O(√N_C log n) queries. A found edge goes into F_i and merges C with another unfinished component. If none is found, C is a component of G_i and is finished. Components only merge along edges of G_i, so F_i is a maximal spanning forest of G_i with high probability.

**Cost.** Charge the √N_C of a search evenly to the N_C entries of C. The searched component is always the smallest unfinished one and merges with an unfinished component at least as large, so the components that contain a fixed entry and get searched at least double in size each time [1]. An entry in a Phase 1 component C₀ therefore pays at most 5/√N_{C₀}. With N_{C₀} ≤ |C₀|² + Σ_{u∈C₀} r(u) and

Σ_C √(a_C² + b_C) ≤ Σ_C a_C + √(c · Σ_C b_C)   for c components,

the round costs O((n + √(n · (i − 1)n)) log n) = O(n √i log n) queries, plus the holes read.

**Theorem 1.** For k ≤ n, with bounded error, F_1, …, F_k can be computed with O(n k^{3/2} log n) queries.

*Proof.* There are n degree queries. Each entry is read as a hole at most once, which adds at most 2kn. Round i costs O(n √i log n), and Σ_{i≤k} √i ≤ k^{3/2}. Each round has at most 2n searches, each with error at most n^{−3}, and there are at most n rounds, since λ, f ≤ n − 1 in Theorems 2 and 3. ∎

## 3. Edge connectivity and s-t flows

**Theorem 2.** With bounded error, λ and a minimum cut of G can be computed with O(n (λ+1)^{3/2} log n) queries, with no knowledge of λ.

*Proof.* After round i, compute λ(H_i) classically and stop as soon as λ(H_i) < i. By Lemma 1, λ(H_i) ≥ min{i, λ}, so the stop happens by round λ + 1. When it happens, a minimum cut S of H_i has |δ_{H_i}(S)| < i, so δ_G(S) = δ_{H_i}(S) by Lemma 1, and every S' has |δ_G(S')| ≥ |δ_{H_i}(S')| ≥ λ(H_i) = |δ_G(S)|. ∎

**Theorem 3.** With bounded error, λ_st, a minimum s-t cut and a maximum s-t flow can be computed with O(n (f+1)^{3/2} log n) queries, with no knowledge of f.

*Proof.* Stop after the first round i with λ_st(H_i) < i, which comes by round f + 1. Then λ_st(H_i) = f, a minimum s-t cut of H_i is one of G as in Theorem 2, and a maximum s-t flow of H_i is a flow in G of value f, hence a maximum flow of G. ∎

In particular, k-edge-connectivity of G can be decided with O(n k^{3/2} log n) queries.

## 4. A scan with all solutions

The forests can also be built in one pass, by the scan-first search of [5] with labels capped at k. Every vertex w has a counter r(w), initially 0. Repeatedly scan an unscanned vertex v of largest label min{k, r(v)}. To scan v, find all entries of its list that lead to an unscanned vertex w with r(w) < k. For each of them, put vw into F_{r(w)+1} and increase r(w) by one.

**Lemma 4.** For i ≤ k, F_i is a forest, and every edge of G outside F_1 ∪ … ∪ F_{i−1} joins two vertices connected in F_i. So Lemma 1 applies.

*Proof.* Orient each edge of F_i towards its endpoint scanned later. A vertex w receives at most one such edge, when r(w) rises from i − 1 to i, and edges point forward in the scan order, so F_i is a forest. Cut the scan order into *i-runs*: a new run starts at every vertex whose label is below i when it is scanned. While some unscanned w has r(w) ≥ i, the scanned vertex has label at least i, so no run starts. Hence a vertex w with label at least i at its scan lies in the same run as the vertex p whose scan raised r(w) to i, and pw ∈ F_i. By induction along the scan order, each run is connected in F_i. Now let vw be an edge outside F_1 ∪ … ∪ F_{i−1}, with v scanned first. When v is scanned, r(w) ≥ i − 1, since otherwise vw would lie in F_{r(w)+1} with r(w) + 1 ≤ i − 1. Edges in no forest have r(w) ≥ k ≥ i. If r(w) = i − 1, then vw ∈ F_i, since i − 1 < k. If r(w) ≥ i, the vertex p that raised r(w) to i was scanned before v, and no run starts between p and w, so v and w lie in the run of p. ∎

**Theorem 4.** For k ≤ n, with bounded error, F_1, …, F_k can be computed with O(n + √(mnk) + √(mn) log n) queries.

*Proof.* Query all degrees. When v is scanned, call an entry of its list marked if it is not yet found and leads to a vertex w that was unscanned with r(w) < k at the start of the scan. A found entry changes r only for its own w, which appears once in the list of v, so no other entry changes its status during the scan. Let t_v be the number of marked entries. Find them one at a time with the search of [7] for an unknown number of solutions, which takes expected O(√(deg(v)/j)) queries while j of them remain, and cut each search off after c√deg(v) log n queries. For a suitable constant c, a cut-off search misses a remaining marked entry with probability at most n^{−4}, and the first cut-off ends the scan of v. So the scan of v takes expected O(√(deg(v) t_v) + √deg(v) log n) queries, with error at most (t_v + 1) n^{−4}. Each counter rises at most k times, so Σ_v t_v ≤ kn, and by the Cauchy-Schwarz inequality

Σ_v √(deg(v) t_v) ≤ √(2m · kn),   Σ_v √deg(v) ≤ √(2m · n).

After the degree queries the expected total is known up to the constant, so stopping at ten times it gives bounded error. ∎

This proof is an instance of the approach of [9, 10]: a classical algorithm that makes few wrong guesses about the answers to its queries (here, that an entry is not marked) runs with about √(queries · wrong guesses) quantum queries.

**Theorem 5.** With bounded error, λ_st, a minimum s-t cut and a maximum s-t flow can be computed with O((√(mn(f + 1)) + (n + √(mn) log n) log(f + 2)) log log(f + 4)) queries, with no knowledge of f.

*Proof.* Run stages j = 0, 1, 2, … with k = 2^j, and stop at the first k with λ_st(H_k) < k, which comes once k > f, so k ≤ 2f + 2. The output is correct as in Theorem 3. Stage j runs the algorithm of Theorem 4 with a cut-off at twice its expected cost E_j. A cut-off is noticed, and then the stage starts again, up to ⌈log₂(10(j + 1)²)⌉ + 1 times. Each attempt exceeds its cut-off with probability at most 1/2, so stage j fails with probability at most 1/(10(j + 1)²), and all stages together with probability below 0.17, plus the small error of the searches. Stage j costs O(E_j log(j + 2)) queries, with E_j = O(n + √(mn2^j) + √(mn) log n). The terms √(mn2^j) form a geometric sum. ∎

## Lean

The library `SmallCut` in `lean/` (Lean 4, Mathlib at the revision pinned in `lean/lakefile.toml`) proves, with only the standard axioms (`lean/axioms.txt`):

- `SmallCut.certificate`: for edge-disjoint subgraphs F 0, F 1, … such that, for i < k, every edge of G outside F 0, …, F (i − 1) joins two vertices connected in F i, the union of F 0, …, F (k − 1) has at least min{k, c} edges across every vertex set S, where c is the number of edges of G across S (Lemma 1);
- `SmallCut.certificate_eq`: if moreover each F i is a subgraph of G and the union has fewer than k edges across S, then G has the same number (Lemma 1, second part);
- `SmallCut.cross_of_reachable`: a path from S to its complement has an edge across S;
- `SmallCut.star_bound_end`, `SmallCut.star_bound_merge`: the arithmetic of the two cases of the Phase 1 degree bound, with the bounds on the stars (s ≤ d + d² and t ≤ b d) as hypotheses;
- `SmallCut.sum_sqrt_le`: Σ √(a_C² + b_C) ≤ Σ a_C + √(c · Σ b_C);
- `SmallCut.scan_hmax` (Lemma 4): for an injective scan order `pos` that obeys the rule of Section 4, `hscan`, and for i < k, every edge of G outside forests 0, …, i − 1 of the scan joins two vertices connected in forest i. Forest i of the scan, `scanF`, holds the edges vw with pos v < pos w for which exactly i neighbours of w come before v. This is the forest that the scan with counters gives, since r(w) = min{k, number of earlier neighbours} at every step;
- `SmallCut.scan_run`: a stretch of the scan with no new run is connected in forest i;
- `SmallCut.scan_parent_unique`: each vertex has at most one earlier neighbour in forest i (that F_i has no cycle follows from this as in the proof of Lemma 4, and is not stated in Lean);
- `SmallCut.scan_certificate`: Lemma 1 for the scan;
- `SmallCut.sum_found_le`: the scan finds at most k·|V| entries in total;
- `SmallCut.certificate_needs_hmax`, `SmallCut.triangle_scan_rule`, `SmallCut.triangle_forest_one_adj` (content of the statements, in `lean/SmallCut/NonVacuity.lean`): without the hypothesis on the edges outside earlier forests, the bound of `certificate` fails for a single edge and empty forests; the scan rule `hscan` holds on the triangle with k = 2, and forest 1 of that scan has an edge, so `scan_hmax` at i = 1 is about a non-empty forest.

**Not formalized:** the query algorithms and their costs (Theorems 1, 4 and 5), the link between the counters r(w) and `scanF`, the bound a ≥ d + 1 of Phase 1, the charging argument of [1], Grover search, and the max-flow min-cut theorem used for Theorem 3.

## Scripts

`sim/check_cert.py` runs Phases 1 and 2 classically on random graphs, pairs of cliques with few joining edges, regular graphs and graphs with hubs, on up to 16 vertices and k ≤ 6. It asserts that every F_i is a maximal spanning forest of G_i, the bound a ≥ d + 1 and the degree bound of Phase 1, λ_st(H_k) ≥ min{k, λ_st(G)} for all pairs, and λ(H_k) = λ(G) when λ(H_k) < k. It also counts the round cost, with √(N_C/t) for a search with t solutions and √N_C for a failed one, and reports it against n + √(2n|H_{i−1}|), together with the totals on graphs with 300 vertices for k up to 16.

`sim/check_scan.py` runs the capped scan of Section 4 with random tie breaking on random graphs, pairs of cliques and graphs with hubs, on up to 16 vertices and k ≤ 5. It asserts Lemma 4 for every i ≤ k and λ_st(H_k) ≥ min{k, λ_st(G)} for all pairs, and reports Σ_v √(deg(v)(t_v + 1)) against √(2mnk) + √(2mn) on graphs with 300 vertices.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check script, and to draft the text.

## References

[1] C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006. arXiv:quant-ph/0401091.

[2] S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021. arXiv:2011.09823.

[3] T. Lu, R. Ren, S. Liu. Tight quantum query bounds for minimum cut and multicut on dense graphs. arXiv:2611.17845.

[4] S. Apers, B. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.

[5] H. Nagamochi, T. Ibaraki. A linear-time algorithm for finding a sparse k-connected spanning subgraph of a k-connected graph. Algorithmica 7, 1992.

[6] Minimum cut in the adjacency array model, `laif/minimum-cut-array-queries` in this repository.

[7] M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46(4-5), 1998. arXiv:quant-ph/9605034.

[8] A. Ambainis, R. Špalek. Quantum algorithms for matching and network flows. STACS 2006. arXiv:quant-ph/0508205.

[9] C. Y.-Y. Lin, H.-H. Lin. Upper bounds on quantum query complexity inspired by the Elitzur-Vaidman bomb tester. Theory of Computing 12, 2016. arXiv:1410.0932.

[10] S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. Quantum 4, 2020. arXiv:1905.13095.
