# Quantum query lower bounds for every 2-connected subgraph

Written 7 Nov 2026.

## Result

Model: an N-vertex graph given by its adjacency matrix, one query per pair of vertices. Task: for a fixed graph H, decide whether the graph contains a copy of H as a subgraph, or find one.

**Theorem 1.** Let H be a fixed 2-connected graph on v ≥ 3 vertices. Every bounded-error quantum algorithm that detects, or finds, a copy of H in N-vertex graphs makes Ω(N^{1 + 1/(6(v−1))}) queries.

**Corollary 2.** Let H be a fixed connected graph and B a block of H with v ≥ 3 vertices. Suppose that
- (a) B has the most edges among the blocks of H, and at most one other block is isomorphic to B; or
- (b) every component of H − E(B) has fewer than e(H)/2 edges.

Then detecting or finding H takes Ω(N^{1 + 1/(6(v−1))}) queries.

Condition (a) holds whenever the 2-core of H is 2-connected, for example for a cycle with trees attached. It also holds for two four-cycles that share a vertex or are joined by a path, which gives Ω(N^{19/18}). Condition (b) holds, for example, for a chain of three four-cycles in which the outer ones are attached at different vertices of the middle one.

| H | Previous lower bound | This folder |
|---|---|---|
| four-cycle C4 = K_{2,2} | Ω(N) | Ω(N^{19/18}) |
| even cycle C_{2ℓ} | Ω(N) | Ω(N^{1 + 1/(6(2ℓ−1))}) |
| K_{a,b}, 2 ≤ a ≤ b | N^{β_r − o(1)} for a = b = r ≥ 10 [2] | Ω(N^{1 + 1/(6(a+b−1))}) |
| triangle | Ω(N^{13/12}) [1] | Ω(N^{13/12}) (the same) |

To our knowledge these are the first superlinear lower bounds for the four-cycle, for even cycles, for K_{r,r} with r ≤ 9 and for unbalanced K_{a,b}. Gilani and Zhou list the four-cycle and K_{r,r} with r < 10 as open [2, Section 1.4]. For non-bipartite H the bound Ω(N^{13/12}) of [1] is at least as large, so the new cases are the bipartite ones. For K_{10,10}, Theorem 1 gives 115/114, which improves β_10 = 181/180; for larger r the bounds of [2] are larger.

## The argument

The proof is the triangle lower bound of [1], run on a host graph built from H. The general step is Proposition 3 below; the 2-connected case needs only degree bounds to satisfy it.

**Host and distributions.** G is the blow-up of H: each vertex of H becomes a part of n vertices, each edge a complete bipartite graph between two parts. The algorithm knows G. The forbidden family is the edge sets of all copies of H in G, including copies that use several vertices of one part. Negative inputs are Bernoulli(p) subgraphs of G conditioned to contain no copy. A positive input plants a uniformly random copy T and conditions on T being the only copy; T is kept in a label register, as in [1, (5.3)].

**Proposition 3.** Let R = (np)^{2/3} ≥ 1 and assume:
- (P) planting T creates no other copy with probability at least 1/2;
- (S) for every vertex w, outside an event of probability b that depends only on the edges away from w, every edge at w interacts with at most d_s other edges at w;
- (I) outside an event of probability b, every edge interacts with at most d_m edges, and p d_m ≤ 1/5.

Two edges i and j interact when some copy contains both and all its other edges are present. Then every t-query algorithm that outputs the planted copy with average probability σ satisfies

    √σ ≤ (t + e(H)) · (C S n^{−7/3} p^{−1/3} + C n^4 b)^{1/2},     S = 2 + (p d_s)²/R²,

with C depending only on H. So t = Ω(n^{7/6} p^{1/6}) whenever p d_s ≤ R and b is negligible.

The proof follows [1, Section 5] step by step.
- The comparison map is (T_T f)^y = Σ_{i∈T} f^{y^{i}} − (e(H) − 1) f^{y^∅}, where y^U agrees with y outside T and has exactly the edges U of T. (P) bounds the probability ratio r_T by 2^{e(H)+1}.
- The averaging operator F_T sums the star operators L_w over the v vertices of T.
- The star estimate [1, (5.18)] uses a variant of [1, Lemma 4.4] without a spectral gap. Let Π_1, ..., Π_ℓ be orthogonal projections, L = Σ Π_i and F = (I + L/R)^{−1}. If Σ_i ‖[Π_i, L]g‖² ≤ κ²⟨g, Lg⟩ for all g, then Σ_i ⟨Π_i f, FΠ_i f⟩ ≤ (2 + κ²/(4R²)) R ‖f‖². The interaction estimate of [1, Lemma 4.5] gives κ² ≤ 3(p d_s)².
- (I) feeds [1, Lemma 4.6].
- In the candidate sums, the queried edge e = uu' splits the candidates into those containing e (O(n^{v−2}) of them) and those that meet u or u' without containing e (O(n^{v−1})). Each edge is charged to one star.

The squared query error is at most α‖f‖² + β‖f‖²_∞ with α ≤ C S n^{−3}(R/p + n/R + n²p/R²), and R = (np)^{2/3} balances the first and last terms.

**2-connected H.** Take p = c₀ n^{−(v−2)/(v−1)}, so np = c₀ n^{1/(v−1)}. Three facts about a 2-connected graph give the hypotheses. `check.py` verifies them by brute force on all 11617 2-connected graphs with at most 6 vertices.
- (F1) For every nonempty vertex set U whose complement has at least two vertices, at least |U| + 1 edges have an endpoint in U.
- (F2) H − x is connected for every vertex x.
- (F3) For distinct edges i, j, every component of H − {i, j} contains an endpoint of i.

Each hypothesis then follows:
- *Planting.* A new copy shares j ≥ 2 vertices with T. By (F1), for j ≤ v − 1 it needs at least v − j + 1 present edges outside T. The expected number of such copies is O(n^{v−j} p^{v−j+1}) = O(c₀^{v−j+1} n^{(2−j)/(v−1)}), and O(p) for j = v. Increasing events are no more likely under the conditioned distribution [1, Lemma 5.2], so (P) holds for small c₀.
- *Stars.* If wa and wb interact, then all edges of the copy minus w are present, and they lie outside the star of w. By (F2) that graph is connected, so a spanning tree rooted at a, embedded through present edges, leaves at most v³ d₀^{v−2} choices for b. Here d₀ = O(np) bounds the maximum degree outside an event of probability exp(−Ω(np)).
- *Interactions.* By (F3) the copy minus i and j has a spanning forest with v − 2 edges whose two trees contain the two endpoints of i. This leaves O(d₀^{v−2}) choices for j.

So p d_s and p d_m are O(p (np)^{v−2}) = O(c₀^{v−1}), which is small, and Proposition 3 gives t = Ω(n^{7/6} p^{1/6}) = Ω(n^{1 + 1/(6(v−1))}). Detection follows by the constant-factor reduction from search to detection for connected subgraphs [3, Lemma 23], as used in [2, Section 2.2].

**Corollary 2.** Write Br_c for the component of H − E(B) that contains the vertex c of B, and let the gadget Γ be the union of the Br_c with all vertices c identified to one root. Attach a private copy of Γ at every vertex of the input. These edges are known and cost no queries. If the input contains B, the padded graph contains H. Conversely, take a copy of H in the padded graph of a B-free input.
- Every 2-connected subgraph lies in the input or in one gadget, so the image of B lies in some gadget, at the image of a vertex u of H.
- The part Q of H beyond u that contains B then embeds into one branch Br_c, with u at c.
- Q contains B and all branches Br_{c'} except the branch Br_e on the side of u.
- Under (b), comparing edge counts gives a contradiction. If c ≠ e, Br_c is smaller than Q. If c = e, Br_e would need at least e(H)/2 edges.
- Under (a), a gadget holds one block isomorphic to B fewer than H, so B and the other such block Y sit in different gadgets, and Y lies outside Q. The embedding does not increase distances, so B lies at distance at least D = dist(B, Y) from u. A shortest path from B to Y leaves Q through u, so it reaches u within D − 1 steps, a contradiction. (If u lies on B, then D = 0, and B and Y would share the vertex u.)

So detecting H is at least as hard as detecting B.

**Limits.** Applied to H directly, the degree bounds fail at a cut vertex joining two blocks with cycles. An edge at the cut vertex interacts with about n(np)^{β−2} edges through another block with β vertices when that block minus the cut vertex is a tree. Corollary 2 avoids this by reducing to one block. Whether the block reduction holds for every block with the most edges is open; if it does, every connected graph with a cycle is superlinear. Paths, subdivided claws and stars with two subdivided legs are linear. The bound n^{7/6} p^{1/6} does not depend on H, so a pattern gains only through a larger admissible density. For cycles the planting condition already caps the density at n^{−(v−2)/(v−1)}. For cliques the admissible density is larger, see [clique-quantum-query-lower-bounds](../clique-quantum-query-lower-bounds/).

## Check

`check.py` verifies:
- (F1) to (F3) and the planting exponents, by brute force over all 2-connected graphs with 3 to 6 vertices;
- on sampled H-free subgraphs of small hosts (C4 and C6 in K_{n,n}, K4 in K_{2,2,2,2}), that the interaction counts, overall and inside a star, are at most v! D^{v−2}, with D the relevant maximum degree;
- the exponent arithmetic, with exact fractions;
- the block reduction on five graphs with cut vertices: for a B-free part and every placement of pendants into gadgets, the check finds no copy of H.

Run it with `python3 check.py` (about 3 seconds).

## References

[1] A. Cornelissen, A. S. Gilani, X. Zhou. A quantum lower bound for triangle finding. arXiv:2611.06751, 2026.

[2] A. S. Gilani, X. Zhou. Superlinear quantum query lower bounds for subgraph detection. arXiv:2609.40263, 2026.

[3] A. Cornelissen, A. S. Gilani, S. Patro. Quantum algorithms for path and cycle containment problems. APPROX/RANDOM 2026, LIPIcs 392, 72:1-72:23. arXiv:2605.09017.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.
