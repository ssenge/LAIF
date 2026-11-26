# Quantum query complexity of Gomory-Hu trees

Written 26 Nov 2026.

A Gomory-Hu tree of an undirected graph G on n vertices is a weighted tree on the same vertices such that, for every pair u, v, the smallest edge weight on the tree path from u to v equals λ(u, v), the value of a minimum u-v cut in G, and the two components left after removing that edge form a minimum u-v cut. Here G is simple and unweighted, with m edges, minimum degree δ and maximum degree Δ. In the adjacency-array model a query returns the degree of a vertex or its i-th neighbour (Theorem 1 uses only these two kinds of query, no pair queries); in the adjacency-matrix model a query names a pair {u, v} and returns whether uv is an edge. Reading the graph and computing offline costs O(m) array queries or O(n²) matrix queries. Global minimum cut has quantum query complexity Θ̃(n^{3/2}) on dense graphs in both models [1, 2].

**Theorem 1 (adjacency array).** A bounded-error quantum algorithm outputs a Gomory-Hu tree of G with

Õ(m √Δ / δ) and Õ(√(mn) · Δ^{1/4})

adjacency-array queries, whichever is smaller. More generally, for every threshold D ≥ √Δ the algorithm uses Õ(vol(L_D) + √(mn) + m √Δ / D) queries, where vol(L_D) is the sum of the degrees below D. The bound counts queries only; the offline computation between queries is not bounded. This is Õ(√(mn)) when Δ = O(δ), Õ(n^{3/2}/ε) when δ ≥ εn, and Õ(n^{7/4}) on every graph with n vertices, the exponent of the classical cut-query algorithm of [3]. Because a Gomory-Hu tree gives the global minimum cut, the lower bound of [2] for (n/3 − 1)-regular graphs makes the bound tight up to polylogarithmic factors there: Gomory-Hu trees of dense near-regular graphs cost Θ̃(n^{3/2}) queries, the same as one global minimum cut.

**Theorem 2 (adjacency matrix).** Every bounded-error quantum algorithm that outputs all values λ(u, v) from the adjacency matrix makes Ω(n²) queries. The same holds for the values λ(r, v) from a single fixed source r, and therefore for Gomory-Hu trees. The bound holds on graphs with at least n²/16 edges in which every value equals min(deg u, deg v), so these problems cost Θ(n²) matrix queries.

Status: Claim for both theorems. The lemmas, the star model and the hard family are checked by script, and Lemma 4 is proved in Lean.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Gomory-Hu tree, adjacency array, simple graphs | O(m) by reading the graph; no quantum algorithm known to us; Ω(n^{3/2}) on dense graphs from global minimum cut [2]; Õ(n^{7/4}) classical cut queries, in the cut-query model [3] | Õ(min(m√Δ/δ, √(mn) Δ^{1/4})), so Õ(n^{7/4}) on every graph; Θ̃(n^{3/2}) on dense near-regular graphs |
| All-pairs and single-source minimum cut values, Gomory-Hu tree, adjacency matrix | O(n²) by reading the matrix; no quantum lower bound for all pairs known to us | Ω(n²), so Θ(n²), on dense graphs |

## Theorem 1: the algorithm

Two facts about a minimum u-v cut (S, T) of value c drive the algorithm.

- *Friendliness.* Every x ∈ S ∖ {u} has at least d_x/2 neighbours in S. Moving x to T changes the value by deg_S(x) − deg_T(x), which is not negative because (S, T) is minimum.
- *Small value.* Call a pair trivial if λ(u, v) = min(d_u, d_v). Trivial pairs need nothing beyond the degrees. If the pair is not trivial, that is c < min(d_u, d_v), then c < Δ. This value c is the cut value in G; the sparsifier enters only through the inequality w_H(S) ≤ 1.1 w_G(S).

Let φ = 200 Δ/δ² and fix the constants below.

1. Query all degrees, n queries. Compute a (1 ± 1/10) spectral sparsifier H of G with Õ(√(mn)) queries [4, Theorem 1], which uses only degree and neighbour queries and needs m ≥ 10n (for smaller m the algorithm reads the graph). Every cut of H has weight within a factor 1 ± 1/10 of the same cut of G, and so has every weighted degree.
2. Offline, decompose H into clusters such that for every cluster C and every X ⊆ C,
   e_H(X, C ∖ X) ≥ φ · min(vol_H(X), vol_H(C ∖ X)),
   where vol_H is the sum of weighted degrees in H (not in H[C]). Splitting a cluster along any cut that violates this inequality, and charging the cut to the side of smaller volume, gives such a decomposition with total inter-cluster weight O(φ vol_H(V) log n), since each vertex is on the smaller side at most O(log n) times.
3. For every vertex x of cluster C, estimate d_C(x)/d_x, the fraction of its neighbours inside C, to within ±0.005 by amplitude estimation on its neighbour array, O(log n) queries per vertex. Let Z_C be the vertices whose estimate is at most 0.52, and call C'' = C ∖ Z_C the core of C. Each vertex of Z_C has at least 0.475 d_x edges leaving C, so vol(Z_C) ≤ 2.2 |∂C|.
4. For every vertex x, find all neighbours outside the core of x (all neighbours if x lies in no core) with Grover search, O(√(d_x (out_x + 1)) log n) queries, where out_x is their number.
5. Offline, build the star model G̃: keep every edge of G that does not join two vertices of the same core, and for each core C'' add a new vertex K joined to every x ∈ C'' by an edge of weight d_x − out_x. Output a Gomory-Hu tree of G̃ for the terminal set V.

**Lemma 3 (cores).** Let (S, T) be a minimum u-v cut of value c < min(d_u, d_v). For every core C'', either C'' ∩ S ⊆ {u} or C'' ∩ T ⊆ {v}.

*Proof.* Let X = C ∩ S and Y = C ∩ T. Every H-edge between X and Y crosses S, so e_H(X, Y) ≤ w_H(S) ≤ 1.1 c. By step 2, one of the two sets, say X, has vol_H(X) ≤ 1.1c/φ, so vol_G(X) ≤ 1.23 c/φ < 1.23 Δ/φ and |X| ≤ vol_G(X)/δ < 0.01 δ. Suppose that x ∈ C'' ∩ S with x ≠ u. Then x ≠ v, and by friendliness x has at least d_x/2 neighbours in S. At most |X| < 0.01 d_x of them lie in C, so more than 0.49 d_x lie outside C. Hence d_C(x) < 0.51 d_x, its estimate is at most 0.515, and x ∈ Z_C, which is a contradiction. If Y is the smaller set, the same argument gives C'' ∩ T ⊆ {v}. ∎

*Correctness.* All amplitude estimates and Grover searches succeed with probability 1 − 1/poly(n) after O(log n) repetitions each, by a union bound over the n vertices; assume they do. Consider a cut of G̃ that meets a core C'' in Q, with the vertex K of that core on the side of C'' ∖ Q. Wherever K lies, the star edges contribute at least e(Q, C'' ∖ Q), and with K on the side of C'' ∖ Q they contribute exactly e(Q, C'' ∖ Q) when |Q| ≤ 1. So every cut of G̃ is at least the corresponding cut of G. For a trivial pair, the single vertex of smaller degree is a cut of value min(d_u, d_v) in both graphs. For a nontrivial pair, Lemma 3 gives a minimum u-v cut of G that meets every core in at most one vertex or in all but one, and G̃ has a cut of the same value. Hence λ_G̃(u, v) = λ_G(u, v) for all u, v ∈ V, and every minimum cut of G̃ is a minimum cut of G. A Gomory-Hu tree of G̃ for the terminals V is therefore one of G. The weights d_x − out_x are exact, and no pair inside a core has to be tested for adjacency.

*Cost.* Let W = Σ_x out_x, which counts each edge from both endpoints, with out_x = d_x for x ∈ Z_C. Then W ≤ Σ_C (|∂_G C| + 2 vol(Z_C)) ≤ 5.4 Σ_C |∂_G C|, and Σ_C |∂_G C| is at most 2/0.9 times the inter-cluster weight of H, which is O(φ m log n). So W = O(Δ m log n/δ²), and by Cauchy-Schwarz step 4 costs Õ(√(Σ_x d_x · W) + √(mn)) = Õ(m √Δ/δ). The other steps cost Õ(√(mn)) and O(n log n), and m √Δ/δ ≥ √(mn/2) always. If φ ≥ 1, the bound is Ω(m) and the algorithm reads the graph instead.

*Low degrees.* For a threshold D ≥ √Δ, let L_D be the vertices of degree below D. The algorithm reads all their neighbours, vol(L_D) queries, and runs steps 2 to 5 on V ∖ L_D: the decomposition of step 2 is a decomposition of the vertex set V ∖ L_D, still with the full weighted degrees as volumes, and φ = 200 Δ/D². Every set X in the proof of Lemma 3 now lies in V ∖ L_D, so |X| ≤ vol_G(X)/D < 0.01 D ≤ 0.01 d_x, and the proof goes through with neighbours in L_D counted as outside C. Edges at L_D are known, so step 4 searches only for neighbours outside the core and outside L_D, and the vertices of Z_C, whose volume is at most 2.2 (|∂C| + e(C, L_D)), are read in full. The cost is Õ(vol(L_D) + √(mn) + m √Δ/D + Δ m/D²), and the last term is at most the third for D ≥ √Δ. With D = δ this is the first bound. Since vol(L_D) ≤ nD, the choice D = (m √Δ/n)^{1/2} gives Õ(√(mn) Δ^{1/4}) whenever m ≥ n √Δ; for smaller m this exceeds m, and reading the graph is cheaper.

## Theorem 2: the hard family

Let 3 ≤ s < h and n = 2(h + s). The vertex set is L ∪ R with L = L₁ ∪ L₂ and R = R₁ ∪ R₂, where |L₁| = |R₁| = s and |L₂| = |R₂| = h. The sets L and R are cliques, every vertex of L₂ is adjacent to every vertex of R₂, and B ⊆ L₁ × R₁ is an arbitrary set of further edges. Write N = h + s and Δ = 2h + s − 1. Vertices of L₂ ∪ R₂ have degree Δ, and a vertex x ∈ L₁ ∪ R₁ has degree N − 1 + deg_B(x) ≤ h + 2s − 1 < Δ.

**Lemma 4.** Every cut (S, T) with |S| ≥ 2 and |T| ≥ 2 has at least Δ crossing edges.

*Proof.* Let a = |S ∩ L| and b = |S ∩ R|. The clique on L contributes a(N − a) crossing edges and the clique on R contributes b(N − b).
- If 1 ≤ a ≤ N − 1 and 1 ≤ b ≤ N − 1, the value is at least 2(N − 1) = 2h + 2s − 2 ≥ Δ.
- Let S split L but not R. Exchanging S and T if needed, S ∩ R is empty, so S ⊆ L and a ≥ 2. For 2 ≤ a ≤ N − 2 the value is at least a(N − a) ≥ 2N − 4 ≥ Δ, since s ≥ 3. For a = N − 1, the side S misses one vertex w of L, and the value is at least (N − 1) + h(h − 1) ≥ Δ, counting the edges from L₂ ∖ {w} to R₂.
- If S splits neither L nor R, then S = L or S = R, and the value is at least |L₂ × R₂| = h² ≥ Δ.
- If S splits R but not L, the same argument applies with L and R exchanged. ∎

For u ≠ v, the cuts ({u}, V ∖ {u}) and ({v}, V ∖ {v}) have values d_u and d_v, and every other u-v cut has value at least Δ ≥ max(d_u, d_v) by Lemma 4. Hence λ(u, v) = min(d_u, d_v) for every pair. Fix r ∈ L₂. For x ∈ L₁, d_x < Δ = d_r, so λ(r, x) = d_x, and

|B| = Σ_{x ∈ L₁} (λ(r, x) − (N − 1)).

*Proof of Theorem 2.* The single-source values from r determine |B|, where B ranges over all subsets of the s² pairs of L₁ × R₁ and every other entry of the matrix is fixed. Deciding whether a string of M = s² bits has Hamming weight t or t + 1, with t = ⌊M/2⌋, needs Ω(√((t + 1)(M − t))) = Ω(M) quantum queries, by the adversary bound of [5] applied to the pairs of strings that differ in one bit. With h = ⌈n/4⌉ + 1 and s = n/2 − h ≥ n/4 − 2, this is Ω(n²) for even n ≥ 24; for odd n an isolated vertex is added, which changes no value λ(u, v) between the other vertices. The graph has at least h² ≥ n²/16 edges. ∎

The proof uses only that degrees are expensive in the adjacency-matrix model. In the adjacency-array model the degree of a vertex is one query, every value of this family is known after n queries, and Theorem 1 applies instead.

## Numerical checks

- `sim/core_lemma.py` (output in `sim/out_core_lemma.txt`) builds dense clusters joined by few edges, with pairs of adjacent middle vertices placed in the cluster where they have fewer neighbours. It certifies a conductance bound for each planted cluster with respect to full degrees (the easy direction of Cheeger's inequality), and shaves with the instance-specific threshold d_C(x) ≤ d_x/2 + b, where b bounds |X| as in the proof of Lemma 3. It uses H = G and exact counts, so it checks the logic of Lemma 3 and of the star model, not the constants of steps 2 and 3, which only take effect at large δ. It asserts that every minimum cut found meets each core as Lemma 3 says and that the star model has the same value λ(u, v) as G for every pair. Without shaving, the star model gives wrong values on every instance.
- `sim/core_lemma_all_cuts.py` (output in `sim/out_core_lemma_all_cuts.txt`) enumerates every cut of random clustered graphs on 10 to 14 vertices, with a cut sparsifier H obtained from G by edge weights in [0.9, 1.1], computes the exact conductance of each planted cluster in H with full volumes, and shaves with the margin d_x/2 + β of the proof. Over 182 instances it checks Lemma 3 on all 7090 minimum u-v cuts of nontrivial pairs and the star model on all pairs, with no failure. With margin 0 it finds violations.
- `sim/matrix_lb.py` (output in `sim/out_matrix_lb.txt`) checks Lemma 4 by brute force over all cuts for n = 16, computes Gomory-Hu trees for random B at n = 20, 26 and 40, asserts that every value equals min(d_u, d_v) and that |B| is recovered from the single-source values, and checks that the claim fails once the block L₂ × R₂ is removed.
- `sim/trivial_fraction.py` (output in `sim/out_trivial_fraction.txt`) shows that on random dense graphs every edge of the Gomory-Hu tree has the value min(d_u, d_v) of its endpoints.

## Lean

The library `GHMatrix` in `lean/` (Lean 4, Mathlib at the revision pinned in `lean/lakefile.toml`) proves Lemma 4 with only the standard axioms (`lean/axioms.txt`):

- `GHMatrix.lemma4`: for any graph on a finite vertex set split into `L` and `R` with `h + s` vertices each, both cliques, with `L₂ ⊆ L` and `R₂ ⊆ R` of size `h` completely joined and any further edges, and `3 ≤ s < h`, every cut with at least two vertices on each side has at least `2h + s − 1` crossing edges;
- `GHMatrix.arith`: the arithmetic core, over the counts `|S ∩ L|`, `|S ∩ R|`, `|S ∩ L₂|`, `|S ∩ R₂|`;
- content of the statement, in `lean/GHMatrix/NonVacuity.lean`: the family with `h = 4`, `s = 3` and `B = ∅` on 14 vertices satisfies all hypotheses, a cut with two vertices of `L₁` on one side has exactly `10 = 2h + s − 1` crossing edges, so the bound is attained, and a cut with one vertex on one side has 6.

## Open questions

- Whether Gomory-Hu trees of all dense simple graphs, with arbitrary degrees, can be computed with Õ(n^{3/2}) adjacency-array queries, matching the lower bound for global minimum cut.

## Not formalized

Theorems 1 and 2, Lemma 3 and the star model are written proofs, not checked in Lean. The sparsifier of [4], amplitude estimation and Grover search enter with their published query bounds.

## References

[1] S. Apers, T. Lee. Quantum complexity of minimum cut. CCC 2021. arXiv:2011.09823.

[2] T. Lu, R. Ren, S. Liu. Tight quantum query bounds for minimum cut and multicut on dense graphs. arXiv:2611.17845.

[3] Y. Kenneth-Mordoch, R. Krauthgamer. All-pairs minimum cut using Õ(n^{7/4}) cut queries. arXiv:2510.16741.

[4] S. Apers, R. de Wolf. Quantum speedup for graph sparsification, cut approximation and Laplacian solving. FOCS 2020. arXiv:1911.07306.

[5] A. Ambainis. Quantum lower bounds by quantum arguments. J. Comput. Syst. Sci. 64(4), 2002. arXiv:quant-ph/0002066.

## Use of AI

The proofs, the scripts and this text were produced with the help of Claude Opus 5.5.
