# Quantum query lower bounds for K4, K5 and K6 finding

Written 6 Nov 2026. Extended to K5, K6 and K7 on 7 Nov 2026.

## Result

Model: an N-vertex graph given by its adjacency matrix, one query per pair of vertices. Task: decide whether the graph contains a k-clique K_k, or find one.

**Theorem 1.** For 4 ≤ k ≤ 7, every bounded-error quantum algorithm that detects, or finds, a K_k in N-vertex graphs makes Ω(N^{7/6 − 1/(3(k+1))}) queries.

| k | Previous exponent | This folder |
|---|---|---|
| 4 | 19/18 [2]; 13/12, from the triangle bound [1] | 11/10 |
| 5 | 13/12 [2] | 10/9 |
| 6 | 11/10 [2] | 47/42 |
| 7 | 9/8 [2] | 9/8 (no change) |

**Theorem 2.** Let 4 ≤ k ≤ 7 and let G = K_{n,...,n} be the complete k-partite graph with parts of size n, known to the algorithm. Let the input be a subgraph of G in which every edge is present with probability p, conditioned on one planted, uniformly random K_k being the only K_k. There are constants C, c₀ > 0, depending on k, such that for p = c₀ n^{−2/(k+1)} every t-query algorithm that outputs the planted K_k with average probability σ satisfies

    √σ ≤ C (t + s) · n^{−7/6} p^{−1/6},      s = k(k−1)/2.

So t = Ω(n^{7/6 − 1/(3(k+1))}). Detection follows by the constant-factor reduction from search to detection for connected subgraphs [2, Section 2.2], [3, Lemma 23].

**Corollary 3.** By [2, Theorem 1.3(i)], detecting a fixed connected graph of chromatic number 5 takes Ω(N^{10/9}) quantum queries, and of chromatic number at least 6 takes Ω(N^{47/42}). For chromatic number 4 the bound is Ω(N^{11/10}).

For k ≥ 8 the method below gives only N^{9/8}, below the bounds of [2].

## The argument

The proof is the triangle lower bound of [1], with triangles replaced by K_k. That proof compares the computation on positive inputs with the computation on negative inputs: Bernoulli(p) graphs conditioned to contain no copy of the pattern. The comparison uses a map built from a few negative inputs and an averaging operator over the stars of the candidate's vertices. Its error per query gives the bound.

For triangles, the density is limited to about n^{−1/2}, because planting a triangle must rarely create a second one. For K_k the planting condition is weaker and allows density n^{−2/(k+1)}, and the bound improves with the density. Two estimates of [1] use a smallness condition that fails at this density. Steps 3 and 4 below replace them.

Notation, as in [1, Section 5]:
- G = K_{n,...,n} with k parts, s = C(k,2), m = s n² edges, every degree Δ = (k−1)n, and M = n^k candidate cliques.
- µ⁻ is the K_k-free distribution.
- D_i is the conditional difference at edge i.
- L_w is the sum of D_i over the edges i at w.
- H_T is the sum of L_w over the k vertices w of the candidate T, and F_T = (I + H_T/R)^{−1}.
- θ = 2/(k+1), p = c₀ n^{−θ} and R = (np)^{2/3}.

**1. Planting.** Fix a negative input and set the s edges of T to one. A new K_k has to share an edge with T, so it shares j vertices with T for some 2 ≤ j ≤ k−1. There are at most C(k,j) n^{k−j} such cliques, each needing s − C(j,2) present edges. The expected number is at most

    C(k,j) c₀^{s−C(j,2)} n^{(k−j)(2−j)/(k+1)},

which is at most C(k,j) c₀^{s−C(j,2)} since j ≥ 2. Increasing events are no more likely under µ⁻ than under independent bits [1, Lemma 5.2]. So T is the only K_k with probability at least 0.97 for small c₀. On that event, all 2^s − 1 proper subsets of T give negative inputs, and the probability ratio r_T of [1, (5.6)] is bounded by a constant.

**2. Comparison map.** The map uses the inputs y^∅ and y^{i}, for i ∈ T, which agree with the positive input y outside T:

    (T_T f)^y = Σ_{i∈T} f^{y^{i}} − (s − 1) f^{y^∅}.

The coefficients sum to one. For a query to e ∈ T, the error is −2 Σ_{i∈T∖{e}} (f^{y^{i}} − f^{y^∅}). So [1, Lemma 5.3] holds with s edges in place of three.

**3. Sums over a star.** Fix the edges outside the star of w. The constraint inside the star is that, for each present outside K_{k−1} on vertices a₁, ..., a_{k−1}, the star edges wa₁, ..., wa_{k−1} are not all present. Two star edges wa and wb interact only if ab is present. So the number of edges that interact with wa is at most the outside degree of a, which is O(np) outside an event of probability exp(−Ω(np)). This count is large, so [1, Lemma 4.5] does not apply as stated: its hypothesis pd ≤ 1/10 fails. The following variant of [1, Lemma 4.4] does not need that hypothesis.

*Lemma.* Let Π_1, ..., Π_ℓ be orthogonal projections, L = Σ Π_i and F = (I + L/R)^{−1}. Suppose Σ_i ‖[Π_i, L]g‖² ≤ κ²⟨g, Lg⟩ for all g. Then Σ_i ⟨Π_i f, FΠ_i f⟩ ≤ (2 + κ²/(4R²)) R ‖f‖².

*Proof.* Write Y for the left side. As in [1, (4.23)], Y = ⟨f, LFf⟩ + R^{−1} Re Σ_i ⟨FΠ_i f, [Π_i, L]Ff⟩.
- The first term is at most R‖f‖².
- F² ⪯ F gives Σ_i ‖FΠ_i f‖² ≤ Y.
- Spectral calculus gives ⟨Ff, LFf⟩ ≤ (R/4)‖f‖².
- By Cauchy-Schwarz, Y ≤ R‖f‖² + (κ/2) R^{−1/2} √Y ‖f‖. With s² = Y/(R‖f‖²) this reads s² ≤ 1 + (κ/2R)s, so s² ≤ 2 + κ²/(4R²). ∎

The interaction estimate in the proof of [1, Lemma 4.5] gives κ² = 2(1 + p)(pd)², with d = O(np). So κ = O(np²), while R = (np)^{2/3}. The ratio κ/R is of order n^{1/3}p^{4/3} = c₀^{4/3} n^{(k−7)/(3(k+1))}, bounded for k ≤ 7. Therefore Σ_{i at w} ⟨D_i f, F_w D_i f⟩ ≤ cR‖f‖² plus a term for rare inputs, as in [1, (5.18)].

**4. Moving a difference through the averaging.** [1, Lemma 4.6] needs pd ≤ 2/5, where d bounds the number of edges j that interact with the queried edge i = uv, on an event of the full input that fails with small probability. An interacting j lies in a K_k with i whose other s − 2 edges are present. Up to exchanging u and v, there are two patterns:
- X₁: j = uw, and a set Y of k − 3 further vertices, with all pairs in {u, v, w} ∪ Y present except uv and uw;
- X₂: j = wz disjoint from i, and a set Y of k − 4 further vertices, with all pairs in {u, v, w, z} ∪ Y present except uv and wz.

The number of interacting j is at most X₁(u, v) + X₁(v, u) + X₂, and the weighted count of [1, Lemma 4.6] is at most twice that, since every weight is at most 2. Each count is a polynomial of degree s − 2 in the edge variables, with coefficients 0 or 1, and expectation at most C n^{k−2} p^{s−2} = C c₀^{s−1}/p under independent bits. Fixing a nonempty set of the pattern's edges leaves an extension of a sub-pattern. For every nonempty set S of non-root vertices, n^{|S|} p^{e(S)} ≥ c n^{1/(k+1)}, where e(S) counts the pattern edges with an endpoint in S and the other in S or the roots (`check.py` verifies this for 4 ≤ k ≤ 7). So every expected partial derivative is at most n^{−1/(k+1)} times the expectation, and polynomial concentration [4] gives X ≤ 2 E X outside probability exp(−n^{δ}), for any δ < 1/(2(k+1)(s−2)) and n large enough. These are increasing events, so the same holds under µ⁻ [1, Lemma 5.2]. A union bound over all edges i gives d = O(c₀^{s−1}/p), and pd ≤ 2/5 for small c₀. The conclusion is [1, (5.19)]: ‖D_i F_T f‖² ≤ 4‖F_T D_i f‖² + (p/R)‖f‖² plus a term for rare inputs.

**5. Counting candidates.** Fix the queried edge e = uv. Let A_e be the candidates containing e (n^{k−2} of them) and B_{u,v} those containing u but not v (fewer than n^{k−1}).
- *A_e.* An edge at u or v lies in n^{k−3} candidates of A_e and is charged to the star at u or v. Any other edge lies in n^{k−4} candidates and is charged to the star of one of its endpoints; there are O(n) such stars. Step 4 adds p/R for each of the O(n^{k−2}) pairs. Total: c(n^{k−3}R + n^{k−2}p/R).
- *B_{u,v}.* An edge at u lies in at most n^{k−2} candidates. Any other edge lies in at most n^{k−3} candidates, and is charged to the star of one of its endpoints, O(n) stars. Total: c(n^{k−2}R + n^{k−1}p/R).

Following [1, Lemma 5.6], the squared query error is at most α‖f‖² + β‖f‖²_∞, where

    α ≤ (c/n^k) n^{k−3} (R/p + n/R + n/R² + n²p/R²).

With R = (np)^{2/3}, the first and last terms balance, and n/R is smaller because np ≥ 1. So α ≤ c n^{−7/3} p^{−1/3}. Every rare-input term carries a factor exp(−n^{δ}), so mβ is negligible. The comparison theorem [1, Theorem 4.1] gives √σ ≤ (t + s)(α + mβ)^{1/2}, which is Theorem 2. The s queries verify the output.

**Choice of constants.** First fix the constants in the degree and extension events. Then choose c₀ small enough for Steps 1 and 4. Finally take n large enough for the concentration bounds.

## Check

`check.py` verifies by brute force on K_{n,...,n}, for k = 4, 5, 6 and small n:
- the multiplicities of Step 5;
- on random K_k-free inputs, that the edges interacting with a queried edge are exactly those counted by the patterns of Step 4, and the outside-degree bound of Step 3;
- the coefficients and the query error of the map in Step 2.

It also checks, with exact fractions for 4 ≤ k ≤ 7, the planting exponents, the sub-pattern exponents of Step 4, the final exponent and the condition κ ≲ R. Run it with `python3 check.py`.

## References

[1] A. Cornelissen, A. S. Gilani, X. Zhou. A quantum lower bound for triangle finding. arXiv:2611.06751, 2026.

[2] A. S. Gilani, X. Zhou. Superlinear quantum query lower bounds for subgraph detection. arXiv:2609.40263, 2026.

[3] A. Cornelissen, A. S. Gilani, S. Patro. Quantum algorithms for path and cycle containment problems. APPROX/RANDOM 2026, LIPIcs 392, 72:1-72:23. doi:10.4230/LIPIcs.APPROX/RANDOM.2026.72.

[4] J. H. Kim, V. H. Vu. Concentration of multivariate polynomials and its applications. Combinatorica 20 (2000), 417-434.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.
