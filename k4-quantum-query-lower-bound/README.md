# A quantum query lower bound of N^{11/10} for K4 finding

Written 6 Nov 2026.

## Result

Model: an N-vertex graph given by its adjacency matrix, one query per pair of vertices. Task: decide whether the graph contains a K4, or find one.

**Theorem 1.** Every bounded-error quantum algorithm that detects, or finds, a K4 in N-vertex graphs makes Ω(N^{11/10}) queries.

**Theorem 2.** Let G = K_{n,n,n,n} be known to the algorithm. Let the input be a subgraph of G in which every edge is present with probability p, conditioned on one planted, uniformly random K4 being the only K4. There are constants C, c₀ > 0 such that, for C·(log n / n)^{1/2} ≤ p ≤ c₀ n^{−2/5}, every t-query algorithm that outputs the planted K4 with average probability σ satisfies

    √σ ≤ C (t + 6) · n^{−7/6} p^{−1/6}.

At p = c₀ n^{−2/5} this gives t = Ω(n^{11/10}). Detection follows by the constant-factor reduction from search to detection for connected subgraphs [2, Section 2.2], [3, Lemma 23].

| | Exponent of N |
|---|---|
| Previous bounds for K4 | 19/18 [2]; 13/12, from the triangle bound [1] |
| K4, this folder | 11/10 |
| K5, previous | 13/12 [2] |
| K5, this folder | 11/10, by adding a vertex adjacent to all others |
| Best known upper bound for K4 | below 3/2, by learning graphs [2] |

**Corollary 3.** By [2, Theorem 1.3], detecting any fixed connected graph of chromatic number 4 or 5 takes Ω(N^{11/10}) quantum queries. For chromatic number 6 and above, [2] already gives at least N^{11/10}.

## The argument

The proof is the triangle lower bound of [1], with triangles replaced by K4. That proof compares the computation on positive inputs with the computation on negative inputs: Bernoulli(p) graphs conditioned to contain no copy of the pattern. The comparison uses a map built from a few negative inputs and an averaging operator over the stars of the candidate's vertices. Its error per query gives the bound.

For triangles, the density is limited to about n^{−1/2}, because planting a triangle must rarely create a second one. For K4 the planting condition is weaker and allows density n^{−2/5}, and the bound improves with the density. Two of the estimates of [1] use a smallness condition that fails at this density. Steps 3 and 4 below replace those estimates.

Notation, as in [1, Section 5]:
- G = K_{n,n,n,n}, with m = 6n² edges, every degree Δ = 3n, and M = n⁴ candidate K4s.
- µ⁻ is the K4-free distribution.
- D_i is the conditional difference at edge i.
- L_w is the sum of D_i over the edges i at w.
- H_T is the sum of L_w over the four vertices w of the candidate T, and F_T = (I + H_T/R)^{−1}.
- R = (np)^{2/3}.

**1. Planting.** Fix a negative input and set the six edges of T to one. A new K4 has to share an edge with T: one sharing at most one vertex would already be present.
- Sharing three vertices: 4n·p³ choices.
- Sharing two vertices: 6n²·p⁵ choices.

Increasing events are no more likely under µ⁻ than under independent bits [1, Lemma 5.2]. So T is the only K4 with probability at least 1 − 4np³ − 6n²p⁵ ≥ 0.97 for small c₀. On that event, all 63 proper subsets of T give negative inputs, and the probability ratio r_T of [1, (5.6)] is bounded by a constant.

**2. Comparison map.** The map uses the inputs y^∅ and y^{i}, for i ∈ T, which agree with the positive input y outside T:

    (T_T f)^y = Σ_{i∈T} f^{y^{i}} − 5 f^{y^∅}.

The coefficients sum to one. For a query to e ∈ T, the error is −2 Σ_{i∈T∖{e}} (f^{y^{i}} − f^{y^∅}). So [1, Lemma 5.3] holds with six edges in place of three: ‖T_T f‖² ≤ c(‖f‖² + p^{−1} Σ_{i∈T} ‖D_i f‖²), and the query error is at most c p^{−1} Σ_{i∈T∖{e}} ‖D_i f‖².

**3. Sums over a star.** Fix the edges outside the star of w. The constraint inside the star is that, for each present outside triangle abc, the three star edges wa, wb, wc are not all present. Two star edges wa and wb interact only if ab is present. So the number of edges that interact with wa is at most the outside degree of a, which is O(np) outside an event of probability exp(−Ω(np)). This count is large, so [1, Lemma 4.5] does not apply as stated: its hypothesis pd ≤ 1/10 fails. The following variant of [1, Lemma 4.4] does not need that hypothesis.

*Lemma.* Let Π_1, ..., Π_ℓ be orthogonal projections, L = Σ Π_i and F = (I + L/R)^{−1}. Suppose Σ_i ‖[Π_i, L]g‖² ≤ κ²⟨g, Lg⟩ for all g. Then Σ_i ⟨Π_i f, FΠ_i f⟩ ≤ (2 + κ²/(4R²)) R ‖f‖².

*Proof.* Write Y for the left side. As in [1, (4.23)], Y = ⟨f, LFf⟩ + R^{−1} Re Σ_i ⟨FΠ_i f, [Π_i, L]Ff⟩.
- The first term is at most R‖f‖².
- F² ⪯ F gives Σ_i ‖FΠ_i f‖² ≤ Y.
- Spectral calculus gives ⟨Ff, LFf⟩ ≤ (R/4)‖f‖².
- By Cauchy-Schwarz, Y ≤ R‖f‖² + (κ/2) R^{−1/2} √Y ‖f‖. With s² = Y/(R‖f‖²) this reads s² ≤ 1 + (κ/2R)s, so s² ≤ 2 + κ²/(4R²). ∎

The interaction estimate in the proof of [1, Lemma 4.5] gives κ² = 2(1 + p)(pd)², with d = O(np). So κ = O(np²) = O(n^{1/5}), while R = Θ(n^{2/5}). Therefore Σ_{i at w} ⟨D_i f, F_w D_i f⟩ ≤ cR‖f‖² plus a term for rare inputs, as in [1, (5.18)].

**4. Moving a difference through the averaging.** [1, Lemma 4.6] needs pd ≤ 2/5, where d counts the edges j that interact with the queried edge i = uv on a good event of the full input. An interacting j lies in a K4 with i whose other four edges are present.
- If j = uw or j = vw, there is a common neighbour z of u and v with w adjacent to both v and z (for j = uw) or to both u and z (for j = vw).
- If j = wz, both w and z are common neighbours of u and v.

On the event that all codegrees are at most d₁ = O(np²), this gives d ≤ 6d₁² = O(n²p⁴), and so pd = O(n²p⁵) ≤ 2/5 for small c₀. Codegrees are sums of independent indicators of mean about np² ≥ C log n, so the bad event has probability exp(−Ω(np²)). The conclusion is [1, (5.19)]: ‖D_i F_T f‖² ≤ 4‖F_T D_i f‖² + (p/R)‖f‖² plus a term for rare inputs.

**5. Counting candidates.** Fix the queried edge e = uv. Let A_e be the candidates containing e (n² of them) and B_{u,v} those containing u but not v (fewer than n³).
- *A_e.* The edges uw, uz, vw and vz each lie in n candidates of A_e and are charged to the stars at u and v. An edge wz lies in one candidate and is charged to the star of one of its endpoints; there are O(n) such stars. Step 4 adds p/R for each of the 5n² pairs. Total: c(nR + n²p/R).
- *B_{u,v}.* An edge at u lies in at most n² candidates. Any other edge of a candidate lies in at most n candidates, and is charged to the star of one of its endpoints, O(n) stars. Total: c(n²R + n³p/R).

Following [1, Lemma 5.6], the squared query error is at most α‖f‖² + β‖f‖²_∞, where

    α ≤ (c/n⁴) (nR/p + n²/R + n²/R² + n³p/R²).

With R = (np)^{2/3}, the first and last terms balance, and n²/R is smaller because np ≥ 1. So α ≤ c n^{−7/3} p^{−1/3}. Every rare-input term carries a factor exp(−Ω(np²)), so mβ is negligible. The comparison theorem [1, Theorem 4.1] then gives √σ ≤ (t + 6)(α + mβ)^{1/2}, which is Theorem 2. The six queries verify the output.

**Choice of constants.** First fix the constant in d₁. Then choose c₀ small enough for Steps 1 and 4. Finally take n large enough that κ ≤ R. At p = c₀n^{−2/5}, the quantity np² is of order n^{1/5}, far above log n.

## Check

`check.py` verifies by brute force on K_{n,n,n,n}, for n ≤ 5:
- the multiplicities of Step 5;
- the bounds on interacting edges in Steps 3 and 4, on random K4-free inputs;
- the coefficients of the map in Step 2.

It also checks the exponent arithmetic with exact fractions. Run it with `python3 check.py`.

## References

[1] A. Cornelissen, A. S. Gilani, X. Zhou. A quantum lower bound for triangle finding. arXiv:2611.06751, 2026.

[2] A. S. Gilani, X. Zhou. Superlinear quantum query lower bounds for subgraph detection. arXiv:2609.40263, 2026.

[3] A. Cornelissen, A. S. Gilani, S. Patro. Quantum algorithms for path and cycle containment problems. APPROX/RANDOM 2026, LIPIcs 392, 72:1-72:23. doi:10.4230/LIPIcs.APPROX/RANDOM.2026.72.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.
