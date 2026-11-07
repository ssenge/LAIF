# Quantum query lower bounds for complete bipartite subgraphs

Written 7 Nov 2026.

## Result

Model: an N-vertex graph given by its adjacency matrix, one query per pair of vertices. Task: for a fixed graph H, decide whether the graph contains a copy of H as a subgraph, or find one.

**Theorem 1.** Let 3 ≤ a ≤ b and θ = (3a + 3b − 8)/(3(a − 1)b + 1). Every bounded-error quantum algorithm that detects, or finds, a copy of K_{a,b} in N-vertex graphs makes Ω(N^{7/6 − θ/6}) queries. For K_{2,3} the bound is Ω(N^{16/15}), and for K_{2,b} with b ≥ 4 it is Ω(N^{15/14}).

For K_{r,r} the exponent is 7/6 − (3r − 4)/(3(3r² − 3r + 1)).

| H | Best previous bound known to us | This folder |
|---|---|---|
| K_{2,3} | Ω(N^{25/24}) [T] | Ω(N^{16/15}) |
| K_{2,b}, b ≥ 4 | Ω(N^{1 + 1/(6(b+1))}) [T] | Ω(N^{15/14}) |
| K_{3,3} | Ω(N^{31/30}) [T] | Ω(N^{41/38}), 41/38 ≈ 1.079 |
| K_{4,4} | Ω(N^{43/42}) [T] | Ω(N^{81/74}), 81/74 ≈ 1.095 |
| K_{10,10} | Ω(N^{115/114}) [T] | Ω(N^{615/542}), 615/542 ≈ 1.135 |
| K_{18,18} | N^{β_18 − o(1)}, β_18 ≈ 1.1468 [2] | Ω(N^{2111/1838}), 2111/1838 ≈ 1.1485 |
| K_{a,b}, 3 ≤ a ≤ b | Ω(N^{1 + 1/(6(a+b−1))}) [T] | Ω(N^{7/6 − θ/6}) |

[T] marks the bound of [two-connected-subgraph-quantum-lower-bounds](../two-connected-subgraph-quantum-lower-bounds/) for 2-connected patterns. For K_{10,10}, [T] gives 115/114, above the 181/180 of [2]; for 11 ≤ r ≤ 18 the previous best is from [2]. To our knowledge these are the best lower bounds for K_{a,b} with a < b and for K_{r,r} with 3 ≤ r ≤ 18. For r ≥ 19 the bounds of [2] are larger; they tend to 2, while the exponent here tends to 7/6. For K_{3,b} with b large the exponent tends to 13/12, and for K_{a,b} with a fixed and b large it tends to 7/6 − 1/(6(a − 1)).

The same method applies to every connected H (Theorem 2). For the octahedron K_{2,2,2}, which has chromatic number 3, it gives Ω(N^{11/10}); the best previous bound known to us is Ω(N^{13/12}) [1].

## The argument

The proof uses Proposition 3 of [two-connected-subgraph-quantum-lower-bounds](../two-connected-subgraph-quantum-lower-bounds/), the triangle lower bound of [1] run on the blow-up of H. With p = c₀ n^{−θ} and R = (np)^{2/3}, that proposition gives t = Ω(n^{7/6} p^{1/6}) = Ω(n^{7/6 − θ/6}) under three hypotheses: (P) planting creates no other copy with probability at least 1/2; (S) inside the star of each vertex w, each edge interacts with at most d_s others, with p d_s ≤ R; (I) each edge interacts with at most d_m edges, with p d_m ≤ 1/5. For 2-connected H, degree bounds give the hypotheses up to θ = (v − 2)/(v − 1). Here the degree bounds are replaced by extension counts, which allow smaller θ, that is, denser inputs.

**Extension counts.** A rooted pattern is a vertex set S of H with a root set R ⊆ S and an edge set F of H[S] with no edge inside R. Its extensions at a fixed image of R are the embeddings of S that extend the root map and have all edges of F present. For θ ∈ (0, 1) put

    ε(S, R, F) = max over R ⊆ U ⊆ S of ( |S \ U| − θ |F \ F[U]| ).

The term for U is the expected number of extensions that contain a fixed image of U, up to constants, on the scale of powers of n. Every vertex of S \ R must meet an edge of F; otherwise ε ≥ 1 and the pattern is useless. The extension count is then a polynomial of degree |F| in the edge variables with bounded coefficients, and the concentration inequality of Kim and Vu [4], with λ = C log n, bounds it by n^ε (log n)^{|F|} outside probability n^{−20}. If the pattern is *safe*, meaning |U \ R| − θ |F[U]| > 0 for every U ≠ R, then the count is at most a constant times its mean outside probability exp(−n^δ), and no logarithmic loss occurs.

**Theorem 2.** Let H be connected with v ≥ 3 vertices, let θ_P = max over 2 ≤ j ≤ v − 1 of (v − j)/(e(H) − e_max(j)), where e_max(j) is the largest number of edges of H on j vertices, and let θ_P ≤ θ < 1. Suppose that for every vertex x of H and distinct neighbours y, z of x some S ⊆ V(H) − x containing y and z has ε(S, {y}, E(H[S])) < 2/3 + θ/3, or equality and a safe pattern. If θ = θ_P, suppose also that the pattern (V(H), i, E(H) − {i, j}) is safe for all distinct edges i, j. Then detecting or finding H takes Ω(N^{7/6 − θ/6}) queries.

- *(P).* A new copy sharing j vertices with the planted copy needs e(H) − e_max(j) new edges, so the expected number is O(c₀ n^{(v−j) − θ(e(H) − e_max(j))}) = O(c₀) for θ ≥ θ_P. Increasing events are no more likely under the conditioned distribution [1, Lemma 5.2].
- *(S).* If wa and wb interact through a copy with w in the role x, a in the role y and b in the role z, then the copy restricted to S is an extension of the pattern (S, {y}, E(H[S])) at a. Its edges avoid w, so the count depends only on edges outside the star of w, and it bounds the number of such b. So p d_s/R = n^{ε − 2/3 − θ/3} up to logarithms.
- *(I).* For edges i and j of H, the copy restricted to V(H) is an extension of (V(H), i, E(H) − {i, j}). If W = V(H) \ U, the edges of this pattern that touch W number at least e_W − 1, where e_W counts the edges of H touching W, and |W|/e_W ≤ θ_P because V(H) \ W contains i. Hence ε < θ for θ > θ_P, so p d_m → 0. At θ = θ_P, ε ≤ θ, and safety removes the logarithmic factor.

Detection follows by the constant-factor reduction from search to detection for connected subgraphs [3, Lemma 23] (as cited in [two-connected-subgraph-quantum-lower-bounds](../two-connected-subgraph-quantum-lower-bounds/)).

**Proof of Theorem 1.** For K_{a,b}, θ_P = (a + b − 2)/(ab − 1): a copy sharing x vertices of one side and y of the other gives the ratio (a + b − x − y)/(ab − xy), and the difference to (a + b − 2)/(ab − 1), after clearing denominators, is bilinear in (a − x, b − y) with nonnegative values at the corners. Shared sets inside one side contain no edge of the planted copy and create no copy.
- *3 ≤ a ≤ b.* Take S = V(H) − x. If x lies on the side of size a, a set W = S \ U with α vertices on the side of x and β on the other side touches αb + β(a − 1) − αβ edges. The term |W| − θ e_W is bilinear in (α, β), and its corner values are 0, (a − 1)(1 − θb), (b − 1)(1 − θ(a − 1)) and a + b − 2 − θ(a − 1)b. Since θ(a − 1) ≥ 1 for a ≥ 3, the middle two are at most 0, and the last equals 2/3 + θ/3 by the choice of θ. The pattern is safe: the corner values of |U \ R| − θ |F[U]| are (a − 1)(1 − θ), b − 1 and the last value above. If x lies on the side of size b, the corners are (a − 1)(1 − θ(b − 1)) ≤ 0, (b − 1)(1 − θa) ≤ 0 and a + b − 2 − θa(b − 1), which is no larger. Finally θ > θ_P, since (3a + 3b − 8)(ab − 1) − (a + b − 2)(3ab − 3b + 1) = 3b² + ab − 4a − 10b + 10 > 0, and θ < 1, since 3(a − 1)b + 1 − (3a + 3b − 8) = 3((a − 2)(b − 1) + 1) > 0.
- *a = 2.* Take S = {y, l, z}, where l ≠ x lies on the side of x, so that y, l, z is a path. Then ε = 2 − 2θ, and 2 − 2θ ≤ 2/3 + θ/3 exactly for θ ≥ 4/7. The path is safe. With θ_P = b/(2b − 1), this gives θ = 3/5 for b = 3 and θ = 4/7 for b ≥ 4. For b = 3 and b = 4 the interaction condition is tight, and its pattern V(H) is safe at θ_P.

**Octahedron.** Here θ_P = 4/11. For adjacent neighbours y, z of x the pattern S = {y, z} has ε = 1 − θ. For the two non-adjacent pairs, S = V(H) − x, a wheel with five vertices, has ε = 4 − 8θ for θ ≤ 1/2, which equals 2/3 + θ/3 at θ = 2/5. The pattern is safe, so θ = 2/5 and the bound is N^{7/6 − 1/15} = N^{11/10}.

**Cut vertices.** Theorem 2 also applies to some graphs with cut vertices, when the blocks are dense. For two copies of K_{3,3} sharing a vertex, θ_P = 5/9, and θ = 13/19 is star-admissible: for y and z in different blocks, the pattern formed by y and the far block minus the cut vertex has ε = 5 − 6θ = 2/3 + θ/3, and it is safe. This gives Ω(N^{20/19}). The reduction behind Corollary 2 of [T] turns every lower bound for the block B into the same bound for H, so Theorem 1 gives more here: Ω(N^{41/38}). For sparse blocks such as four-cycles, the far pattern has ε ≥ 1 and Theorem 2 does not apply.

**Limits.** For K_{r,r} the star condition, not planting, determines θ when r ≥ 3. The bound n^{7/6} p^{1/6} of Proposition 3 does not depend on H, so the exponent stays below 7/6 for every H. For large r the random constructions of [2] give more.

## Check

`check.py` verifies:
- the conditions of Theorem 2 by brute force over all induced patterns, with the safety of every tight condition, reproducing 13/12, 19/18, 11/10 and 10/9 for the triangle, the four-cycle, K4 and K5;
- the closed form of Theorem 1 against the brute force for a + b ≤ 8, and against a computation by vertex types for all 2 ≤ a ≤ b ≤ 30;
- θ = 2/5 for the octahedron, and θ = 13/19 for two copies of K_{3,3} sharing a vertex;
- the comparison with β_r of [2, (68)] with exact fractions: the exponent here is larger exactly for r ≤ 18, among 10 ≤ r ≤ 20; for r ≥ 20, β_r ≥ β_20 > 7/6. For r ≤ 9, β_r < 1.

Run it with `python3 check.py` (about 20 seconds).

## References

[1] A. Cornelissen, A. S. Gilani, X. Zhou. A quantum lower bound for triangle finding. arXiv:2611.06751, 2026.

[2] A. S. Gilani, X. Zhou. Superlinear quantum query lower bounds for subgraph detection. arXiv:2609.40263, 2026.

[3] A. Cornelissen, A. S. Gilani, S. Patro. Quantum algorithms for path and cycle containment problems. APPROX/RANDOM 2026, LIPIcs 392, 72:1-72:23. arXiv:2605.09017.

[4] J. H. Kim, V. H. Vu. Concentration of multivariate polynomials and its applications. Combinatorica 20(3):417-434, 2000.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.
