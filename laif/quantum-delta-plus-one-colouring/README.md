# Quantum (Δ + 1)-colouring with Õ(n^{5/4}) queries

Written 22 Nov 2026.

**Setting.** As in [1]: an n-vertex graph G with maximum degree Δ is given by quantum degree queries (the degree of v), neighbourhood queries (the j-th neighbour of v, in an arbitrary fixed order) and adjacency queries (whether u and v are adjacent). The task is to output a proper colouring with Δ + 1 colours with probability at least 2/3.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | (Δ + 1)-colouring, quantum queries | Õ(n^{4/3}) [1, Cor. 4]; lower bound Ω(n) with adjacency queries only [4] | O(min{n√Δ log n, n^{3/2} Δ^{−1/2} log² n}) = O(n^{5/4} log^{3/2} n) | Claim; checked by script |
| Cor 2 | (1 + ε)Δ-colouring, quantum queries | Õ(ε^{−1} n^{5/4}) [1, Cor. 6] | Õ(n^{5/4}), independent of ε | Claim |

Theorem 1 gives the bound Õ(n^{5/4}) that [1, Section 4] names as the target of a quantum neighbourhood algorithm with Õ(n√Δ) queries. The classical query complexity is Θ̃(n^{3/2}) [2, 1]. The lower bound Ω(n) of [4] holds when only adjacency queries are available; a matching lower bound for the combined model is open.

## The algorithm

It is the palette sparsification algorithm of [2] with the classical scans replaced by quantum search [3].

1. Read all degrees and set Δ = max_v d(v), with n degree queries.
2. Every vertex v samples a list L(v) of ℓ = min{Δ + 1, ⌈c ln n⌉} colours from {1, …, Δ + 1}, independently and uniformly, where c is the sufficiently large constant of the palette sparsification theorem [2, Thm. 1]; if Δ + 1 ≤ ⌈c ln n⌉, then L(v) = {1, …, Δ + 1}. By that theorem, which holds for every graph, with probability 1 − 1/poly(n) the graph G has a proper colouring χ with χ(v) ∈ L(v) for every v.
3. Call an edge uv a conflict edge if L(u) ∩ L(v) ≠ ∅, and let t_v be the number of conflict edges at v. Find all conflict edges:
   - if Δ ≤ √n log n: for every v, search the positions j ≤ d(v) of the neighbourhood list of v for neighbours u with L(u) ∩ L(v) ≠ ∅;
   - if Δ > √n log n: for every v, let C_v = {u ≠ v : L(u) ∩ L(v) ≠ ∅}, which depends only on the lists, and search C_v for neighbours of v with adjacency queries.
4. Colour the conflict graph H from the lists, which needs no queries.

The lists are fixed classical data, so the marking "L(u) ∩ L(v) ≠ ∅" is computed coherently from the answer u of a neighbourhood query.

## Theorem 1, the proof

**Correctness.** Every edge uv of G with χ(u) = χ(v) has a common colour in L(u) ∩ L(v), so it is a conflict edge. Hence a colouring of H from the lists is proper on G, and one exists with high probability by step 2.

**Sizes.** Each pair u ≠ v has a common colour with probability at most ℓ²/(Δ + 1). So E[t_v] ≤ ℓ² d(v)/(Δ + 1) ≤ ℓ² and E[|C_v|] ≤ ℓ² n/(Δ + 1). (For Δ < ℓ² the bound on t_v holds trivially, since t_v ≤ d(v) ≤ Δ.) Given L(v), the events for different u are independent, so by the multiplicative tail bound for sums of independent indicators, with probability 1 − n^{−3} every v has t_v ≤ 2ℓ² + O(log n) = O(log² n) and |C_v| ≤ 2ℓ² n/(Δ + 1) + O(log n).

**Queries.** All t marked items among N can be found with O(√(N(t + 1))) queries in expectation [5], and every item found is checked with one query, so no wrong item is ever reported. Certifying that none is left takes O(log n) further runs of quantum search with O(√N) queries each [3], which miss a remaining item with probability at most n^{−3}. So the expected cost per vertex is O(√(N(t + 1)) + √N log n). In the neighbourhood case N = d(v) ≤ Δ and t = t_v, so the cost per vertex is O(√Δ log n), and O(n√Δ log n) in total. In the adjacency case N = |C_v| = O(n log² n/Δ), so the cost per vertex is O(√(n/Δ) log² n), and O(n^{3/2} Δ^{−1/2} log² n) in total. Step 1 costs n queries. The case is chosen by the smaller of the two expressions, that is by Δ ≤ √n log n, which gives the minimum of the two totals and at most O(n^{5/4} log^{3/2} n). A query budget of a constant times the expected total, by the first-moment inequality, gives a worst-case count, and with the union bound over the vertices and the failure probability of step 2 the total error stays below 1/3. ∎

**Corollary 2.** For (1 + ε)Δ ≥ Δ + 1 colours, a (Δ + 1)-colouring is a (1 + ε)Δ-colouring, so Theorem 1 applies. For εΔ < 1, (1 + ε)Δ < Δ + 1 colours do not always suffice, and the statement is for εΔ ≥ 1.

Computing the colouring of H in step 4 is free in the query model.

## Scripts

`sim/check_palette.py` builds graphs of maximum degree Δ, unions of random perfect matchings and disjoint copies of the complete graph on Δ + 1 vertices (where a colouring from the lists needs every colour in every clique), with n up to 4000 and Δ up to 577. It samples lists of size ⌈2 ln n⌉ and checks the sizes of t_v and C_v, that a colouring from the lists exists on the conflict graph (found by local search) and is proper on G, and that the search costs Σ_v (√(N_v(t_v + 1)) + √N_v ln n), with N_v = d(v) or |C_v|, stay below 2n√Δ ℓ and 2n√(n/Δ) ℓ². The constant 2 is a choice for the script; the theorem uses the constant of [2].

```
python sim/check_palette.py
matchings: n=3000 Delta=200 l=17: max t_v=171 (l^2=289), max |C_v|=2466 (n l^2/(Delta+1)=4313), proper list colouring found; neighbour cost 852647 (2 n sqrt(Delta) l = 1442498), adjacency cost 2986097 (2 n sqrt(n/Delta) l^2 = 6715753)
matchings: n=4000 Delta=577 l=17: max t_v=271 (l^2=289), max |C_v|=1745 (n l^2/(Delta+1)=2000), proper list colouring found; neighbour cost 2198959 (2 n sqrt(Delta) l = 3266832), adjacency cost 3737197 (2 n sqrt(n/Delta) l^2 = 6087373)
cliques: n=4000 Delta=199 l=17: max t_v=180 (l^2=289), max |C_v|=3258 (n l^2/(Delta+1)=5780), proper list colouring found; neighbour cost 1178943 (2 n sqrt(Delta) l = 1918516), adjacency cost 4707152 (2 n sqrt(n/Delta) l^2 = 10365525)
cliques: n=4000 Delta=63 l=17: max t_v=63 (l^2=289), max |C_v|=3999 (n l^2/(Delta+1)=18062), proper list colouring found; neighbour cost 512919 (2 n sqrt(Delta) l = 1079467), adjacency cost 4101219 (2 n sqrt(n/Delta) l^2 = 18422457)
```

**Not formalized:** all of the folder. The palette sparsification theorem and quantum search are taken from the literature.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. A. Ferber, L. Hardiman, X. Chen. Improved sublinear algorithms for classical and quantum graph coloring. arXiv:2502.06024, 2025.
2. S. Assadi, Y. Chen, S. Khanna. Sublinear algorithms for (Δ + 1) vertex coloring. SODA 2019.
3. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschritte der Physik 46, 1998. arXiv:quant-ph/9605034.
4. J. Morris, F. Song. Simple vertex coloring algorithms. arXiv:2102.07089, 2021.
5. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM Journal on Computing 35(6), 2006. arXiv:quant-ph/0401091.
