# Quantum (Δ + 1)-colouring with Õ(n^{5/4}) queries

Written 22 Nov 2026.

**Setting.** As in [1]: an n-vertex graph G with maximum degree Δ is given by quantum degree queries (the degree of v), neighbourhood queries (the j-th neighbour of v, in an arbitrary fixed order) and adjacency queries (whether u and v are adjacent). The task is to output a proper colouring with Δ + 1 colours with probability at least 2/3.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | (Δ + 1)-colouring, quantum queries | Õ(n^{4/3}) [1, Cor. 4]; lower bound Ω(n) with adjacency queries [5] | O(min{n√Δ log n, n^{3/2} Δ^{−1/2} log² n}) = Õ(n^{5/4}) | Claim; checked by script |
| Cor 2 | (1 + ε)Δ-colouring, quantum queries | Õ(ε^{−1} n^{5/4}) [1, Cor. 6] | Õ(n^{5/4}), independent of ε | Claim |

Theorem 1 gives the bound Õ(n^{5/4}) that [1, Section 4] names as the target of a quantum neighbourhood algorithm with Õ(n√Δ) queries. The classical query complexity is Θ̃(n^{3/2}) [2, 1]. The gap to the lower bound Ω(n) stays open.

## The algorithm

It is the palette sparsification algorithm of [2] with the classical scans replaced by quantum search [3].

1. Read all degrees and set Δ = max_v d(v), with n degree queries.
2. Every vertex v samples a list L(v) of ℓ = ⌈c ln n⌉ colours from {1, …, Δ + 1}, independently and uniformly. By the palette sparsification theorem [2, Thm. 1], with high probability G has a proper colouring χ with χ(v) ∈ L(v) for every v.
3. Call an edge uv a conflict edge if L(u) ∩ L(v) ≠ ∅, and let t_v be the number of conflict edges at v. Find all conflict edges:
   - if Δ ≤ √n: for every v, search the positions j ≤ d(v) of the neighbourhood list of v for neighbours u with L(u) ∩ L(v) ≠ ∅;
   - if Δ > √n: for every v, let C_v = {u ≠ v : L(u) ∩ L(v) ≠ ∅}, which depends only on the lists, and search C_v for neighbours of v with adjacency queries.
4. Colour the conflict graph H from the lists, which needs no queries.

The lists are fixed classical data, so the marking "L(u) ∩ L(v) ≠ ∅" is computed coherently from the answer u of a neighbourhood query.

## Theorem 1, the proof

**Correctness.** Every edge uv of G with χ(u) = χ(v) has a common colour in L(u) ∩ L(v), so it is a conflict edge. Hence a colouring of H from the lists is proper on G, and one exists with high probability by step 2.

**Sizes.** Each pair u ≠ v has a common colour with probability at most ℓ²/(Δ + 1). So E[t_v] ≤ ℓ² d(v)/(Δ + 1) ≤ ℓ² and E[|C_v|] ≤ ℓ² n/(Δ + 1). Given L(v), the events for different u are independent, so by the multiplicative tail bound for sums of independent indicators, with probability 1 − n^{−3} every v has t_v ≤ 2ℓ² + O(log n) = O(log² n) and |C_v| ≤ 2ℓ² n/(Δ + 1) + O(log n).

**Queries.** Finding all t marked items among N, and certifying that no further one exists, takes O(√(N(t + 1)) + √N log n) queries with error at most n^{−3}, by repeated quantum search with an unknown number of solutions [3] (each found item is removed, and a final search of O(√N log n) queries certifies that none is left). In the neighbourhood case N = d(v) ≤ Δ and t = t_v, so the cost per vertex is O(√Δ log n), and O(n√Δ log n) in total. In the adjacency case N = |C_v| = O(n log² n/Δ), so the cost per vertex is O(√(n/Δ) log² n), and O(n^{3/2} Δ^{−1/2} log² n) in total. Step 1 costs n queries. Choosing the case by Δ ≤ √n gives O(n^{5/4} log² n), and a union bound over the vertices keeps the total error below 1/3. ∎

**Corollary 2.** For (1 + ε)Δ ≥ Δ + 1 colours, a (Δ + 1)-colouring is a (1 + ε)Δ-colouring, so Theorem 1 applies. For εΔ < 1, (1 + ε)Δ < Δ + 1 colours do not always suffice, and the statement is for εΔ ≥ 1.

Computing the colouring of H in step 4 is free in the query model. With the asymmetric lists of [4] it can also be found in polynomial time, at polylogarithmic extra cost in the list sizes.

## Scripts

`sim/check_palette.py` builds random graphs of maximum degree Δ (unions of random perfect matchings, n up to 4000, Δ up to 389), samples lists of size ⌈c ln n⌉, and checks the sizes of t_v and C_v, that a colouring from the lists exists on the conflict graph (found by local search) and is proper on G, and that the search costs Σ_v √(d(v)(t_v + 1)) and Σ_v √(|C_v|(t_v + 1)) stay below n√Δ ℓ and n√(n/Δ) ℓ².

```
python sim/check_palette.py
n=2000 Delta=100 l=8: max t_v=67 (l^2=64), max |C_v|=1081 (n l^2/(Delta+1)=1267), proper list colouring found; neighbour cost 138586 (n sqrt(Delta) l = 160000), adjacency cost 442310 (n sqrt(n/Delta) l^2 = 572433)
n=3000 Delta=200 l=9: max t_v=89 (l^2=81), max |C_v|=1121 (n l^2/(Delta+1)=1209), proper list colouring found; neighbour cost 342285 (n sqrt(Delta) l = 381838), adjacency cost 789753 (n sqrt(n/Delta) l^2 = 941135)
n=3000 Delta=389 l=9: max t_v=102 (l^2=81), max |C_v|=630 (n l^2/(Delta+1)=623), proper list colouring found; neighbour cost 493795 (n sqrt(Delta) l = 532523), adjacency cost 610612 (n sqrt(n/Delta) l^2 = 674826)
n=4000 Delta=299 l=10: max t_v=112 (l^2=100), max |C_v|=1261 (n l^2/(Delta+1)=1333), proper list colouring found; neighbour cost 626248 (n sqrt(Delta) l = 691665), adjacency cost 1257202 (n sqrt(n/Delta) l^2 = 1463034)
```

**Not formalized:** all of the folder. The palette sparsification theorem and quantum search are taken from the literature.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. A. Ferber, L. Hardiman, X. Chen. Improved sublinear algorithms for classical and quantum graph coloring. arXiv:2502.06024, 2025.
2. S. Assadi, Y. Chen, S. Khanna. Sublinear algorithms for (Δ + 1) vertex coloring. SODA 2019.
3. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschritte der Physik 46, 1998. arXiv:quant-ph/9605034.
4. S. Assadi, H. Yazdanyar. Simple sublinear algorithms for (Δ + 1) vertex coloring via asymmetric palette sparsification. arXiv:2502.17629, 2025.
5. J. Morris, F. Song. Simple vertex coloring algorithms. arXiv:2102.07089, 2021.
