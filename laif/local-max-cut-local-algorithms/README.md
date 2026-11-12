# Few-round classical algorithms for LocalMaxCut on regular graphs

_12 November 2026_

In LocalMaxCut, a vertex is satisfied by a cut when at least half of its neighbours lie on the other side. The objective is the number of satisfied vertices. A cut with every vertex satisfied is a local optimum of Max-Cut, since flipping any single vertex does not increase the cut. On d-regular graphs a vertex is satisfied when at least ⌈d/2⌉ of its d neighbours are on the other side.

For 3-regular graphs of large girth, [1] computes the value of QAOA at depth 1 as 0.819292 n. It also shows that the one-round flip algorithms of its Section 3.1 satisfy at most 0.8 n vertices in expectation. These algorithms draw one random bit per vertex and flip it with a probability that depends on the number of agreeing neighbours. In [1] the QAOA is expected to use the larger locality of LocalMaxCut at larger degrees.

## Result

| Degree d, graphs of large girth | QAOA at depth 1 | Classical rule of radius 1 | At least, confidence 1 − 10⁻⁹ |
|---|---|---|---|
| 3 | 0.819292 [1] | **0.82137 ± 0.00002** | 0.8212 |
| 4 | 0.891347 | **0.92011 ± 0.00002** | 0.9198 |
| 5 | 0.774273 | **0.78510 ± 0.00003** | 0.7848 |
| 6 | 0.856036 | **0.89408 ± 0.00002** | 0.8938 |
| 7 | 0.748364 | **0.77638 ± 0.00003** | 0.7761 |
| 8 | 0.828952 | **0.87675 ± 0.00002** | 0.8765 |

The entries are expected fractions of satisfied vertices. Previous best bound: for d = 3, 0.819292 by QAOA at depth 1 and below 0.8 for the one-round flip algorithms of [1]. For d ≥ 4, to our knowledge, no value is stated before. The QAOA values for d ≥ 4 are computed here, exactly on the d-regular tree and maximized over the two angles. The classical values hold on every d-regular graph of girth at least 5, and the QAOA values on every d-regular graph of girth at least 7, so the comparison holds at girth at least 7. The ± is one standard error.

So at depth 1 the classical rule satisfies more vertices than QAOA at every degree from 3 to 8. The difference is 0.002 at d = 3, between 0.011 and 0.028 at the odd degrees 5 and 7, and between 0.029 and 0.048 at the even degrees 4, 6 and 8. This differs from the trend expected in [1], where the advantage of the QAOA grows with the degree.

The rule has radius 1: each vertex reads only its own seed and the seeds of its neighbours. At depth 1, the output bit of QAOA for this objective depends on the neighbourhood of radius 2, since each phase term covers a closed neighbourhood. So the classical rule uses the smaller light cone and still satisfies more vertices.

This hints that the advantage stated in [1, Theorem 2] holds against the one-bit flip algorithms of its Section 3.1, and not against one-round local algorithms in general. For degree 2, [1] already shows a classical algorithm above QAOA.

## Large degrees, depth 1

For d from 9 to 101 a simpler rule suffices: z_u = +1 if g_u > λ d^(−1/2) Σ_{w∼u} g_w, so u compares its seed with a scaled sum of all neighbour seeds. Given the seeds of v and its neighbours, the outputs of the neighbours are independent, with P(z_u = +1) = Φ((√d g_u/λ − g_v)/√(d − 1)). So `sim/classical_d.py` samples only these d + 1 seeds and computes the distribution of the number of disagreeing neighbours exactly. The value is an average of conditional probabilities in [0, 1], so the Hoeffding bound applies, with 2 · 10⁵ samples per d. The parameter λ is chosen on separate samples and lies between 0.85 and 0.90 (`sim/classical_d.jsonl`).

The QAOA values come from `sim/qaoa_count.py`, which writes the formula of `sim/qaoa_tree.py` as sums over the number of disagreeing vertices: binomial sums for the children and grandchildren of the neighbours of v, and a dynamic program over the capped counts for the d neighbours. It agrees with `sim/qaoa_tree.py` to 10⁻¹⁵, and in double precision it agrees with 30 to 40 digit arithmetic to 10⁻¹⁵ at d = 12, 20, 26 and 50. The angles come from a grid and from warm starts (`sim/opt_count.py`, `sim/opt_warm.py`, `sim/qaoa_d.jsonl`).

| d | QAOA at depth 1 | Linear rule | At least, confidence 1 − 10⁻⁹ |
|---|---|---|---|
| 9 | 0.7311 | 0.7597 | 0.7523 |
| 10 | 0.8077 | 0.8546 | 0.8473 |
| 11 | 0.7195 | 0.7575 | 0.7501 |
| 12 | 0.7911 | 0.8456 | 0.8383 |
| 13 | 0.7115 | 0.7561 | 0.7488 |
| 14 | 0.7788 | 0.8391 | 0.8318 |
| 15 | 0.7054 | 0.7542 | 0.7469 |
| 16 | 0.7699 | 0.8331 | 0.8258 |
| 17 | 0.7002 | 0.7536 | 0.7463 |
| 18 | 0.7626 | 0.8282 | 0.8209 |
| 19 | 0.6955 | 0.7533 | 0.7460 |
| 20 | 0.7560 | 0.8242 | 0.8169 |
| 21 | 0.6913 | 0.7527 | 0.7453 |
| 30 | 0.7306 | 0.8106 | 0.8033 |
| 31 | 0.6758 | 0.7509 | 0.7436 |
| 40 | 0.7142 | 0.8015 | 0.7942 |
| 50 | 0.7021 | 0.7965 | 0.7891 |
| 51 | 0.6577 | 0.7492 | 0.7419 |
| 60 | 0.6926 | 0.7925 | 0.7852 |
| 61 | 0.6517 | 0.7490 | 0.7417 |
| 70 | 0.6850 | 0.7884 | 0.7811 |
| 71 | 0.6467 | 0.7489 | 0.7415 |
| 80 | 0.6785 | 0.7862 | 0.7788 |
| 81 | 0.6424 | 0.7483 | 0.7410 |
| 90 | 0.6731 | 0.7843 | 0.7770 |
| 91 | 0.6388 | 0.7484 | 0.7411 |
| 100 | 0.6683 | 0.7819 | 0.7746 |
| 101 | 0.6356 | 0.7478 | 0.7405 |

The classical rule is above QAOA at depth 1 at every d from 3 to 40 and at d = 50, 51, 60, 61, ..., 100, 101. The smallest margin between the lower bound of the rule and the QAOA value is 0.021, at d = 9.

**Limit d → ∞ (Claim).** For this rule, the expected satisfied fraction tends to

  1/2 + (1/π) arcsin ρ(λ), with ρ(λ)² = 8λ² / ((1 + λ²)((π + 2)λ² + π)),

which is largest at λ = (π/(π + 2))^(1/4) ≈ 0.8841, with the value 0.74687. Fix v with z_v = +1, that is g_v > λT_v with T_v = d^(−1/2) Σ_{u∼v} g_u. Given g_v and T_v, a neighbour u disagrees with v with probability 1/2 + c(λg_v − T_v)/√d + o(1/√d), where c = (2π(1 + λ²))^(−1/2). Here g_v enters the threshold of u with weight λ/√d, and the condition on T_v shifts each g_u by T_v/√d. The indicators of disagreement have conditional variance 1/4 − c² each, since the condition on T_v removes their component along g_u. By the central limit theorem, the number of disagreeing neighbours is d/2 + √d(c(λg_v − T_v) + sN) + o(√d), with s² = 1/4 − c² and N standard normal. So the value tends to 2 P(sN + c(λg − T) ≥ 0, g > λT) for independent standard normal g, T and N. This is an orthant probability of two correlated normal variables, which gives the formula. `sim/classical_limit.py` checks it against a Monte Carlo evaluation of the limit expression. The finite values at odd d lie slightly above it: 0.7478 at d = 101, 0.746 ± 0.001 at d = 401 and 0.749 ± 0.002 at d = 1601.

The QAOA values at depth 1 decrease with d along both parities over the computed range. They lie below the classical limit 0.74687 from d = 9 on for odd d and from d = 24 on for even d. A limit of the QAOA value for d → ∞ is not computed here.

## Two rounds against QAOA at depth 2, d = 3

At depth p, the output bit of QAOA for this objective depends on the qubits within distance 2p, since each phase term covers a closed neighbourhood. At depth 2 this is distance 4.

| 3-regular graphs of large girth | Output radius | Expected satisfied fraction | At least, confidence 1 − 10⁻⁹ |
|---|---|---|---|
| QAOA at depth 2 | 4 | 0.895826 | |
| Rule of radius 1, then one round of priority flips | 3 | **0.94414 ± 0.00003** | 0.9438 |
| The same, then one round in which every unsatisfied vertex flips | 4 | **0.96986 ± 0.00002** | 0.9695 |

The QAOA value is computed here, exactly on the 3-regular tree and maximized over the four angles. The QAOA value holds on 3-regular graphs of girth at least 11, the classical values at girth at least 9 and 11. So a classical rule whose output depends on a smaller neighbourhood than that of depth-2 QAOA satisfies more vertices.

**Priority flips.** Every vertex u draws a second seed h_u, uniform on [0, 1]. Start from the output z of the rule of radius 1. Call u unsatisfied when fewer than 2 of its neighbours differ from z_u. An unsatisfied vertex flips its bit when its h is larger than the h of each unsatisfied neighbour. Flipping an unsatisfied vertex satisfies it. No two adjacent vertices flip in the same round. The output at u depends on the seeds within distance 3 of u, so the satisfaction of v depends on those within distance 4. On a 3-regular graph of girth at least 9 that ball is a tree, and the value equals the tree value. For the rule with the further round, distance 5 and girth at least 11.

**QAOA at depth p on the tree.** Each qubit carries a path of 2p + 1 bits: its bit before each mixer on the ket side, the measured bit, and the bits on the bra side. The amplitude factorizes into one mixer weight per qubit and one phase per vertex term. Each vertex term couples a vertex with its neighbours, so on the tree the sum is computed from the leaves inwards, with one message per edge indexed by the paths of both endpoints. Only the vertex terms with centre within distance 2p of v enter, by the light cone. `sim/qaoa_p.py` implements this. It agrees with the depth-1 code for d = 3 and d = 4. It gives the same value on a tree two levels deeper, and reproduces depth 1 when the second layer is switched off. `sim/opt_p2.py` searches the angles from 46 starts, 40 of them random, and the 5 best local maxima all have the value 0.895826 (`sim/qaoa_p2.jsonl`). The classical values come from `sim/tree_eval.py`, which samples 10⁸ independent trees for each rule, seed 20261112 (`sim/eval_tree.jsonl`), with the Hoeffding bound as above.

## The rule

Every vertex u draws an independent standard normal seed g_u. Let s₍₁₎ ≤ ... ≤ s₍d₎ be the sorted seeds of the d neighbours of u. Then z_u = +1 if g_u > T, and z_u = −1 otherwise, with the threshold T below.

- **d = 3.** With a ≤ m ≤ b the sorted neighbour seeds, T = m + m² (a + b) / 4. So u compares its seed with the median seed of its neighbours, and the threshold is pushed further out when the median is far from 0. With the plain median threshold, the value is 0.8160.
- **d ≥ 4.** T = Σᵢ wᵢ s₍ᵢ₎, a weighted sum of the sorted neighbour seeds with symmetric weights (wᵢ = w_{d+1−i}):

  | d | w₁, ..., w_d |
  |---|---|
  | 4 | 0.14, 0.64, 0.64, 0.14 |
  | 5 | 0.04, 0.39, 0.81, 0.39, 0.04 |
  | 6 | 0.08, 0.25, 0.61, 0.61, 0.25, 0.08 |
  | 7 | 0.04, 0.24, 0.45, 0.65, 0.45, 0.24, 0.04 |
  | 8 | 0.06, 0.22, 0.42, 0.41, 0.41, 0.42, 0.22, 0.06 |

  The middle order statistics carry most of the weight, so u again compares its seed with a smoothed median of its neighbours.

Each rule commutes with flipping every seed. Ties have probability zero.

The satisfaction of v depends only on the outputs of v and its neighbours, so on the seeds of the at most 1 + d + d(d − 1) = d² + 1 vertices within distance 2 of v. On a d-regular graph of girth at least 5 these vertices are distinct, so the expected satisfied fraction equals the value on the d-regular tree, on every such graph.

## QAOA at depth 1

The state is exp(−iβ Σ X) exp(−iγC) |+⟩ⁿ, where C is the sum of the satisfaction indicators. The expectation of the indicator at v involves the qubits of v and its neighbours after the mixer, and the phase terms of the vertices within distance 2 of v, which act on the qubits within distance 3. On the d-regular tree, `sim/qaoa_tree.py` writes the expectation as a sum over the 2^(d+1) × 2^(d+1) pairs of bra and ket assignments of the closed neighbourhood of v. Each term is a product of one factor per neighbour u of v. Each such factor is an average over the other neighbours of u, with one factor per child of u, and each child factor is an average over the child's own neighbours. This is exact on the tree. For d = 3 it agrees to 10⁻¹⁴ at several angle pairs, up to the sign convention of the angles, with the 22-qubit statevector of `sim/qaoa_lmc.py`. `sim/qaoa_scan.py` evaluates a grid of 72 × 36 angle pairs over γ ∈ [0, 2π) and β ∈ [0, π/2), since the objective is invariant under the global flip, and refines the 6 best points (`sim/qaoa_values.jsonl`). The optimal angles (γ, β) are close to (5.70, 1.29) for even d and (0.60, 0.32) for odd d.

## Status and checks

The results are numerical, and no part is formalized in Lean.

- **Value of the rule, d = 3:** `sim/lmc_eval.py` samples 4 · 10⁸ independent trees of radius 2 around a vertex, seed 20261112, and applies the rule to the vertex and its three neighbours. It gives 0.821367 with standard error 0.000019 (`sim/eval_c025.txt`). For 0/1 samples, the two-sided Hoeffding bound at confidence 1 − 10⁻⁹ gives at least 0.821204. With the coefficient 1/4 replaced by 0.2 or 0.3, the value is 0.8213 or 0.8212.
- **Value of the rule, d = 4 to 8:** `sim/lmc_eval_d.py` samples 2 · 10⁸ independent trees of radius 2 for each d, seed 20261112 (`sim/eval_d.jsonl`), with the same Hoeffding bound. The weights come from a search over symmetric weight vectors on 4 · 10⁵ samples (`sim/rd.py`), rounded to two decimals, and are evaluated on fresh samples.
- **Finite graphs, d = 3:** `sim/lmc_graph.py` runs the rule on random 3-regular multigraphs with 2 · 10⁶ vertices, from the configuration model. Three graphs give 0.82120, 0.82114 and 0.82128. These graphs have O(1) short cycles, so their value matches the tree value up to sampling noise. On the 3-regular cages of girth 5, 6 and 8 (10, 14 and 30 vertices), the dodecahedron, and the 3-regular symmetric graphs of girth 6 with 18 and 20 vertices, Monte Carlo over the seeds gives values from 0.82134 to 0.82141, each within about 1.3 standard errors of the tree value.
- **QAOA at depth 1, d = 3:** `sim/qaoa_lmc.py` computes the exact expectation for one vertex on the 22 qubits of the 3-regular tree of radius 3, which holds the light cone of the vertex term. Optimizing over γ and β gives 0.8192921, as in [1, Appendix B].
- **One-bit flip algorithms, d = 3:** `sim/lmc_flip.py` computes the exact value of the flip algorithms of [1, Section 3.1] by enumerating the 2¹⁰ initial bits of the tree of radius 2, and optimizes over their parameters. The best value found is 0.7726, consistent with [1, Theorem 4]. With flip probabilities that also depend on the vertex's own initial bit, the best value found is 0.7797.
- **Origin of the rule, d = 3:** `sim/lmc_sym.py` trains smoothed versions of threshold rules built from a few odd features of the sorted neighbour seeds, then evaluates the hard rule on fresh samples. With nine features of degree up to 3, the value is about 0.8218.
- **Not covered:**
  - graphs of girth below 5 (on the cube graph, of girth 4, the value for d = 3 is about 0.8096);
  - degrees above 101, and from 41 to 101 the degrees not listed in `sim/qaoa_d.jsonl`;
  - a limit of the QAOA value for d → ∞, and a formal proof of the classical limit;
  - QAOA at depth 3 or more, and at depth 2 for d ≥ 4;
  - a proof that the angle searches find the global maxima of the QAOA values, which grids, random starts and local refinements replace;
  - a deterministic error bound for the integral, which the Monte Carlo bound replaces.

## References

1. C. Carlson, Z. Jorquera, A. Kolla, S. Kordonowy. A quantum advantage over classical for local max cut. arXiv:2304.08420, 2023.
