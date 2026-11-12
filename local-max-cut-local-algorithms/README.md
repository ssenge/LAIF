# One-round classical algorithms for LocalMaxCut on regular graphs

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

The entries are expected fractions of satisfied vertices. Previous best bound: for d = 3, 0.819292 by QAOA at depth 1 and below 0.8 for the one-round flip algorithms of [1]. For d ≥ 4, to our knowledge, no value is stated before. The QAOA values for d ≥ 4 are computed here, exactly on the d-regular tree and maximized over the two angles. The classical values hold on every d-regular graph of girth at least 5.

So at depth 1 the classical rule satisfies more vertices than QAOA at every degree from 3 to 8. The difference is 0.002 at d = 3, between 0.011 and 0.028 at the odd degrees 5 and 7, and between 0.029 and 0.048 at the even degrees 4, 6 and 8.

The rule has radius 1: each vertex reads only its own seed and the seeds of its neighbours. At depth 1, the output bit of QAOA for this objective depends on the neighbourhood of radius 2, since each phase term covers a closed neighbourhood. So the classical rule uses the smaller light cone and still satisfies more vertices.

This hints that the advantage stated in [1, Theorem 2] holds against the one-bit flip algorithms of its Section 3.1, and not against one-round local algorithms in general. For degree 2, [1] already shows a classical algorithm above QAOA.

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
  - degrees above 8;
  - QAOA at depth 2 or more;
  - a proof that the angle search finds the global maximum of the depth-1 QAOA value, which the grid and the local refinement replace;
  - a deterministic error bound for the integral, which the Monte Carlo bound replaces.

## References

1. C. Carlson, Z. Jorquera, A. Kolla, S. Kordonowy. A quantum advantage over classical for local max cut. arXiv:2304.08420, 2023.
