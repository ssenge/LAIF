# A one-round classical algorithm for LocalMaxCut on 3-regular graphs

_12 November 2026_

In LocalMaxCut, a vertex is satisfied by a cut when at least half of its neighbours lie on the other side. The objective is the number of satisfied vertices. A cut with every vertex satisfied is a local optimum of Max-Cut, since flipping any single vertex does not increase the cut. On 3-regular graphs a vertex is satisfied when at least 2 of its 3 neighbours are on the other side.

For 3-regular graphs of large girth, [1] computes the value of QAOA at depth 1 as 0.819292 n. It also shows that the one-round flip algorithms of its Section 3.1 satisfy at most 0.8 n vertices in expectation. These algorithms draw one random bit per vertex and flip it with a probability that depends on the number of agreeing neighbours.

## Result

| Quantity, 3-regular graphs of large girth | Previous best bound | This folder |
|---|---|---|
| Expected fraction of satisfied vertices, one-round local algorithm | 0.819292, QAOA at depth 1 [1]; below 0.8 for the one-round flip algorithms of [1] | **0.82137 ± 0.00002**, at least 0.8212 at confidence 1 − 10⁻⁹, classical rule of radius 1, girth ≥ 5 |

The rule has radius 1: each vertex reads only its own seed and the seeds of its neighbours. At depth 1, the output bit of QAOA for this objective depends on the neighbourhood of radius 2, since each phase term covers a closed neighbourhood. So the classical rule uses the smaller light cone and still satisfies more vertices.

This hints that the advantage stated in [1, Theorem 2] holds against the one-bit flip algorithms of its Section 3.1, and not against one-round local algorithms in general. For degree 2, [1] already shows a classical algorithm above QAOA.

## The rule

Every vertex u draws an independent standard normal seed g_u. Let a ≤ m ≤ b be the sorted seeds of the three neighbours of u. Then

  z_u = +1 if g_u > m + m² (a + b) / 4, and z_u = −1 otherwise.

So u compares its seed with the median seed of its neighbours, and the threshold is pushed further out when the median is far from 0. The rule commutes with flipping every seed. Ties have probability zero. With the plain median threshold, the value is 0.8160.

The satisfaction of v depends only on the outputs of v and its neighbours, so on the seeds of the at most 10 vertices within distance 2 of v. On a 3-regular graph of girth at least 5 these 10 vertices are distinct, so the expected satisfied fraction equals the value on the 3-regular tree, on every such graph.

## Status and checks

The results are numerical, and no part is formalized in Lean.

- **Value of the rule:** `sim/lmc_eval.py` samples 4 · 10⁸ independent trees of radius 2 around a vertex, seed 20261112, and applies the rule to the vertex and its three neighbours. It gives 0.821367 with standard error 0.000019 (`sim/eval_c025.txt`). For 0/1 samples, the two-sided Hoeffding bound at confidence 1 − 10⁻⁹ gives at least 0.821204. With the coefficient 1/4 replaced by 0.2 or 0.3, the value is 0.8213 or 0.8212.
- **Finite graphs:** `sim/lmc_graph.py` runs the rule on random 3-regular multigraphs with 2 · 10⁶ vertices, from the configuration model. Three graphs give 0.82120, 0.82114 and 0.82128. These graphs have O(1) short cycles, so their value matches the tree value up to sampling noise. On the Petersen graph, the dodecahedron and the Heawood, Pappus, Desargues and Tutte 8-cage graphs, Monte Carlo over the seeds gives values from 0.82134 to 0.82141, each within about 1.3 standard errors of the tree value.
- **QAOA at depth 1:** `sim/qaoa_lmc.py` computes the exact expectation for one vertex on the 22 qubits of the 3-regular tree of radius 3, which holds the light cone of the vertex term. The phase operator is exp(−iγC), with C the sum of the indicator terms, and the mixer is exp(−iβ Σ X). Optimizing over γ and β gives 0.8192921, as in [1, Appendix B].
- **One-bit flip algorithms:** `sim/lmc_flip.py` computes the exact value of the flip algorithms of [1, Section 3.1] by enumerating the 2¹⁰ initial bits of the tree of radius 2, and optimizes over their parameters. The best value found is 0.7726, consistent with [1, Theorem 4]. With flip probabilities that also depend on the vertex's own initial bit, the best value found is 0.7797.
- **Origin of the rule:** `sim/lmc_sym.py` trains smoothed versions of threshold rules built from a few odd features of the sorted neighbour seeds, then evaluates the hard rule on fresh samples. With nine features of degree up to 3, the value is about 0.8218.
- **Not covered:**
  - graphs of girth below 5 (on the cube graph, of girth 4, the value is about 0.8096);
  - degrees other than 3;
  - QAOA at depth 2 or more;
  - a deterministic error bound for the integral, which the Monte Carlo bound replaces.

## References

1. C. Carlson, Z. Jorquera, A. Kolla, S. Kordonowy. A quantum advantage over classical for local max cut. arXiv:2304.08420, 2023.
