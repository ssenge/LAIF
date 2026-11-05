# Research results

> Most of these results were generated automatically by AI, with some additional instructions from me. For questions or corrections, please [open an issue](https://github.com/ssenge/ResearchResults/issues).

Results on open problems in algorithms and complexity. Each folder holds one topic with its proofs, Lean files and scripts.

## Results

"Lean" means that the theorem is machine-checked in Lean 4 with Mathlib, using only the standard axioms. "Assuming" names a classical theorem that the Lean statement takes as an explicit hypothesis. "Claim" means a result with a written proof that is not fully formalized. This table shows the main results of each folder. Each folder states all its results, and exactly what is checked and what is not. In the rows on distributed algorithms, n is the number of nodes, D the hop diameter, and Õ hides factors polylogarithmic in n.

| Category | Problem | Before | After | Status | Details |
|---|---|---|---|---|---|
| Quantum query complexity | Exact minimum degree with cut queries | O(√n) quantum [1] and O(n) classical upper bounds, without matching lower bounds | Θ(√n) quantum against Θ(n) classical, for integer weights of O(n² log n) bits. Simple graphs stay open | Lower bounds: Lean, the quantum one assuming the approximate degree of AND. O(√n): cited | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Is the maximum of a totally monotone or inverse Monge matrix at least θ? | Θ(n) classically by SMAWK; √(rc) by plain quantum search; no quantum result known to us | O(√n log n), Ω(√n), queries only | Lean, assuming Lee et al. Q = Θ(Adv±) | [totally-monotone-maximum-queries](totally-monotone-maximum-queries/) |
| Quantum query complexity | Recognizing threshold graphs and chain graphs from the adjacency matrix | Θ(n²) classically; about n^{3/2} suggested by the 4-vertex certificate; no quantum result known to us | Θ̃(n) against Θ(n²), queries only | Part Lean, assuming BBHT and the OR bound; part Claim | [threshold-graph-recognition-queries](threshold-graph-recognition-queries/) |
| Quantum query complexity | Minimum cut and edge connectivity in the adjacency array model, n vertices, m edges, weights in [1, τ] | Õ(√(mnτ)) [10]; on dense graphs Ω(n) for τ = 1, Ω(n^{3/2}) for τ > 1, Ω(τn) | Ω(n^{3/2}√τ) for 1 ≤ τ ≤ n/4, so Θ̃(n^{3/2}√τ) on dense graphs, and Θ̃(n^{3/2}) for edge connectivity of dense simple graphs. Below dense graphs a factor n/√m stays open | Lower bound: Lean, assuming the degree bound for exact counting. Upper bound: cited | [minimum-cut-array-queries](minimum-cut-array-queries/) |
| Exact exponential algorithms, quantum | Equal Subset Sum on n integers, worst case | 3^{2n/7} ≤ 2^{0.4529n}, implied by Chukhin et al.; 2^{0.5044n} by Allcock et al. | 2^{0.4384n}, with quantum random access to quantum memory | Claim; lemmas and cost composition in Lean, with the quantum primitives as hypotheses; exponent by interval arithmetic | [quantum-equal-subset-sum](quantum-equal-subset-sum/) |
| Exact exponential algorithms, quantum | Subset Balancing on n integers with coefficients in {−d, …, d}, worst case, d = 2 and d = 3 | 5^{2n/7} ≤ 2^{0.6634n} and 7^{2n/7} ≤ 2^{0.8021n}, implied by Chukhin et al. | 2^{0.6125n} and 2^{0.7215n}, with quantum random access to quantum memory | Claim; lemmas, concavity and cost composition in Lean, with the quantum primitives as hypotheses; exponent by interval arithmetic | [quantum-subset-balancing](quantum-subset-balancing/) |
| Distributed algorithms, CONGEST | Maximum matching on bipartite planar networks | Õ(D³) from the separator scheme | Õ(D²) | Claim, with simulation; combinatorial core in Lean; paper in the folder | [exact-planar-bipartite-matching](exact-planar-bipartite-matching/) |
| Distributed algorithms, CONGEST | Maximum matching on general planar networks | Õ(s*) for a maximum matching of size s* [2] | Õ(D²), randomized | Claim, with simulation; the matrix steps in Lean | [exact-planar-bipartite-matching](exact-planar-bipartite-matching/) |
| Distributed algorithms, CONGEST | Exact single-source shortest paths on directed planar networks, nonnegative weights | Õ(D²) [3] | Õ(D), given the Label Hypothesis stated in the folder | Claim; in Lean the round bound from the Label Hypothesis and two cited results; paper arXiv:2611.02256 | [exact-shortest-paths-and-flows-on-planar-graphs](exact-shortest-paths-and-flows-on-planar-graphs/) |
| Distributed algorithms, CONGEST | Exact maximum st-flow on directed planar networks | Õ(D²) [4] | min{Õ(D²), D·n^{o(1)}}, given the Label Hypothesis | Claim; in Lean the round bound from the Label Hypothesis, a reduction for negative weights and two cited results | [exact-shortest-paths-and-flows-on-planar-graphs](exact-shortest-paths-and-flows-on-planar-graphs/) |
| Distributed algorithms, LOCAL | Round exponent κ of the (7 + ε)-approximation of minimum dominating set on planar graphs, (c/ε)^κ rounds | κ ≈ 25.81 [5] | κ < 5.89 for the algorithm of [5], same ratio. Other algorithms reach O(ε⁻⁴ log²(1/ε)) rounds [8], and ratio 7 in constant rounds [9] | Proved on paper; core inequalities in Lean; paper in the folder | [minimum-dominating-set-on-planar-graphs](minimum-dominating-set-on-planar-graphs/) |
| Distributed algorithms, LOCAL | Rounds of the (1 + ε)-approximations of [5] as a function of ε | (c/ε)^25.81; dependence on ε open | At least 1/ε − 4 rounds on every minor-closed class that contains all paths; Θ(1/ε) on forests and on outerplanar graphs | Lower bound in Lean | [minimum-dominating-set-on-planar-graphs](minimum-dominating-set-on-planar-graphs/) |
| Fine-grained complexity | Algorithmic consequences of the October 2026 claims [6, 7] that the Exponential Time Hypothesis is false | Time 2^{o(n)} for these problems would contradict ETH | One Turing machine in time 2^{εn} for several counting and parity problems, conditional on the unrefereed claims [6, 7]; some results have since turned out to be known or superseded, see the folder | Lean, as theorems about Turing machines on top of the formalized algorithm of [7] | [eth-corollaries](eth-corollaries/) |

## Minor results

| Problem | Result | Details |
|---|---|---|
| Maximum matching on general graphs with adjacency-matrix quantum queries | Õ(n^{3/2}√(1 + n/g)) queries at odd girth g | [quantum-matching-queries](quantum-matching-queries/) |
| Shortest cover and all covers of a string with quantum queries | O(√n log⁴ n) and O(√n log⁵ n), Ω(√n) | [string-cover-queries](string-cover-queries/) |
| Dominator tree, bridges of a flow graph, strong bridges and strong articulation points with quantum queries | Θ(n^{3/2}) in the matrix model, O(√(nm) log n) in the array model | [dominator-tree-queries](dominator-tree-queries/) |
| LP-type problems with n constraints and combinatorial dimension δ with quantum queries | O(δ²√n log n + δ√n log^{3/2} n) | [lp-type-queries](lp-type-queries/) |
| Minimum-cost arborescence with quantum queries | O(√(nm) log³ n), Ω(√(nm)) | [minimum-arborescence-queries](minimum-arborescence-queries/) |
| Matrix product verification AB = C with quantum queries | Ω(n^{5/3}), so Θ(n^{5/3}). Previous proof by Kintali. Our contribution: a Lean proof over F₂ and a short written proof | [matrix-product-verification-queries](matrix-product-verification-queries/) |

## Former repositories

The folders `exact-planar-bipartite-matching`, `exact-shortest-paths-and-flows-on-planar-graphs`, `minimum-dominating-set-on-planar-graphs` and `eth-corollaries` continue the repositories [ExactPlanarBipartiteMatching](https://github.com/ssenge/ExactPlanarBipartiteMatching), [ExactShortestPathsAndFlowsOnPlanarGraphs](https://github.com/ssenge/ExactShortestPathsAndFlowsOnPlanarGraphs), [MinimumDominatingSetOnPlanarGraphs](https://github.com/ssenge/MinimumDominatingSetOnPlanarGraphs) and [eth-corollaries](https://github.com/ssenge/eth-corollaries), which are no longer updated. Their histories and tags stay there; all new results are added here.

## References

1. S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022. arXiv:2201.05674.
2. T. Izumi, N. Kitamura, Y. Yamaguchi. A Nearly Linear-Time Distributed Algorithm for Exact Maximum Matching. SODA 2024, arXiv:2311.04140.
3. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019, arXiv:1912.11491.
4. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025, arXiv:2411.11718.
5. S. Amiri, S. Siebertz. Almost optimal constant-round approximation of dominating set in graph classes with excluded minors. arXiv:2610.09618.
6. OpenAI. The Exponential Time Hypothesis is False. Preprint, 17 October 2026, revised 25 October 2026. https://github.com/openai/math, family 378.
7. Anthropic. A 2^{o(n)} Time Algorithm for 3-SAT. hexagon:2610.00577v1, 26 October 2026.
8. T. Picavet. Almost tight distributed approximation for domination in sparse graph classes. arXiv:2610.31203.
9. S. Amiri, S. Siebertz, W. Wawrzyniak. Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts. arXiv:2611.02057.
10. S. Apers, T. Lee. Quantum Complexity of Minimum Cut. CCC 2021, arXiv:2011.09823.

## License

Copyright 2026 Sebastian Senge. Apache License 2.0; see [`LICENSE`](LICENSE).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
