<div align="center">

<img src="logo.gif" alt="Barbarossa, a red-bearded 1980s computer nerd at his home computer" width="240">

# BarbarossAI Research Project

**Why waste AI slop on social media: new bounds and faster algorithms for open problems in algorithms and complexity!**

[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/proofs-Lean%204%20%2B%20Mathlib-8a2be2.svg)](https://leanprover-community.github.io/)
[![Issues](https://img.shields.io/badge/questions-open%20an%20issue-orange.svg)](https://github.com/ssenge/ResearchResults/issues)

[Results](#results) · [Minor results](#minor-results) · [Former repositories](#former-repositories) · [References](#references) · [Use of AI](#use-of-ai)

</div>

---

> Most of these results were generated automatically by AI, with some additional instructions from me. They may contain errors, so please read them with care. For questions or corrections, please [open an issue](https://github.com/ssenge/ResearchResults/issues).

Results on open problems in algorithms and complexity. Each folder holds one topic with its proofs, Lean files and scripts.

## Results

"Lean" means that the theorem is machine-checked in Lean 4 with Mathlib, using only the standard axioms. "Assuming" names a classical theorem that the Lean statement takes as an explicit hypothesis. "Claim" means a result with a written proof that is not fully formalized. This table shows the main results of each folder. Each folder states all its results, and exactly what is checked and what is not. In the rows on distributed algorithms, n is the number of nodes, D the hop diameter, and Õ hides factors polylogarithmic in n.

| Category | Problem | Before | After | Status | Details |
|---|---|---|---|---|---|
| Quantum query complexity | Exact minimum degree with cut queries | O(√n) quantum [1] and O(n) classical upper bounds, without matching lower bounds | Θ(√n) quantum against Θ(n) classical, for integer weights of O(n² log n) bits. Simple graphs stay open | Lower bounds: Lean, the quantum one assuming the approximate degree of AND. O(√n): cited | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Is the maximum of a totally monotone or inverse Monge matrix at least θ? | Θ(n) classically by SMAWK; √(rc) by plain quantum search; no quantum result known to us | O(√n log n), Ω(√n), queries only | Lean, assuming Lee et al. Q = Θ(Adv±) | [totally-monotone-maximum-queries](totally-monotone-maximum-queries/) |
| Quantum query complexity | Recognizing threshold graphs and chain graphs from the adjacency matrix | Θ(n²) classically; about n^{3/2} suggested by the 4-vertex certificate; no quantum result known to us | Θ̃(n) against Θ(n²), queries only | Part Lean, assuming BBHT and the OR bound; part Claim | [threshold-graph-recognition-queries](threshold-graph-recognition-queries/) |
| Quantum query complexity | Minimum cut and edge connectivity in the adjacency array model, n vertices, m edges, weights in [1, τ] | Õ(√(mnτ)) [10]; on dense graphs Ω(n) for τ = 1, Ω(n^{3/2}) for τ > 1, Ω(τn) | Ω(n^{3/2}√τ) for 1 ≤ τ ≤ n/4, so Θ̃(n^{3/2}√τ) on dense graphs, and Θ̃(n^{3/2}) for edge connectivity of dense simple graphs. Below dense graphs a factor n/√m stays open | Lower bound: Lean, assuming the degree bound for exact counting. Upper bound: cited | [minimum-cut-array-queries](minimum-cut-array-queries/) |
| Quantum query complexity | Exact s-t minimum cut on simple graphs, adjacency list, n vertices, m edges, f = λ_st | Õ(√m n^{5/6}), so Õ(n^{11/6}) [11]; on dense graphs Ω(n) | Õ(√(mn) + n(mf)^{1/4}), so Õ(n^{7/4}) in the worst case; Õ(n^{3/2}) at minimum degree Ω(n), tight; Ω(n^{3/2}) on dense graphs. The bound of [11] stays smaller below m = n^{2/3} f | Claim; deterministic core in Lean, with successive shortest paths, the sparsifier and strengths as hypotheses | [st-minimum-cut-queries](st-minimum-cut-queries/) |
| Quantum query complexity | Success probability of k-distinctness with T queries, on the hard inputs of [21] | at most O(1/n + T^{7/2}/n^{5/2}) for k = 3 [21]; known to be attained at the bounded-error point T = n^{5/7} [22] | attained up to polylog factors for all n^{3/7} ≤ T ≤ n^{5/7}; for every k ≥ 3, the general bound of [21] is attained for n^{1 − 2^{k−1}/(2^k − 1)} ≤ T ≤ √n | Claim; exponents in Lean | [k-distinctness-success-probability](k-distinctness-success-probability/) |
| Exact exponential algorithms, quantum | Equal Subset Sum on n integers, worst case | 3^{2n/7} ≤ 2^{0.4529n}, implied by Chukhin et al.; 2^{0.5044n} by Allcock et al. | 2^{0.4384n}, with quantum random access to quantum memory | Claim; lemmas and cost composition in Lean, with the quantum primitives as hypotheses; exponent by interval arithmetic | [quantum-equal-subset-sum](quantum-equal-subset-sum/) |
| Exact exponential algorithms, quantum | Subset Balancing on n integers with coefficients in {−d, …, d}, worst case, d = 2 and d = 3 | 5^{2n/7} ≤ 2^{0.6634n} and 7^{2n/7} ≤ 2^{0.8021n}, implied by Chukhin et al. | 2^{0.6125n} and 2^{0.7215n}, with quantum random access to quantum memory | Claim; lemmas, concavity and cost composition in Lean, with the quantum primitives as hypotheses; exponent by interval arithmetic | [quantum-subset-balancing](quantum-subset-balancing/) |
| Parameterized algorithms, quantum | Vertex Cover, parameter k | 1.25281^k randomized and 1.25284^k deterministic classically; 1.175^k quantum in a 2021 thesis; about 1.1287^k by backtracking on 1.2738^k | 1.1193^k (1.1194^k from the deterministic analysis alone), bounded error, polynomial space | Claim; counting, cost recursion and level scan in Lean, with the quantum primitives as hypotheses; the conditions on the classical algorithms argued from their analyses | [quantum-vertex-cover](quantum-vertex-cover/) |
| Exact exponential algorithms, quantum | Maximum Independent Set on n vertices | 1.19951^n classically; 2^{n/5} = 1.1488^n quantum; about 1.1337^n by backtracking on a plain tree | 1.0953^n, bounded error, polynomial space | As above | [quantum-vertex-cover](quantum-vertex-cover/) |
| Quantum cryptanalysis, superposition queries | Key recovery and universal forgery for CHCTR (HCTR2 cascaded under two keys) | 2n/3-bit multi-user security against classical attackers; no quantum attack known to us | About 2n + 2 quantum encryption queries (258 for AES), Q2 model | Claim; shift identities, key recovery, collision cases and Simon sampling identity in Lean; query bound in the ideal cipher model; AES test at full size | [hctr2-superposition-attacks](hctr2-superposition-attacks/) |
| Quantum cryptanalysis, superposition queries | Key recovery and universal forgery for HCTR++, and for HCTR2-TwKD under one tweak | Security beyond the birthday bound against classical attackers; no quantum attack known to us | About 4n + 4 queries (HCTR++, encryption and decryption) and n + 2 queries (HCTR2-TwKD, inside its per-tweak limit), Q2 model | As above | [hctr2-superposition-attacks](hctr2-superposition-attacks/) |
| Exact exponential algorithms, quantum | Undirected Hamiltonicity, k-path, p-packing of q-sets; TSP with integer weights of total w | 1.6569^n, 1.6569^k, 3.3432^p for q = 3 [18, 19]; w 1.6569^n, and 1.728^n for any weights with QRAM [20] | 1.6330^n, 1.6330^k, 2.804^p; w 1.6330^n, with polynomially many qubits and no QRAM. TSP with arbitrary weights unchanged | Claim; exponents in Lean | [quantum-algebraic-sieves](quantum-algebraic-sieves/) |
| Distributed algorithms, CONGEST | Maximum matching on bipartite planar networks | Õ(D³) from the separator scheme | Õ(D²) | Claim, with simulation; combinatorial core in Lean; paper in the folder | [exact-planar-bipartite-matching](exact-planar-bipartite-matching/) |
| Distributed algorithms, CONGEST | Maximum matching on general planar networks | Õ(s*) for a maximum matching of size s* [2] | Õ(D²), randomized | Claim, with simulation; the matrix steps in Lean | [exact-planar-bipartite-matching](exact-planar-bipartite-matching/) |
| Distributed algorithms, CONGEST | Exact single-source shortest paths on directed planar networks, nonnegative weights | Õ(D²) [3] | Õ(D), with the rotation lists as input | Lean, assuming five cited results named in the folder: realization, distance labels, face identifiers, aggregation, smoothing; paper arXiv:2611.02256 | [exact-shortest-paths-and-flows-on-planar-graphs](exact-shortest-paths-and-flows-on-planar-graphs/) |
| Distributed algorithms, CONGEST | Exact maximum st-flow on directed planar networks | Õ(D²) [4] | min{Õ(D²), D·n^{o(1)}}, with the rotation lists as input | Claim; in Lean the round bound, assuming a reduction for negative weights and the same five cited results | [exact-shortest-paths-and-flows-on-planar-graphs](exact-shortest-paths-and-flows-on-planar-graphs/) |
| Distributed algorithms, LOCAL | Round exponent κ of the (7 + ε)-approximation of minimum dominating set on planar graphs, (c/ε)^κ rounds | κ ≈ 25.81 [5] | κ < 5.89 for the algorithm of [5], same ratio. Other algorithms reach O(ε⁻⁴ log²(1/ε)) rounds [8], and ratio 7 in constant rounds [9] | Proved on paper; core inequalities in Lean; paper in the folder | [minimum-dominating-set-on-planar-graphs](minimum-dominating-set-on-planar-graphs/) |
| Distributed algorithms, LOCAL | Rounds of the (1 + ε)-approximations of [5] as a function of ε | (c/ε)^25.81; dependence on ε open | At least 1/ε − 4 rounds on every minor-closed class that contains all paths; Θ(1/ε) on forests and on outerplanar graphs | Lower bound in Lean | [minimum-dominating-set-on-planar-graphs](minimum-dominating-set-on-planar-graphs/) |
| Quantum machine learning | Worst-case generalization error of quantum neural networks with T trainable two-qubit gates, each used at most M times, N samples | O(√(T log T / N)), and O(√(T log(MT) / N)) with reuse [12] | Ω(√(T log((M + 1)T) / N)) for empirical risk minimization with N ≥ m samples, where m = Θ(T log((M + 1)T)) is the size of the shattered set, so the logarithmic factor is needed; sets shattered at constant margin have size Θ(T log(MT)) | Claim, with simulation; shattering core in Lean, assuming the Fourier expansion of the bump | [qnn-generalization-lower-bounds](qnn-generalization-lower-bounds/) |
| Quantum machine learning | Trainable parameters a fixed-encoding quantum neural network needs to approximate the Hölder ball of order β on [0, 1]^d within ε in sup norm | O(ε^{−d/β}) up to constants, outside a small set or in L² [14]; for periodic C^k functions O(ε^{−(d+1)/k}) [15]; lower bound Ω̃(ε^{−d}) gates for Lipschitz functions (β = 1) [16] | Θ(ε^{−d/β}) up to a factor log(1/ε) for every β > 0, for any fixed encoding, depth and width, with at most (1/ε)^{O(1)} trainable gates; deep ReLU networks need only Õ(ε^{−d/(2β)}) for integer β | Claim, with simulation | [qnn-approximation-rates](qnn-approximation-rates/) |
| Quantum machine learning | Classical cost of estimating the loss m = tr(Aρ₀A†O) of the free fermion stacked LCU, l layers of k Gaussian unitaries on n qubits, to additive error ε | O(k^{2l} n³) by expanding all k^l terms, against O(lkn²) quantum gates [24] | O(l n⁵ log(1/δ)/ε²) for O = Z₁, with no dependence on k at fixed ε, and the same for each gradient entry. On the random ensemble of [24] the sampler's variance has mean at most E[p_s] + 2^{1−n}, close to that of postselected shots | Claim, with simulation | [stacked-lcu-sampling](stacked-lcu-sampling/) |
| Quantum optimization | Gradient queries for finite-sum convex optimization with a quantum finite-sum oracle, n convex components, high dimension d, in the four cases of [25]: ℓ-smooth or L-Lipschitz components, regularizer μ-strongly convex or not | Quantum lower bounds Ω(n + n^{3/4}κ^{1/4} log^{1/2}(Δμ/(εℓ))) for κ = ℓ/μ ≥ 100n, and Ω̃(n + n^{3/4}(ℓR²/ε)^{1/4}), Ω̃(n + n^{3/4}L^{1/2}(εμ)^{−1/4}), Ω̃(n + n^{3/4}(LR/ε)^{1/2}) [25]; the classical lower bounds of [26] are Ω(n + √(nκ) log(1/ε)), Ω(n + R√(nℓ/ε)), Ω(n + L√(n/(με))), Ω(n + LR√n/ε) | The classical bounds hold for quantum algorithms too, for d polynomial and queries in a ball: Ω(√(nκ) log(Δμ/(εℓ))), and Ω(n + R√(nℓ/ε)), Ω(n + L√(n/(με))), Ω(n + LR√n/ε) for n ≥ 600. So there is no quantum speedup in high dimension | Claim, with simulation | [quantum-finite-sum-lower-bound](quantum-finite-sum-lower-bound/) |
| Quantum optimization | ε-approximate Nash equilibrium, or the value up to ±ε, of an m × n zero-sum game with entries in [−1, 1], entry queries | Ω(√(m + n)) for constant ε [28]; upper bound Õ(√(m + n) ε^{−2.5} + ε^{−3}) [27] | Ω(√(max(m, n) · min(m, n, 1/ε))), so Ω(√((m + n)/ε)) when min(m, n) ≥ 1/ε | Lean for the combinatorial part, assuming the relational adversary bound | [zero-sum-games-precision-lower-bound](zero-sum-games-precision-lower-bound/) |
| Fine-grained complexity | Algorithmic consequences of the October 2026 claims [6, 7] that the Exponential Time Hypothesis is false | Time 2^{o(n)} for these problems would contradict ETH | One Turing machine in time 2^{εn} for several counting and parity problems, conditional on the unrefereed claims [6, 7]; some results have since turned out to be known or superseded, see the folder | Lean, as theorems about Turing machines on top of the formalized algorithm of [7] | [eth-corollaries](eth-corollaries/) |

## Minor results

| Problem | Result | Details |
|---|---|---|
| Maximum matching on general graphs with adjacency-matrix quantum queries | Õ(n^{3/2}√(1 + n/g)) queries at odd girth g | [quantum-matching-queries](quantum-matching-queries/) |
| Shortest cover and all covers of a string with quantum queries | O(√n log⁴ n) and O(√n log⁵ n), Ω(√n) | [string-cover-queries](string-cover-queries/) |
| Dominator tree, bridges of a flow graph, strong bridges and strong articulation points with quantum queries | Θ(n^{3/2}) in the matrix model, O(√(nm) log n) in the array model | [dominator-tree-queries](dominator-tree-queries/) |
| LP-type problems with n constraints and combinatorial dimension δ with quantum queries | O(δ²√n log n + δ√n log^{3/2} n) | [lp-type-queries](lp-type-queries/) |
| Minimum-cost arborescence with quantum queries | O(√(nm) log³ n), Ω(√(nm)) | [minimum-arborescence-queries](minimum-arborescence-queries/) |
| Depth D of fixed upload circuits approximating a tunable upload gate e^{iwxσ_z} on [0, 1] to error ε | D ≤ (2/π)\|w\| + (32/π) ln(1/ε) + 17, and D ≥ (2/π)\|w\|(1 − O(ε)) − O(1); so D = Θ(log(1/ε)) for fixed w, where O((log 1/ε)^σ) for every σ > 1 was known [13] | [fixed-upload-depth](fixed-upload-depth/) |
| Generalization gap of hybrid models whose Lipschitz classical head reads one quantum expectation, T trainable gates used at most M times | Rademacher complexity O((B + √(ΛβB) + B√(T log(e + MT)))/√N) for heads with Lipschitz constant Λ and bound B, with no width or depth factor; tight for worst-case data. [17] treats heads reading several expectations, with bound Õ((α^k/√N)(k^{3/2}√(mn) + √(T log T))) | [hybrid-qnn-generalization](hybrid-qnn-generalization/) |
| Qubits q against classical latent dimension c on the (ℓ, n, k)-hypergraph translation task of [23], N = (n choose k) | A hybrid model with q qubits and c = N − (q choose k) + 2n classical coordinates samples the task exactly; models meeting the regularity assumptions of [23], with full-rank quantum states, need c ≥ N − 4^q. The endpoints were n qubits and c ≥ N − 1 [23] | [hybrid-memory-tradeoff](hybrid-memory-tradeoff/) |
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
11. S. Apers, A. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.
12. M. C. Caro, H.-Y. Huang, M. Cerezo, K. Sharma, A. Sornborger, L. Cincio, P. J. Coles. Generalization in quantum machine learning from few training data. Nature Communications 13, 4919 (2022). arXiv:2111.05292.
13. A. Y. Liu, L. Pira. The Cost of Removing Tunability in Quantum Data Re-Uploading. arXiv:2606.25598.
14. Z. Yu, Q. Chen, Y. Jiao, Y. Li, X. Lu, X. Wang, J. Z. Yang. Non-asymptotic Approximation Error Bounds of Parameterized Quantum Circuits. NeurIPS 2024, arXiv:2310.07528.
15. A. Neufeld, P. Schmocker, V. K. Tran. Approximation rates of quantum neural networks for periodic functions via Jackson's inequality. arXiv:2511.16149.
16. H. Zhao, L. Lewis, I. Kannan, Y. Quek, H.-Y. Huang, M. C. Caro. Learning quantum states and unitaries of bounded gate complexity. arXiv:2310.19882.
17. T. Wu, A. Bentellis, A. Sakhnenko, J. M. Lorenz. Generalization Bounds in Hybrid Quantum-Classical Machine Learning Models. arXiv:2504.08456.
18. A. Björklund. Determinant sums for undirected Hamiltonicity. SIAM J. Comput. 43(1), 2014, arXiv:1008.0541.
19. A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto. Narrow sieves for parameterized paths and packings. J. Comput. Syst. Sci. 87, 2017, arXiv:1007.1161.
20. A. Ambainis, K. Balodis, J. Iraids, M. Kokainis, K. Prūsis, J. Vihrovs. Quantum speedups for exponential-time dynamic programming algorithms. SODA 2019, arXiv:1807.05209.
21. A. Belovs. Tight quantum lower bound for k-distinctness. arXiv:2604.05133, 2026.
22. A. M. Childs, S. Jeffery, R. Kothari, F. Magniez. A time-efficient quantum walk for 3-distinctness using nested updates. arXiv:1302.7316, 2013.
23. E. R. Anschuetz, X. Gao. Arbitrary Polynomial Separations in Trainable Quantum Machine Learning. arXiv:2402.08606.
24. N. Khatri, S. Zohren, G. Matos. Stacking the Deck: Tunable Trainability in Stacked LCUs. arXiv:2607.24686.
25. Y. Zhang, C. Zhang, C. Fang, L. Wang, T. Li. Quantum Algorithms and Lower Bounds for Finite-Sum Optimization. ICML 2024, arXiv:2406.03006.
26. B. Woodworth, N. Srebro. Tight Complexity Bounds for Optimizing Composite Objectives. NeurIPS 2016, arXiv:1605.08003.
27. A. Bouland, Y. M. Getachew, Y. Jin, A. Sidford, K. Tian. Quantum speedups for zero-sum games via improved dynamic Gibbs sampling. ICML 2023, arXiv:2301.03763.
28. T. Li, S. Chakrabarti, X. Wu. Sublinear quantum algorithms for training linear and kernel-based classifiers. ICML 2019, arXiv:1904.02276.

## License

Copyright 2026 Sebastian Senge. Apache License 2.0; see [`LICENSE`](LICENSE).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
