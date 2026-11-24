# Approximate counting of independent sets with a quantum algorithm in polynomial space

Written 24 Nov 2026.

Counting the independent sets of a graph exactly is #P-complete, and no polynomial-time approximation exists for general graphs unless NP = RP. In exponential time, a classical algorithm of [1] computes a (1 ± ε)-approximation of the number of independent sets of an n-vertex graph in time O*(1.1869^n). It branches on vertices of high degree, sends the residual graphs of low degree to a polynomial-time approximation scheme, and counts the small residual graphs by an enumerate-or-sample estimator. Here the branching tree, the low-degree residuals and the small residuals are all handled by quantum estimation, with an exact identity that turns the whole computation into one tree size plus one weighted count.

**Theorem 1.** For every ε ∈ (0, 1) and δ ∈ (0, 1), a quantum algorithm with poly(n) qubits and no quantum random access memory outputs, for any graph G on n vertices, a number within a factor 1 ± ε of the number #IS(G) of its independent sets with probability at least 1 − δ, in time

O(2^{c n} · poly(n, 1/ε) · log²(1/δ)),  c = a/(2(1 + a)) < 0.12355,  so 2^{c n} = O(1.0895^n),

where a = log₂ α and α ≈ 1.25542 is the root of α⁷ = α⁶ + 1.

Status: Claim. Assuming the tree size estimation theorem of [2], the quantum counting theorem of [3] and the approximation scheme of [4] for graphs of maximum degree at most 5. The identity of Section 1, the leaf and ticket bounds and the exponents are checked by script.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| (1 ± ε)-approximation of the number of independent sets of an n-vertex graph, success probability 1 − δ | 1.1869^n classically [1]; 1.1205^n quantum, implied by [3] and [4] (the bucketed count of Section 2 over the leaves of the branching of Section 1 run without a budget) | **1.0895^n**, polynomial space, no quantum random access memory |

All bounds hide factors polynomial in n, 1/ε and log(1/δ). That bucketed count alone takes time √T(n) = α^{n/2} = 1.1205^n, and tree size estimation [2] on the include/exclude tree with quantum counting gives 2^{n/4} = 1.1893^n. A quantum rebalance of the decomposition of [1], with its residual instances compiled into a single one, is anticipated in [1, Section 1.2]; the compiled tree of Section 1 is such a compilation, and with both parts estimated quantumly the two costs balance at 1.0895^n.

## 1. The decomposition

Fix β = 1/(1 + a) ≈ 0.7529. The preprocessing tree P of [1, Algorithm 9] starts at (G, ⌈βn⌉). At a node (H, b) it stops with a hard leaf if b ≤ 0 and with an easy leaf if H has maximum degree at most 5. Otherwise it takes a vertex v of maximum degree, deg v ≥ 6, and has the two children (H − v, b − 1) and (H − N[v], b − deg v − 1). Each independent set of H lies in exactly one child, so #IS(G) is the sum of #IS over the leaves of P. Since the budget drops by at least 1 and at least 7, P has at most T(⌈βn⌉) = O(2^{aβn}) leaves, with T(b) = T(b − 1) + T(b − 7) for b > 0 and T(b) = 1 for b ≤ 0. A hard leaf has at most (1 − β)n vertices.

The compiled tree C replaces every hard leaf H by its include/exclude tree: branch on the first vertex u of H, with children H − u and H − N[u], down to the empty graph. That tree is a full binary tree whose leaves are the independent sets of H. So C is a full binary tree, and counting its nodes gives

**#IS(G) = (N + 1)/2 + Σ_{easy leaves E} (#IS(E) − 1),**

where N is the number of nodes of C. To see it, let h and e be the numbers of hard and easy leaves of P and S_hard the sum of #IS over the hard leaves. P has 2(h + e) − 1 nodes, and replacing each hard leaf H by a tree of 2·#IS(H) − 1 nodes gives N = 2 S_hard + 2e − 1. Both terms on the right are nonnegative, since #IS(E) ≥ 1.

Each node of C is reached from the root by a path of at most n bits, and its parent, its children and whether it is a leaf are computed from that path in polynomial time. A node of P with budget b > 0 has at most 2T(b) · 2^{(1−β)n} − 1 nodes below and including it, and a node of an include/exclude tree on k vertices at most 2^{k+1} − 1. These bounds are compatible with the branching, so a ticket m in a universe of size U_C = 2T(⌈βn⌉) · 2^{(1−β)n} is mapped to a node of C or to nothing in polynomial time, every node of C getting exactly one ticket. The leaves of P get tickets in the same way in a universe of size T(⌈βn⌉).

## 2. The algorithm

1. **Tree size.** Run the tree size estimator of [2] on C with the bound T₀ = 8T(⌈βn⌉) and relative error ε. If it returns an estimate, keep it. If it reports N > T₀/(1 + ε), then N ≥ 4T(⌈βn⌉), so a fraction at least 2 · 2^{−(1−β)n} of the U_C tickets hits a node of C, and quantum counting [3] over the tickets estimates N to relative error ε in time O(2^{(1−β)n/2}/ε).
2. **Easy leaves.** For each easy leaf E let v(E) be the deterministic (1 ± ε)-approximation of #IS(E) by [4], clipped to [1, 2^n]. For each k in a range of O(n/ε) values, quantum counting over the leaf tickets of P estimates the number M_k of easy leaves with (1 + ε)^k ≤ v(E) < (1 + ε)^{k+1}. An empty bucket gives 0 with certainty, and a nonempty one is estimated to relative error ε in time O(√T(⌈βn⌉)/ε). The weighted sum Σ_k (1 + ε)^k M̂_k approximates Σ_E #IS(E) within 1 ± 3ε, and Σ_k M̂_k approximates e within 1 ± ε.
3. **Output** (N̂ + 1)/2 + Σ_k (1 + ε)^k M̂_k − Σ_k M̂_k.

The errors are at most εN ≤ 2ε #IS(G), 3ε Σ_E #IS(E) and εe ≤ ε #IS(G), so the output is within a factor 1 ± 6ε of #IS(G); running with ε/6 gives Theorem 1. Each estimate is repeated O(log(n/(εδ))) times with the median taken, so all succeed together with probability 1 − δ.

## 3. Running time

Step 1 costs O(√T₀ · poly(n) · ε^{−3/2} log²(1/δ)) = O*(2^{aβn/2}) in its first part [2] and O*(2^{(1−β)n/2}) in its second. Step 2 costs O(n/ε) counts of O*(2^{aβn/2}) each. With β = 1/(1 + a), both exponents equal a/(2(1 + a)) n, so the total is O*(2^{a n/(2(1 + a))}) = O*(1.0895^n). The space is that of [2] and [3] with oracles computed in polynomial space, so poly(n) qubits.

## 4. Measurements

[`sim/isapprox.py`](sim/isapprox.py) checks, with exact arithmetic where it decides:

- the identity of Section 1 against brute-force counting on 88 random graphs with 8 to 18 vertices and edge probabilities 0.4 to 0.85, together with the leaf bound T(⌈βn⌉), the size bound of the hard leaves and the bound N ≤ U_C;
- that the ticket map hits every node of C exactly once, by running it over the whole universe for five graphs (one of them complete) and comparing the root paths it returns;
- that bucketed sums with (1 ± ε)-accurate values stay within 1 ± 3ε, for ε = 1/4, 1/10 and 1/50;
- the exponents: 2^{−a} + 2^{−7a} ≤ 1 with a = 0.328174, the balance at β = 1/(1 + a), and the bases 1.08941 (this work), 1.18681 (classical [1]), 1.12046 (bucketed count without a budget), 1.12145 (classical preprocessing with quantum residual counting) and 1.18921 (include/exclude tree alone).

Run it with `python isapprox.py` in `sim/`. The script checks no quantum step.

## 5. Limits

- The constants of [2], [3] and [4] enter only polynomially; the base is that of the recurrence (1, 7).
- The approximation scheme of [4] needs λ = 1 below the uniqueness threshold (Δ − 1)^{Δ−1}/(Δ − 2)^Δ, which holds for maximum degree Δ ≤ 5 (the threshold is 256/243 for Δ = 5).
- Only independent sets are covered. The #2-SAT algorithm of [1] also calls an exact counting algorithm on part of its inputs, and this method does not shorten that part.
- Not formalized in Lean.

## References

1. K. Clinch, S. Gaspers, S. Mackenzie, Q. Wang. Faster exponential-time approximate counting via bounded self-reductions. arXiv:2607.06393.
2. A. Ambainis, M. Kokainis. Quantum algorithm for tree size estimation, with applications to backtracking and 2-player games. STOC 2017. arXiv:1704.06774.
3. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. arXiv:quant-ph/0005055.
4. D. Weitz. Counting independent sets up to the tree threshold. STOC 2006.

## Use of AI

The algorithm, the proofs, the scripts and this text were produced with the help of Claude Opus 5.5.
