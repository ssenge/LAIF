# Risk-aware disjoint routing: hardness, exact classical and quantum algorithms, and a compact QUBO

Written 16 Nov 2026.

The problem is from [1], which models resilient routing in a network as follows. An undirected graph G with link latencies c ≥ 0, a source s and two terminals t₁, t₂ are given, together with a joint failure probability p(e, f) ≥ 0 for every pair of links and a weight B ≥ 0. The task is to find internally vertex-disjoint paths P₁ from s to t₁ and P₂ from s to t₂ that minimize

    F(P₁, P₂) = c(P₁) + c(P₂) + B · Σ_{e ∈ P₁, f ∈ P₂} p(e, f).

The first two terms are the latency of the working and the backup path, and the last term is the risk that one event takes down both. In [1] the problem is solved with a QUBO formulation, and the related min-prod problem is posed: find two internally vertex-disjoint paths from s to t that minimize (|P₁| + C)(|P₂| + C) for a constant C ≥ 0, with its complexity stated as open.

## Results

**Theorem 1 (hardness).** For every rational constant C ≥ 0, the min-prod problem of [1] is NP-hard, also in the version with two terminals t₁ and t₂.

**Corollary 2.** The routing problem of [1] is NP-hard even with unit latencies and a uniform joint failure probability p(e, f) = q, for any fixed rational q > 0 and rational B > 0.

**Theorem 3 (exact classical algorithm).** An exact algorithm enumerates the first path in the order of a lower bound on F and completes each candidate optimally with one shortest path computation. It evaluates at most N + 1 candidates, where N is the number of simple paths P₁ whose lower bound does not exceed the optimum, and each step takes polynomial time.

**Theorem 4 (exact quantum algorithm).** Branch-and-bound over prefixes of the first path, with a monotone bound, is accelerated by quantum branch-and-bound [2]. With integer latencies and integer values B · p(e, f), it finds an optimal pair, with bounded error, using

    Õ(√T · n^{3/2} · log c_max)

calls of the branching and bounding procedures, each with at most n − 1 bound evaluations of polynomial time. Here n is the number of vertices, T ≤ nN is the number of nodes of the search tree whose bound does not exceed the optimum, c_max bounds the cost of a feasible pair, and Õ hides polylogarithmic factors. It uses polynomial space and no quantum random access memory.

This is a quantum advantage over the classical branch-and-bound search that it accelerates: that search explores the T nodes, and the quantum algorithm needs about √T of them, a quadratic speedup in the worst case up to factors polynomial in n.

**Theorem 5 (compact QUBO).** The routing problem has a QUBO with one variable per link of G − t₂ for P₁, one per link of G − t₁ for P₂, and one slack variable per path at each inner vertex of degree at least 3. A slack at such vertices is necessary, since no quadratic penalty in the link variables alone vanishes exactly at degrees 0 and 2 there. Any penalty weight

    A > c(E) + B · Σ_{e ≠ f, unordered} p(e, f)

is sufficient for every B ≥ 0 and every p ≥ 0: every minimizer is a feasible pair of minimum cost, together with stray cycles of latency zero that can be dropped, and none if all latencies are positive. If no feasible pair exists, the minimum exceeds the bound on the right. On the network of [1] with 5 vertices and 7 links this gives 12 or 13 qubits, depending on the source, against 24 in the formulation of [1].

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Theorem 1, Corollary 2 | Every rational C ≥ 0; uses the NP-hardness of the min-min disjoint paths problem [3], with the proof for undirected graphs in [4] (edge-disjoint paths; the vertex-disjoint version follows through the line graph) | Claim | 2026-11-16 |
| Theorem 3 | Exact for all inputs; N can be exponential in n, as Theorem 1 allows | Claim | 2026-11-16 |
| Theorem 4 | Uses the guarantee of [2] as stated there, for integer costs. The speedup is relative to classical branch-and-bound on the same tree, not a proven separation from every classical algorithm; it pays off only when T is large compared with the polynomial factors in n | Claim | 2026-11-16 |
| Theorem 5 | Every B ≥ 0 and p ≥ 0; minimizers checked by exhaustive search on the network of [1] for three sources, two failure scenarios and six values of B | Claim | 2026-11-16 |

## References

1. M. Harb, N. Foroughi, M. Stehman, B. Lutz, N. Erez, E. Garcell. Quantum-based resilient routing in networks: minimizing latency under dual-link failures. IEEE Transactions on Quantum Engineering 7, 2026. doi:10.1109/TQE.2026.3702858.
2. A. Montanaro. Quantum speedup of branch-and-bound algorithms. Physical Review Research 2, 013056, 2020. arXiv:1906.10375.
3. D. Xu, Y. Chen, Y. Xiong, C. Qiao, X. He. On the complexity of and algorithms for finding the shortest path with a disjoint counterpart. IEEE/ACM Transactions on Networking 14(1):147–158, 2006.
4. L. Guo, H. Shen. On finding min-min disjoint paths. Algorithmica 66(3):641–653, 2013.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the algorithms and proofs, and to draft the text.
