# Exact weighted diameter and radius of planar networks in Quantum CONGEST

Written 6 Nov 2026.

## Result

Network: an undirected planar graph G with n nodes, hop-diameter D and integer edge weights polynomial in n, in the Quantum CONGEST model (messages of O(log n) qubits per edge and round). Task: the exact weighted diameter or radius.

**Theorem 1.** There is a Quantum CONGEST algorithm that computes the weighted diameter of G exactly in Õ(√n · D²) rounds with probability at least 2/3. The same algorithm with minimum in place of maximum computes the weighted radius.

**Theorem 2.** Every Quantum CONGEST algorithm that computes, with probability at least 2/3, the weighted diameter of planar networks with hop-diameter 3, or the weighted radius of planar networks with hop-diameter 5, takes Ω(√n / log n) rounds.

**Theorem 3.** Every classical CONGEST algorithm that computes the weighted radius of planar networks with hop-diameter 5 with probability at least 2/3 takes Ω(n / log n) rounds. For the diameter this is [3, Theorem 9].

| | Rounds |
|---|---|
| Previous best bound, quantum | Õ(n), the classical bound via exact all-pairs shortest paths [1]; a (1 + o(1))-approximation in Õ(min(n^{9/10} D^{3/10}, n)) on general networks [2] |
| Classical, planar | Ω(n / log n) for D = 3 [3] (diameter) and for D = 5 (radius, Theorem 3); Õ(n) [1] |
| This folder | Õ(√n · D²), and Ω(√n / log n) for D = 3 (diameter) and D = 5 (radius) |

For D = polylog(n) the quantum complexity of both problems is Θ̃(√n), against Θ̃(n) classically. On general networks with D = Θ(log n), even a (3/2 − ε)-approximation takes Ω̃(n^{2/3}) quantum rounds [2], so planarity lowers the quantum complexity of the exact problem below that bound.

## The argument

**Upper bound.** Elect a leader, build a BFS tree and rename the nodes 1, ..., n along it, in O(D) rounds. The eccentricity ecc(s) of a source s is computed by an exact single-source shortest path tree from s, in Õ(D²) rounds with high probability [4, Theorem 1.6], followed by a maximum over the BFS tree in O(D) rounds. The diameter is the maximum of ecc(s) over the n sources, found by the distributed quantum optimization of [5, Theorem 7] with O(√n) calls to this evaluation, in Õ(√n · D²) rounds.

The evaluation has to act on a superposition of sources. Before the search, every node fixes its random bits once. With failure probability at most n^{−2} per source, a union bound shows that with probability at least 1 − 1/n the fixed bits give correct distances for all n sources at once. Given those bits, the evaluation is a deterministic CONGEST procedure of fixed length: the leader sends s down the tree, every node runs its part reversibly while keeping its messages, the maximum is copied to the leader, and the run is reversed. This costs O(T + D) rounds for an SSSP procedure of T rounds.

With the directed SSSP algorithm of [exact-shortest-paths-and-flows-on-planar-graphs](../exact-shortest-paths-and-flows-on-planar-graphs/) (Theorem A, Õ(D) rounds with the rotation lists as input), the same argument gives Õ(√n · D) rounds, also for directed networks.

**Lower bound.** The network of [3, Theorem 9] encodes two strings A, B ∈ {0,1}^k with 2k + 4 nodes. Alice holds nodes a_1, ..., a_k and hubs l, r; Bob holds b_1, ..., b_k and hubs l', r'. Every a_i is joined to l and r, every b_j to l' and r', and the cut between the two sides consists of the edges ll' and rr', each of weight 4. With α = A[i] and β = B[j], the weights are

    w(a_i, l) = 4i + α,  w(a_i, r) = 4(k + 1 − i) + α,  w(b_j, l') = 4(k + 1 − j) + β,  w(b_j, r') = 4j + β.

The network is planar with hop-diameter 3. The pair a_i, b_i is at distance 4(k + 2) + A[i] + B[i]. The hub pairs l, r' and r, l' are at distance at most 4(k + 2) + 2·min(A[1], B[1]), and every other pair at distance at most 4(k + 1) + 2. So the diameter is 4(k + 2) + 2 if A and B intersect, and at most 4(k + 2) + 1 otherwise.

**Radius network.** Take the same graph with weight 5 in place of 4 (so w(a_i, l) = 5i + α and so on), the bits α = 1 − A[i] and β = 1 − B[j], and a leaf of weight 3 at each of the four hubs. The network is planar with hop-diameter 5. As before, a_i and b_i are at distance 5(k + 2) + α + β, and every other pair of coordinate nodes at distance at most 5(k + 1) + 2. A coordinate node is at distance at most 5(k + 1) + 1 from each hub, hence less than 5(k + 2) from each leaf, so ecc(a_i) = ecc(b_i) = 5(k + 2) + (1 − A[i]) + (1 − B[i]). Every path from l to r' passes through some b_j or some a_i and weighs at least 5(k + 2), so with the leaf at r' the eccentricity of l is at least 5(k + 2) + 3; the other hubs and the leaves are the same. The radius is therefore 5(k + 2) if A and B intersect, and at least 5(k + 2) + 1 otherwise.

**Simulation.** For either network, an algorithm of T rounds gives a two-party protocol in which Alice and Bob simulate their own nodes and exchange the O(log n) qubits sent over the two cut edges in each round, as in [5, Theorem 10]. The protocol decides disjointness of k-bit strings with O(T log n) qubits of communication. Quantum disjointness needs Ω(√k) qubits [6], so T = Ω(√k / log n) = Ω(√n / log n). A classical algorithm gives a protocol with O(T log n) bits, and classical disjointness needs Ω(k) bits [7], which gives Theorem 3.

## Machine check

`lean/PlanarDiameterQ.lean` checks the path weights of both lower-bound networks (with k written n), with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- `cross_same`: both paths between a_i and b_i weigh 4(k + 2) + A[i] + B[i].
- `cross_diff`, `same_side`, `to_hub`, `hubs`: the other pairs are at distance at most 4(k + 1) + 2, and the hub pairs l, r' and r, l' at most 4(k + 2) unless A[1] = B[1] = 1.
- `through_node`: a path through a further coordinate node, which has degree two, weighs more than 4(k + 2) + 2.
- `gap`: the diameter reaches 4(k + 2) + 2 exactly when some A[i] = B[i] = 1.
- `rad_cross_same`, `rad_other_pairs`, `rad_to_leaf`, `rad_through_node`: the eccentricities 5(k + 2) + α + β of the coordinate nodes in the radius network.
- `rad_hub`, `rad_gap`: every path from l to r' weighs at least 5(k + 2), and the radius is 5(k + 2) exactly when some A[i] = B[i] = 1.

`gadget_check.py` computes all eccentricities of both networks by Dijkstra's algorithm for all inputs with k ≤ 6 and for 200 random inputs with k ≤ 40, and checks the claimed diameter, radius and eccentricities. With networkx installed it also checks planarity, the hop-diameters 3 and 5 and the two cut edges for k ≤ 40.

**Not machine-checked:** the exact SSSP algorithm [4], distributed quantum optimization and its implementation [5], the simulation argument, and the disjointness lower bounds [6, 7].

## References

[1] A. Bernstein, D. Nanongkai. Distributed exact weighted all-pairs shortest paths in near-linear time. STOC 2019. arXiv:1811.03337.

[2] X. Wu, P. Yao. Quantum complexity of weighted diameter and radius in CONGEST networks. PODC 2022. arXiv:2206.02767.

[3] A. Abboud, V. Cohen-Addad, P. N. Klein. New hardness results for planar graph problems in P and an algorithm for sparsest cut. STOC 2020. arXiv:2007.02377.

[4] J. Li, M. Parter. Planar diameter via metric compression. STOC 2019. arXiv:1912.11491.

[5] F. Le Gall, F. Magniez. Sublinear-time quantum computation of the diameter in CONGEST networks. PODC 2018. arXiv:1804.02917.

[6] A. A. Razborov. Quantum communication complexity of symmetric predicates. Izvestiya: Mathematics 67(1), 2003. arXiv:quant-ph/0204025.

[7] A. A. Razborov. On the distributional complexity of disjointness. Theoretical Computer Science 106(2), 1992.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean formalization, and to draft the text.
