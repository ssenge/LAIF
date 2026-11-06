# Exact weighted diameter and radius of planar networks in Quantum CONGEST

Written 6 Nov 2026.

## Result

Network: an undirected planar graph G with n nodes, hop-diameter D and integer edge weights in {0, ..., W}, with a polynomial bound on W known to all nodes, in the Quantum CONGEST model (messages of O(log n) qubits per edge and round). Task: the exact weighted diameter or radius.

**Theorem 1.** There is a Quantum CONGEST algorithm that computes the weighted diameter of G exactly in Õ(D² + √n · D) rounds with probability at least 2/3. The same algorithm with minimum in place of maximum computes the weighted radius.

**Theorem 2.** Let 3 ≤ D ≤ n/2 for the diameter and 5 ≤ D ≤ n/2 for the radius. Every Quantum CONGEST algorithm that computes, with probability at least 2/3, the weighted diameter, or the weighted radius, of n-node planar networks with hop-diameter D takes Ω(√n / log n) rounds.

**Theorem 3.** Every classical CONGEST algorithm that computes the weighted radius of n-node planar networks with hop-diameter D, for 5 ≤ D ≤ n/2, with probability at least 2/3 takes Ω(n / log n) rounds. For the diameter this is [3, Theorem 9] with D = 3 in its proof, and the padding below extends it to 3 ≤ D ≤ n/2.

| | Rounds |
|---|---|
| Previous best bound, quantum | Õ(n), the classical bound via exact all-pairs shortest paths [1]; a (1 + o(1))-approximation in Õ(min(n^{9/10} D^{3/10}, n)) on general networks [2] |
| Classical, planar | Ω(n / log n): diameter for D = 3 [3] and, with padding, 3 ≤ D ≤ n/2; radius for 5 ≤ D ≤ n/2 (Theorem 3); Õ(n) [1] |
| This folder | Õ(D² + √n · D), and Ω(√n / log n) for 3 ≤ D ≤ n/2 (diameter) and 5 ≤ D ≤ n/2 (radius) |

For D = polylog(n) the quantum complexity of both problems is Θ̃(√n), against Θ̃(n) classically. On general networks with D = Θ(log n), even a (3/2 − ε)-approximation takes Ω̃(n^{2/3}) quantum rounds [2], so planarity lowers the quantum complexity of the exact problem below that bound.

## The argument

**Upper bound.** Elect a leader, build a BFS tree and rename the nodes 1, ..., n along it, in Õ(D) rounds. Then compute, once and classically, the exact distance labels of [4, Lemmas 5.1 and 5.2]: labels of Õ(D) bits such that d(u, v) is a function of the labels of u and v, in Õ(D²) rounds with high probability. From then on everything is deterministic. The diameter is the maximum of ecc(s) over the n sources, found by the distributed quantum optimization of [5, Theorem 7] (over 2^⌈log n⌉ elements, with value −1 on the extra ones) with O(√n) calls to an evaluation of ecc(s).

The evaluation acts on a superposition of sources and runs reversibly in Õ(D) rounds:
1. The leader sends s down the tree.
2. The label of s goes up the tree as a pipelined XOR, which works because only node s contributes a nonzero string, and then back down to all nodes.
3. Every node computes d(s, v) from the two labels, and the maximum goes up the tree to the leader, which copies it.
4. Everything is undone in reverse order.

This gives Õ(D²) + O(√n) · Õ(D) = Õ(D² + √n · D) rounds.

More generally, any randomized exact single-source shortest path algorithm of T rounds with failure probability n^{−2} gives Õ(√n · (T + D)). Each node fixes its random bits once, before the search, and a union bound over the n sources makes one choice correct for all of them. The directed algorithm of [exact-shortest-paths-and-flows-on-planar-graphs](../exact-shortest-paths-and-flows-on-planar-graphs/) (Theorem A, Õ(D) rounds with the rotation lists as input, under the cited results listed there) would give Õ(√n · D) for directed networks.

**Lower bound.** The network in the proof of [3, Theorem 9] encodes two strings A, B ∈ {0,1}^k with 2k + 4 nodes. Alice holds nodes a_1, ..., a_k and hubs l, r; Bob holds b_1, ..., b_k and hubs l', r'. Every a_i is joined to l and r, every b_j to l' and r', and the cut between the two sides consists of the edges ll' and rr', each of weight 4. With α = A[i] and β = B[j], the weights are

    w(a_i, l) = 4i + α,  w(a_i, r) = 4(k + 1 − i) + α,  w(b_j, l') = 4(k + 1 − j) + β,  w(b_j, r') = 4j + β.

The network is planar with hop-diameter 3. The pair a_i, b_i is at distance 4(k + 2) + A[i] + B[i]. The hub pairs l, r' and r, l' are at distance between 4(k + 2) and 4(k + 2) + 2·min(A[1], B[1]), and every other pair at distance at most 4(k + 1) + 2. So the diameter is 4(k + 2) + 2 if A and B intersect, and at most 4(k + 2) + 1 otherwise.

**Radius network.** Take the same graph with weight 5 in place of 4 (so w(a_i, l) = 5i + α and so on), the bits α = 1 − A[i] and β = 1 − B[j], and a leaf of weight 3 at each of the four hubs. The network is planar with hop-diameter 5. As before, a_i and b_i are at distance 5(k + 2) + α + β, and every other pair of coordinate nodes at distance at most 5(k + 1) + 2. A coordinate node is at distance at most 5(k + 1) + 1 from each hub, hence less than 5(k + 2) from each leaf, so ecc(a_i) = ecc(b_i) = 5(k + 2) + (1 − A[i]) + (1 − B[i]). Every path from l to r' passes through some b_j or some a_i and weighs at least 5(k + 2), so with the leaf at r' the eccentricity of l is at least 5(k + 2) + 3; the other hubs and the leaves are the same. The radius is therefore 5(k + 2) if A and B intersect, and at least 5(k + 2) + 1 otherwise.

**Padding.** A path of t new nodes with weight-0 edges at hub l, plus optionally one more node for parity, raises the hop-diameter to t + 3 (diameter network) and max(5, t + 4) (radius network). Every new node is at the same distance as l from all old nodes, so the diameter and the radius do not change. For t = 0, the parity node is joined to l with weight 0 and to r with weight 4(k + 1) + 2. Weight-0 edges can be avoided by multiplying all weights by n and giving the new edges weight 1.

**Simulation.** For either network, an algorithm of T rounds gives a two-party protocol in which Alice and Bob simulate their own nodes and exchange the O(log n) qubits sent over the two cut edges in each round, as in [5, Theorem 10]. The protocol decides disjointness of k-bit strings with O(T log n) qubits of communication. Quantum disjointness needs Ω(√k) qubits [6], and k ≥ n/4 − 3 for D ≤ n/2, so T = Ω(√k / log n) = Ω(√n / log n). A classical algorithm gives a protocol with O(T log n) bits, and classical disjointness needs Ω(k) bits [7], which gives Theorem 3.

## Machine check

`lean/PlanarDiameterQ.lean` checks the path weights of both lower-bound networks (with k written n), with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- `cross_same`: both paths between a_i and b_i weigh 4(k + 2) + A[i] + B[i].
- `cross_diff`, `same_side`, `to_hub`, `hubs`, `hubs_bounds`: the other pairs are at distance at most 4(k + 1) + 2; every path between the hub pairs l, r' and r, l' weighs at least 4(k + 2), and the named paths at most 4(k + 2) + 2, and at most 4(k + 2) unless A[1] = B[1] = 1.
- `through_node`: a path through a further coordinate node, which has degree two, weighs more than 4(k + 2) + 2.
- `gap`: the diameter reaches 4(k + 2) + 2 exactly when some A[i] = B[i] = 1.
- `rad_cross_same`, `rad_other_pairs`, `rad_to_leaf`, `rad_through_node`: the eccentricities 5(k + 2) + α + β of the coordinate nodes in the radius network.
- `rad_hub`, `rad_hub_leaf`, `rad_gap`: every path from l to r' weighs at least 5(k + 2), so a hub's eccentricity, with its leaf, exceeds every coordinate eccentricity; the radius is 5(k + 2) exactly when some A[i] = B[i] = 1.

`gadget_check.py` computes all eccentricities of both networks by Dijkstra's algorithm for all inputs with k ≤ 6 and for 200 random inputs with k ≤ 40. It checks the claimed diameter, the radius formula 5(k + 2) + min_i((1 − A[i]) + (1 − B[i])) and the eccentricities. The same checks run on the padded networks with 0 ≤ t ≤ 7, with and without the parity node, for k ≤ 4. With networkx installed it also checks planarity, the hop-diameters and the two cut edges, for k ≤ 40 without padding and k ≤ 5 with padding.

**Not machine-checked:** the graph part of the distance analysis (which paths need to be considered), the padding argument, the distance labels [4], distributed quantum optimization and its implementation [5], the simulation argument, and the disjointness lower bounds [6, 7].

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
