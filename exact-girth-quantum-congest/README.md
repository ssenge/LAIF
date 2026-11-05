# Exact girth in Quantum CONGEST

Written 5 Nov 2026.

## Result

Network: an undirected graph G with n nodes, girth g and diameter D, in the Quantum CONGEST model (messages of O(log n) qubits per edge and round).

**Theorem.** There is a Quantum CONGEST algorithm that computes the girth exactly, with every node learning it (or learning that G has no cycle), in Õ(√n + D) rounds with probability at least 2/3. For a given bound k, an algorithm that finds the girth when g ≤ k, and otherwise reports that it is larger, takes Õ(k + √n) rounds, with the girth as the minimum of the node outputs.

| | Rounds |
|---|---|
| Previous best bound, quantum | Õ(g + (gn)^{1/2 − 1/Θ(g)}), and Õ(k + (kn)^{1/2 − 1/Θ(k)}) for the bounded version [1]; Õ(n^{1/2 − 1/(2k)}) for detecting cycles of length at most 2k, k constant [2] |
| Classical | O(n) [3]; Õ(min(g n^{1 − 1/Θ(g)}, n)) [4]; O(n/h + D) with the promise g ≥ h [5] |
| This folder | Õ(√n + D), and Õ(k + √n) for the bounded version |

For g ≥ log n, the bound of [1] is of order √(gn), so the gain is a factor of order √g in the bounded version and when D = O(g). Since D ≥ ⌊g/2⌋, the theorem also gives Õ(√n + D) = Õ(D) once g ≥ √n. For small g, the bounds of [1] and [2] stay smaller.

## The argument

**Value of a source [6].** Run BFS from a source s to depth h = ⌈k/2⌉ + 1 and let val(s) be the minimum of d(u) + d(v) + 1 over edges uv not in the BFS tree with both ends reached. The tree paths from s to u and to v split at a common ancestor and close a cycle of length at most val(s), so val(s) ≥ g for every s. If s lies on a shortest cycle C and g ≤ k, then C has an edge outside the tree, and with its ends at positions i and i + 1 of C (s at position 0), d(u) + d(v) + 1 ≤ min(i, g − i) + min(i + 1, g − i − 1) + 1 ≤ g, with both depths at most ⌊g/2⌋ ≤ h. So val(s) = g for all g vertices of C.

**Search with parallel queries.** Fix a round with bound k, assuming no cycle of length at most k/2. The clustering of [7, Theorem 17], with separation 4k + 2, gives clusters of diameter O(k log n) in O(log n) colours. For each colour in turn, every cluster X runs minimum finding over the sources in its k-neighbourhood X^{+k}. All BFS runs stay inside X^{+2k}, so clusters of one colour do not interfere. A shortest cycle that meets X lies in X^{+k}, so at least g > k/2 of the at most n sources reach the minimum. The parallel minimum finding of [1, Lemma 3 and Corollary 9] with p = k queries per batch uses O(√(n/(gp))) = O(√n/k) batches. One batch costs O(k log n) rounds: distributing the queries in the cluster, depth-h distances from p sources in O(p + h) rounds [8], one exchange of p distances and parents with the neighbours, and the minimum over the cluster. So a round costs Õ(k + √n).

**Doubling.** Run the rounds for k = 3, 6, 12, ... with the error of each round reduced to O(1/log n). The values are never below g, so the first round that finds a cycle returns g. That round has k < 2g, and the total is Õ(g + √n) for the minimum of the node outputs. Broadcasting the minimum after each round adds O(D) per round. Since a graph with a cycle has one of length at most 2D + 1, the algorithm stops after the round with k > 2D + 1, with D estimated in O(D) rounds. This gives Õ(√n + D) with global output.

## Machine check

`lean/GirthQuantum.lean` checks the counting steps, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- `edge_on_cycle`, `cdist_le_half`: an edge of the cycle at positions i and i + 1 closes a walk of length at most g, with both ends at cycle distance at most ⌊g/2⌋ from s.
- `round_cost`: √(n/((k/2)·k)) batches of K·k rounds cost √(2n)·K, for every k.

**Not machine-checked:** the BFS argument of [6], the clustering [7], parallel minimum finding and its Quantum CONGEST implementation [1], and source detection [8].

## References

[1] J. van Apeldoorn, T. de Vos. A framework for distributed quantum queries in the CONGEST model. PODC 2022. arXiv:2202.10969.

[2] P. Fraigniaud, M. Luce, F. Magniez, I. Todinca. Even-cycle detection in the randomized and quantum CONGEST model. PODC 2024. arXiv:2402.12018.

[3] S. Holzer, R. Wattenhofer. Optimal distributed all pairs shortest paths and applications. PODC 2012.

[4] K. Censor-Hillel, O. Fischer, T. Gonen, F. Le Gall, D. Leitersdorf, R. Oshman. Fast distributed algorithms for girth, cycles and small subgraphs. DISC 2020. arXiv:2101.07590.

[5] I. Chebolu, A. Mallick, C. A. S. Murty, S. Pangal, B. S. Rajpurohit, H. Rana. Adaptive black-box exactness barriers for nearest-source girth estimation in CONGEST. arXiv:2608.17358, 2026.

[6] A. Itai, M. Rodeh. Finding a minimum circuit in a graph. SIAM J. Comput. 7(4), 1978.

[7] T. Eden, N. Fiat, O. Fischer, F. Kuhn, R. Oshman. Sublinear-time distributed algorithms for detecting small cliques and even cycles. Distributed Computing, 2021.

[8] C. Lenzen, B. Patt-Shamir, D. Peleg. Distributed distance computation and routing with small messages. Distributed Computing 32, 2019.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean formalization, and to draft the text.
