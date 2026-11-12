# 3-Hitting Set and d-Hitting Set with a quantum algorithm, parameterized by the solution size

Written 12 Nov 2026.

Input: a hypergraph G on n vertices whose hyperedges have at most d vertices, and an integer k. Question: is there a set of at most k vertices that meets every hyperedge? For d = 2 this is Vertex Cover.

**Theorem 1.** 3-Hitting Set has a quantum algorithm with bounded error, polynomial space and no quantum random access memory in time O(1.4287^k) · poly(n).

**Theorem 2.** For d = 4, 5 and 6, d-Hitting Set has a quantum algorithm of the same kind in time O(1.7439^k), O(2.0102^k) and O(2.2452^k), times poly(n).

Status: Claim. Theorem 1 of [2] is used as stated there, where its time recursion is in Lean. The conditions for the algorithm of [1] are argued here from its analysis, and the constants and the split step are checked by script.

## Before and after

| Problem | Previous best bound | After |
|---|---|---|
| 3-Hitting Set | 2.0409^k classically [1]; 1.4725^k quantum, implied by [3] on the plain search tree of [4] | **1.4287^k** |
| 4-Hitting Set | 3.0409^k classically [1], from [5], [6]; 1.7799^k quantum, implied by [3] on [4] with [5], [6] | **1.7439^k** |
| 5-Hitting Set | 4.0409^k classically [1], from [5], [6]; 2.0416^k quantum, implied as above | **2.0102^k** |
| 6-Hitting Set | 5.0409^k classically [1], from [5], [6]; 2.2734^k quantum, implied as above | **2.2452^k** |

All bounds hide polynomial factors in n. Each new base is the square root of the classical one, rounded up. To our knowledge no quantum bound for these problems parameterized by k has been stated before. A walk on the 2.0755^k algorithm of [7] would give 1.4407^k if its search tree is plain, and walks on the d-Hitting Set algorithms of [8], with bases 3.115, 4.08 and 5.049, would give 1.7650^k, 2.0199^k and 2.2470^k under the same condition. The new bounds are below all of these.

## 1. The tool

Theorem 1 of [2] turns a recursive decision procedure into a quantum algorithm in time √B(x) · poly(n), for a measure B with three conditions. (M1) bounds the sum of B over every antichain of the OR-tree by n^C B(x). (M2) asks that a value call y at a node v has log B(y) ≤ (3/4) log B(v) + C log n. (M3) bounds the size of the full call tree below x by n^C B(x). A plain walk [3] needs a search tree in which every node only branches. The algorithm of [1] is not of that kind, which is why [2] is used.

## 2. 3-Hitting Set: Theorem 1

The algorithm HS of [1] applies reduction rules (R1) to (R5) and branching rules (B1) to (B8). All of them except (B7) make one call or branch into several calls, so they are OR nodes. Rule (B7) applies when the maximum degree is at most 3 and G is disconnected. It takes a component H, finds the minimum size k′ of a hitting set of H by calls HS(H, i) for i = 4, 5, … , and then continues with HS(G − H, k − k′). Every component has optimum at least 4, since rule (R3) solves the others. So (B7) makes value calls on H followed by a tail call, and the value calls can have nearly the measure of their caller.

**The split step.** For k ≥ 10, replace (B7) as follows, with K = ⌊k/2⌋. Make value calls HS(H, i) for i = 4, … , K. If one succeeds at i = k′, make the tail call HS(G − H, k − k′). Otherwise make value calls HS(G − H, i) for i = 4, … , K, and if one succeeds at i = k″, make the tail call HS(H, k − k″). If neither succeeds, both optima exceed K, so their sum exceeds k, and the answer is no. For k < 10 keep (B7) as it is. The answer is the same as before, since both orders decide whether opt(H) + opt(G − H) ≤ k.

**Measure.** Let b = 2.0409 and B(G, k) = b^{μ(G, k) + 2d̂(G) + α(G, k)}, with μ, d̂ and α as in [1]. Here μ(G, k) = k − Ψ(…) with 0 ≤ Ψ ≤ 2 by Property (P1) of [1], d̂ is the maximum degree clipped to [3, 6], and α(G, k) is 0 if G is good in the sense of [1] and 3 otherwise, which is computable in polynomial time. In [1], α is 3 exactly when rule (B8) at maximum degree at most 3 occurs below the node. The form used here serves the same purpose: (B8) at maximum degree at most 3 is applied only to a hypergraph that is not good, its children are good [1, Lemmas 13 and 15], and goodness survives the deletion of vertices and hyperedges [1, Lemma 14], so also the passage to H or G − H. So α never grows from a node to a call it makes.

- **(M1) and (M3).** The proof of Lemma 30 of [1] bounds the measures of the children of each rule by the measure of the node. For (B6) and (B8) the branching vectors include the rule applied next in a child, so these are macro steps of constant size in the sense of Lemma 0 of [2], which gives (M1) with a constant factor. None of them passes through (B7). For the split step the calls go up to K and the tail has budget at most k − 4, since the other part has optimum at least 4. Its leaves therefore number at most 2 Σ_{i=4}^{K} b^{i+E} + b^{k−4+E}, with E = 2d̂(G) + α(G, k), and this is at most b^{k−2+E} ≤ B(G, k) for k ≥ 10. The tail alone has measure at most b^{k−4+E} ≤ B(G, k). Induction then gives (M1) for every antichain and bounds the number of leaves, and every node deletes a vertex or a hyperedge, so the depth is at most n + m and (M3) holds.
- **(M2).** A value call has budget at most K ≤ k/2, so its log measure is at most (k/2 + 15) log b, against at least (k − 2) log b for its caller. For k above a constant this is at most 3/4 of it. Below that constant the call has constant measure, which the term C log n covers. For k < 10 the value calls of (B7) have budget at most 9 and constant measure too.

Theorem 1 of [2] then gives √(2.0409^{k + O(1)}) · poly(n) = O(1.4287^k) · poly(n). A hitting set comes by self-reduction, fixing vertices one at a time into the solution, G[+v], or out of it.

## 3. d ≥ 4: Theorem 2

An algorithm for d-Hitting Set in time c^k gives one for (d + 1)-Hitting Set in time (c + 1)^k by iterative compression [5], [6]. The vertices are added one at a time, and a solution S of size k + 1 is compressed. For each subset X of S that stays in the solution, the hyperedges not met by X must be met outside S, and each of them keeps at most d vertices outside S. That is a d-Hitting Set instance with budget k − |X|. The quantum version searches over X by variable-time search with the quantum algorithm for d-Hitting Set inside, in time √(Σ_X c^{k−|X|}) · poly(n) = √((c + 1)^{k+1}) · poly(n), and it repeats this over the n rounds with error reduction. From c = 2.0409 this gives the bases √3.0409, √4.0409 and √5.0409. For d ≥ 7 the classical bases of [8] are smaller.

## 4. Measurements

`sim/bounds.py` checks the rounded bases in exact arithmetic, the implied bases of the table, and the inequality of the split step for 10 ≤ k < 400. It also compares the decision of the split step with opt(H) + opt(G − H) ≤ k on random pairs of 3-uniform hypergraphs, with optima by brute force. Run it with `python bounds.py` in `sim/`. It exits nonzero on a failed check, and the log is alongside.

## 5. Limits

- The rules of [1], their safeness and the lemmas of its analysis are used as stated. That the rules other than (B7) are OR nodes, and that Lemma 30 gives (M1) and (M3), is argued here from its text.
- The polynomial factor of Theorem 1 of [2] has a fixed but large exponent, and there is no gate count. The bounds say nothing about instances that fit on current devices.
- The algorithm and the analysis are not formalized beyond Theorem 1 of [2] itself.

## References

1. D. Tsur. Faster parameterized algorithm for 3-Hitting Set. arXiv:2501.06452.
2. Vertex Cover and Independent Set with a quantum algorithm, Theorem 1. [quantum-vertex-cover](../quantum-vertex-cover/).
3. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14, 2018. arXiv:1509.02374.
4. H. Shachnai, M. Zehavi. A multivariate approach for weighted FPT algorithms. ESA 2015. arXiv:1407.2033.
5. M. Dom, J. Guo, F. Hüffner, R. Niedermeier, A. Truß. Fixed-parameter tractability results for feedback set problems in tournaments. Journal of Discrete Algorithms 8(1), 2010.
6. F. V. Fomin, S. Gaspers, D. Kratsch, M. Liedloff, S. Saurabh. Iterative compression and exact algorithms. Theoretical Computer Science 411(7-9), 2010.
7. M. Wahlström. Algorithms, measures and upper bounds for satisfiability and related problems. PhD thesis, Linköping University, 2007.
8. H. Fernau. Parameterized algorithmics for d-hitting set. International Journal of Computer Mathematics 87(14), 2010.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation script, and to draft the text.
