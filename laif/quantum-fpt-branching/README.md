# Quantum algorithms for parameterized graph problems from classical search trees

Written 22 Nov 2026.

For a graph G and a budget k, Vertex Cover above LP asks for a vertex cover of size at most k, with the parameter μ = k − vc*(G), where vc*(G) is the optimum of the linear programming relaxation. Several problems reduce to it with μ bounded by their own parameter, and a quantum walk over its search tree then gives the bounds below.

**Theorem 1.** Odd Cycle Transversal, Above Guarantee Vertex Cover and Almost 2-SAT (clause and variable deletion) have quantum algorithms with bounded error, polynomial space and no quantum random access memory, in time O(1.5214^k) · poly(n). For Above Guarantee Vertex Cover, k is the excess of the minimum vertex cover over a maximum matching.

**Theorem 2.** Deletion to a graph whose vertex cover number equals its matching number (KVD), and Vertex Cover parameterized by the size k of a KVD set or of an odd cycle transversal, have quantum algorithms of the same kind in time O(1.2335^k) · poly(n).

**Theorem 3.** With k the solution size, quantum algorithms of the same kind solve Cluster Vertex Deletion in time O(1.3458^k) · poly(n), Edge Dominating Set in O(1.4951^k) · poly(n), and d-Path Vertex Cover (deletion of at most k vertices so that no path on d vertices remains) for d = 3, 4, 5, 6, 7 in O(1.3071^k), O(1.4624^k), O(1.6238^k), O(1.8261^k) and O(1.9899^k), times poly(n).

Status: Claim. For Odd Cycle Transversal the matching bound on the relaxation and the bound on μ are in Lean (`lean/FptBranching.lean`), and so are the bases; for the problems of Theorem 2 only the arithmetic of the budget step is. The search tree of [1] and the reductions of [1] and [4] are used as stated there (Assuming), and the walk is the direct application of [2] and [3]. For Theorem 3 the search trees of [5], [7] and [9] are used as stated there, with the changes of Section 3; the bounds of [9] are computer-assisted and are used as stated (Assuming). The bases are checked by script.

## Before and after

| Problem | Previous best bound | After |
|---|---|---|
| Odd Cycle Transversal | 2.3146^k classically [1]; 1.6181^k quantum, implied by [1, Theorem 1] with [3] | **1.5214^k** |
| Above Guarantee Vertex Cover | 2.3146^k classically [1]; 1.6181^k quantum, implied as above | **1.5214^k** |
| Almost 2-SAT | 2.3146^k classically [1]; 1.6181^k quantum, implied as above | **1.5214^k** |
| KVD | 1.5214^k classically [1]; 1.2721^k quantum, implied by [1, Theorem 1] with [3] | **1.2335^k** |
| Vertex Cover parameterized by a KVD set | 1.5214^k classically [1]; 1.2721^k quantum, implied as above | **1.2335^k** |
| Vertex Cover parameterized by an odd cycle transversal | 1.5214^k classically [1]; 1.2721^k quantum, implied as above | **1.2335^k** |
| Cluster Vertex Deletion | 1.811^k classically [5]; 1.3821^k quantum, implied by [6] with [3] | **1.3458^k** |
| Edge Dominating Set | 2.2351^k classically [7]; 1.5215^k quantum, implied by [8] with [3] | **1.4951^k** |
| 3-Path Vertex Cover | 1.708^k classically [9]; 1.3089^k quantum, implied by [10] with [3] | **1.3071^k** |
| 4-Path Vertex Cover | 2.138^k classically [9]; 1.6184^k quantum, implied by [11] with [3] | **1.4624^k** |
| 5-, 6-, 7-Path Vertex Cover | 2.636^k, 3.334^k, 3.959^k classically [9]; 1.9863^k, 2.2242^k, 2.4395^k quantum, implied by [12] with [3] | **1.6238^k, 1.8261^k, 1.9899^k** |

All bounds hide polynomial factors in n. The new bases are √2.3146 and 2.3146^{1/4}, rounded up. The implied quantum bases come from a walk on the simpler search tree of [1, Theorem 1], of size 2.6181^μ, through the same reductions. Each bound of Theorem 3 is a direct application of [3] to the newest search tree, and the implied bases apply [3] in the same way to the earlier trees named in the table. For d-Path Vertex Cover the bases of [9], printed with three decimals, are raised by 0.0005 before the square root. The walk on the tree of [5] also serves as the oracle of the quantum monotone local search of [14], with bounds in n. To our knowledge no quantum bound for these problems parameterized by k has been stated before.

## 1. The tool

The algorithm of [1, Theorem 2] decides Vertex Cover above LP with a search tree of size 2.3146^μ · poly(n). Its rules apply polynomial-time preprocessing at a node and then branch. The worst branching vectors are (1, 3/2, 3/2) for rule B5 and (3/2, 3/2, 5/2, 5/2, 2) for rule B6, both with root 2.31460 in μ. The algorithm of [1] treats connected components separately and solves components of at most 10 vertices exactly. Here the budget stays global, as in [2, Section 5]: μ is additive over components, so branching inside one component gives the same drops of μ, and solving a small component exactly at a node and removing it lowers the budget by its vertex cover number and the relaxation by at most that, so μ does not grow. Rule B6 applies only when every component is 3-regular with surplus 2, so the whole graph being irreducible gives the same for the component of the branching vertex, which is what Lemmas 16 and 17 of [1] use. Every node therefore does polynomial work and branches, and the tree is plain. The walk on backtracking trees of [3] then decides it in time √(2.3146^μ) · poly(n) = O(1.5214^μ) · poly(n), with bounded error and polynomial space. A solution comes by self-reduction.

## 2. The reductions

- **Odd Cycle Transversal.** The construction of [1, Section 5.2] takes two copies of the vertex set, puts a copy of G on each, and joins the copies of each vertex by an edge. G has an odd cycle transversal of size at most k exactly when this graph H has a vertex cover of size at most n + k [1, Lemma 20]. The n joining edges form a perfect matching of H, so every fractional vertex cover of H has weight at least n (`matching_le_fractional`), and the excess at budget n + k is at most k (`transversal_excess`).
- **Above Guarantee Vertex Cover.** The relaxation is at least the size of a maximum matching, so μ is at most the excess over the matching [1, Theorem 3].
- **Almost 2-SAT.** Both versions reduce to Above Guarantee Vertex Cover [1, Corollary 2]. As instances of BIP2 they also reduce in linear time to Vertex Cover above LP with the same gap above the relaxation, which is at most k [4, Theorem 1 and Example 3].
- **Vertex Cover parameterized by a KVD set.** The preprocessing in the proof of [1, Theorem 5] (Lemma 1 there) leaves a graph G′ and a budget ℓ′, and G′ has a KVD set O of size at most k [1, Lemma 22]. Then vc(G′) − vc*(G′) ≤ |O|/2 ≤ k/2 (`kvd_excess`, from the two inequalities in the proof there). If ℓ′ ≥ vc*(G′) + k/2 the answer is yes at once, and otherwise the excess ℓ′ − vc*(G′) is below k/2 (`kvd_budget`). The walk then costs O(1.5214^{k/2}) = O(1.2335^k), times poly(n) (`half_cost`).
- **Vertex Cover parameterized by an odd cycle transversal.** An odd cycle transversal is a KVD set [1, Corollary 5].
- **KVD.** If G has a KVD set of size at most k, then vc(G) − vc*(G) = vc(G′) − vc*(G′) ≤ k/2 on the preprocessed graph G′ [1, Lemmas 2 and 22]. The walk tries the budgets from ⌈vc*(G′)⌉ up to vc*(G′) + k/2 on G′, and if none of them succeeds the answer is no. Otherwise a minimum vertex cover comes by self-reduction, which does not raise the excess, at a polynomial factor, and it gives a minimum KVD set in polynomial time [1, Corollary 4].

## 3. Search trees for Theorem 3

Each algorithm below is a search tree whose nodes do polynomial work and then stop or branch with a smaller budget, so the walk of [3] gives the square root of its size, and a solution comes by self-reduction.

- **Cluster Vertex Deletion [5].** The reduction rules are polynomial, the components of maximum degree 2 are solved in closed form, and the families of hitting sets that the algorithm branches over are themselves produced by a branching procedure. The analysis of [5] bounds the leaves of the combined tree, with every dead end of the inner procedure counted, so the inner steps are nodes of one tree. The same argument is given in [14] for this tree. The tree of [6] is plain as well.
- **Edge Dominating Set [7, Theorem 1].** The tree branches on vertices, 4-cycles and bad components, and a leaf with only clique components is solved in polynomial time [7, Lemma 2]. The analysis bounds the number of leaves. Its third stage is written as an enumeration of assignments of the bad components subject to two counting conditions. As a tree that assigns one component per level and prunes a node when the conditions fail even with the cheapest branch for every remaining component, it has the same leaves and at most polynomially more nodes, since the cheapest branch of each component type minimizes both counted quantities. The tree of [8] has the same final stage, over its 2-path components, and is restated in the same way.
- **d-Path Vertex Cover [9].** The generated algorithm (Algorithm 1 and Theorem 1 of [9]) applies two polynomial reduction rules, each followed by one call, solves the instance by brute force when every component has fewer than a constant number of vertices, and otherwise branches on a rule applied to one component with the global budget. Its bounds are those of Table 1 of [9]. The earlier trees of [10] and [12] are plain in the same sense, and the algorithm of [11] uses iterative compression, where each round is one plain tree.

## 4. Lean

`lean/FptBranching.lean` proves, with only the standard axioms (`lean/axioms.txt`):

- `matching_le_fractional`: a matching of size m, given by 2m distinct endpoints, forces every nonnegative fractional vertex cover to have weight at least m.
- `transversal_excess`, `transversal_cost`: the excess of the transversal reduction is at most k, and a cost C · 1.5214^μ is then at most C · 1.5214^k.
- `kvd_excess`, `kvd_budget`, `half_excess_base`, `half_cost`: the arithmetic of the budget step, and an excess of at most k/2 gives C · 1.2335^k.
- `walk_base_k`, `walk_base_half`, `base_half_sq`: 2.3146 < 1.5214², 2.3146 < 1.2335⁴ and 1.5214 ≤ 1.2335².

Lean 4 v4.36.0-rc1 with Mathlib at revision d875a8de5222f62cf1c2fafc7984588adadc990a. Run `lake exe cache get` and then `lake build` in `lean/`.

Not formalized: the search tree of [1], the walk of [3], the reductions of [1] and [4], and for the problems of Theorem 2 the two inequalities vc(G′) ≤ |M| + |O| and vc*(G′) ≥ |M| + |O|/2 and Lemma 22 of [1].

## 5. Measurements

`sim/bases.py` recomputes the root 2.314596 of the vectors of rules B5 and B6 of [1], checks the printed bases in exact arithmetic on the recurrence of the walk, and recomputes the implied bases from the root φ² of the tree of [1, Theorem 1]. Run it with `python bases.py` in `sim/`. It exits nonzero on a failed check. `sim/bases2.py` checks the bases of Theorem 3 and of the implied baselines in exact arithmetic, each the square root of the classical base rounded up at the fourth decimal, and checks that the bases for d = 3 to 6 lie below the quantum bounds for d-Hitting Set of [13].

## 6. Limits

- The search tree of [1], the safeness of its rules and its analysis are used as stated, as are its reductions and those of [4]. The same holds for the trees of [5] to [12]; their case analyses are used as stated.
- The polynomial factor of the walk is not given explicitly, and there is no gate count.

## References

1. D. Lokshtanov, N. S. Narayanaswamy, V. Raman, M. S. Ramanujan, S. Saurabh. Faster parameterized algorithms using linear programming. ACM Transactions on Algorithms, 2014. arXiv:1203.0833.
2. Vertex Cover and Independent Set with a quantum algorithm. [quantum-vertex-cover](../quantum-vertex-cover/).
3. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14, 2018. arXiv:1509.02374.
4. Y. Iwata, K. Oka, Y. Yoshida. Linear-time FPT algorithms via network flow. SODA 2014. arXiv:1307.4927.
5. D. Tsur. Faster parameterized algorithm for Cluster Vertex Deletion. arXiv:1901.07609.
6. A. Boral, M. Cygan, T. Kociumaka, M. Pilipczuk. Fast branching algorithm for Cluster Vertex Deletion. arXiv:1306.3877.
7. K. Iwaide, H. Nagamochi. An improved algorithm for parameterized edge dominating set problem. Journal of Graph Algorithms and Applications 20(1), 2016.
8. M. Xiao, T. Kloks, S.-H. Poon. New parameterized algorithms for edge dominating set. arXiv:1104.4160.
9. R. Červený, O. Suchý. Generating faster algorithms for d-Path Vertex Cover. arXiv:2111.05896.
10. D. Tsur. Parameterized algorithm for 3-path vertex cover. arXiv:1809.02636.
11. D. Tsur. An O*(2.619^k) algorithm for 4-path vertex cover. arXiv:1811.03592.
12. D. Tsur. l-path vertex cover is easier than l-hitting set for small l. arXiv:1906.10523.
13. 3-Hitting Set and d-Hitting Set with a quantum algorithm. [quantum-hitting-set](../quantum-hitting-set/).
14. Quantum monotone local search. [quantum-monotone-local-search](../quantum-monotone-local-search/).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean files, and to draft the text.
