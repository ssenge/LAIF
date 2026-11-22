# Quantum algorithms for problems that reduce to Vertex Cover above LP, parameterized by the solution size

Written 22 Nov 2026.

For a graph G and a budget k, Vertex Cover above LP asks for a vertex cover of size at most k, with the parameter μ = k − vc*(G), where vc*(G) is the optimum of the linear programming relaxation. Several problems reduce to it with μ bounded by their own parameter, and a quantum walk over its search tree then gives the bounds below.

**Theorem 1.** Odd Cycle Transversal, Above Guarantee Vertex Cover and Almost 2-SAT (clause and variable deletion) have quantum algorithms with bounded error, polynomial space and no quantum random access memory, in time O(1.5214^k) · poly(n). For Above Guarantee Vertex Cover, k is the excess of the minimum vertex cover over a maximum matching.

**Theorem 2.** Deletion to a graph whose vertex cover number equals its matching number (KVD), and Vertex Cover parameterized by the size k of a KVD set or of an odd cycle transversal, have quantum algorithms of the same kind in time O(1.2335^k) · poly(n).

Status: Claim. The search tree of [1] and the reductions of [1] and [4] are used as stated there (Assuming), and the walk is the direct application of [2] and [3]. The excess bounds and the bases are checked by script.

## Before and after

| Problem | Previous best bound | After |
|---|---|---|
| Odd Cycle Transversal | 2.3146^k classically [1]; 1.6181^k quantum, implied by [1, Theorem 1] with [3] | **1.5214^k** |
| Above Guarantee Vertex Cover | 2.3146^k classically [1]; 1.6181^k quantum, implied as above | **1.5214^k** |
| Almost 2-SAT | 2.3146^k classically [1]; 1.6181^k quantum, implied as above | **1.5214^k** |
| KVD | 1.5214^k classically [1]; 1.2721^k quantum, implied by [1, Theorem 1] with [3] | **1.2335^k** |
| Vertex Cover parameterized by a KVD set | 1.5214^k classically [1]; 1.2721^k quantum, implied as above | **1.2335^k** |
| Vertex Cover parameterized by an odd cycle transversal | 1.5214^k classically [1]; 1.2721^k quantum, implied as above | **1.2335^k** |

All bounds hide polynomial factors in n. The new bases are √2.3146 and 2.3146^{1/4}, rounded up. The implied quantum bases come from a walk on the simpler search tree of [1, Theorem 1], of size 2.6181^μ, through the same reductions. To our knowledge no quantum bound for these problems parameterized by k has been stated before.

## 1. The tool

The algorithm of [1, Theorem 2] decides Vertex Cover above LP with a search tree of size 2.3146^μ · poly(n). Its rules apply polynomial-time preprocessing at a node and then branch. The worst branching vectors are (1, 3/2, 3/2) for rule B5 and (3/2, 3/2, 5/2, 5/2, 2) for rule B6, both with root 2.31460 in μ. The algorithm of [1] treats connected components separately and solves components of at most 10 vertices exactly. Here the budget stays global, as in [2, Section 5]: μ is additive over components, so branching inside one component gives the same drops of μ, and solving a small component exactly at a node and removing it lowers the budget by its vertex cover number and the relaxation by at most that, so μ does not grow. Rule B6 applies only when every component is 3-regular with surplus 2, so the whole graph being irreducible gives the same for the component of the branching vertex, which is what Lemmas 16 and 17 of [1] use. Every node therefore does polynomial work and branches, and the tree is plain. The walk on backtracking trees of [3] then decides it in time √(2.3146^μ) · poly(n) = O(1.5214^μ) · poly(n), with bounded error and polynomial space. A solution comes by self-reduction.

## 2. The reductions

- **Odd Cycle Transversal.** The construction of [1, Section 5.2] takes two copies of the vertex set, puts a copy of G on each, and joins the copies of each vertex by an edge. G has an odd cycle transversal of size at most k exactly when this graph H has a vertex cover of size at most n + k [1, Lemma 20]. The n joining edges form a perfect matching of H, so every fractional vertex cover of H has weight at least n, and the excess at budget n + k is at most k.
- **Above Guarantee Vertex Cover.** The relaxation is at least the size of a maximum matching, so μ is at most the excess over the matching [1, Theorem 3].
- **Almost 2-SAT.** Both versions reduce to Above Guarantee Vertex Cover [1, Corollary 2]. As instances of BIP2 they also reduce in linear time to Vertex Cover above LP with the same gap above the relaxation, which is at most k [4, Theorem 1 and Example 3].
- **Vertex Cover parameterized by a KVD set.** The preprocessing in the proof of [1, Theorem 5] (Lemma 1 there) leaves a graph G′ and a budget ℓ′, and G′ has a KVD set O of size at most k [1, Lemma 22]. Then vc(G′) − vc*(G′) ≤ |O|/2 ≤ k/2, from the two inequalities in the proof there. If ℓ′ ≥ vc*(G′) + k/2 the answer is yes at once, and otherwise the excess ℓ′ − vc*(G′) is below k/2. The walk then costs O(1.5214^{k/2}) = O(1.2335^k), times poly(n).
- **Vertex Cover parameterized by an odd cycle transversal.** An odd cycle transversal is a KVD set [1, Corollary 5].
- **KVD.** If G has a KVD set of size at most k, then vc(G) − vc*(G) = vc(G′) − vc*(G′) ≤ k/2 on the preprocessed graph G′ [1, Lemmas 2 and 22]. The walk tries the budgets from ⌈vc*(G′)⌉ up to vc*(G′) + k/2 on G′, and if none of them succeeds the answer is no. Otherwise a minimum vertex cover comes by self-reduction, which does not raise the excess, at a polynomial factor, and it gives a minimum KVD set in polynomial time [1, Corollary 4].

## 3. Measurements

`sim/bases.py` recomputes the root 2.314596 of the vectors of rules B5 and B6 of [1], checks the printed bases in exact arithmetic on the recurrence of the walk, and recomputes the implied bases from the root φ² of the tree of [1, Theorem 1]. Run it with `python bases.py` in `sim/`. It exits nonzero on a failed check.

## 4. Limits

- The search tree of [1], the safeness of its rules and its analysis are used as stated, as are its reductions and those of [4].
- Not formalized: the search tree of [1], the walk of [3], and the reductions of [1] and [4].
- The polynomial factor of the walk is not given explicitly, and there is no gate count.

## References

1. D. Lokshtanov, N. S. Narayanaswamy, V. Raman, M. S. Ramanujan, S. Saurabh. Faster parameterized algorithms using linear programming. ACM Transactions on Algorithms, 2014. arXiv:1203.0833.
2. Vertex Cover and Independent Set with a quantum algorithm. [quantum-vertex-cover](../quantum-vertex-cover/).
3. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14, 2018. arXiv:1509.02374.
4. Y. Iwata, K. Oka, Y. Yoshida. Linear-time FPT algorithms via network flow. SODA 2014. arXiv:1307.4927.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation script, and to draft the text.
