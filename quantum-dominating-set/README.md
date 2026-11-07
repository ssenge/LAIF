# Domination problems in polynomial space with a quantum algorithm

Written 7 Nov 2026.

Input: a graph G on n vertices and a number k. Output: whether G has a solution of size at most k for the problems below. The smallest k, and a solution, follow by trying every k and by self-reduction.

- **Dominating Set:** a set D of vertices such that every vertex is in D or has a neighbour in D.
- **Independent Dominating Set:** a dominating set with no edge inside it.
- **Edge Dominating Set:** a set of edges such that every edge shares an endpoint with one of them. **Minimum Maximal Matching** asks for a smallest maximal matching, and both have weighted versions.

**Theorem 1.** With bounded error, polynomial space and no quantum random access memory, there are quantum algorithms in time

- O*(1.4969^{n/2}) ⊂ O(1.2235^n) for Dominating Set,
- O*(2^{0.212n}) ⊂ O(1.1583^n) for Independent Dominating Set,
- O*(1.3226^{n/2}) ⊂ O(1.1501^n) for Edge Dominating Set, Minimum Maximal Matching, and their weighted versions.

Status: Claim, implied by the quantum walk of [2] and the classical algorithms of [1], [7] and [6]. The structure of the decision trees is checked by scripts against brute force; the arithmetic of the bases is in Lean.

## Before and after

| Problem | Before | After |
|---|---|---|
| Dominating Set | O(2^{n/2}) quantum [4]; classically O*(1.4864^n) [3] and O*(1.4969^n) [1], both in polynomial space | O(1.2235^n) |
| Independent Dominating Set | classically O*(1.3351^n) [9] and O*(2^{0.424n}) [7], polynomial space; quantum O*(3^{n/6}) ⊂ O(1.2010^n) from the walk on the enumeration of maximal independent sets [10] | O(1.1583^n) |
| Edge Dominating Set, Minimum Maximal Matching | classically O*(1.3160^n) [8], with the conversion of [6] for Minimum Maximal Matching; quantum O(1.2010^n) from the walk on the enumeration of minimal vertex covers [10] | O(1.1501^n) |
| Weighted versions of both | classically O*(1.3226^n) [6], polynomial space | O(1.1501^n) |

All rows are for bounded error, polynomial space and no quantum random access memory. These are best known upper bounds in this model, to our knowledge, and not tight ones. The quantum bound 1.2010^n in the table is the plain walk on an enumeration tree; to our knowledge it has not been stated. For unweighted graphs, Minimum Maximal Matching and Edge Dominating Set have the same optimum, with a conversion in polynomial time [6].

**Prior work.** The classical algorithms are branch and reduce algorithms analysed by measure and conquer [1], [6], [7]. The quantum walk on backtracking trees is from [2], and the remark that quantum search applies to branching algorithms in general from [5]. To our knowledge, the quantum bounds above have not been stated before.

## 1. The decision trees

Each algorithm below, in its decision form with a budget k, is a backtracking tree: every step answers, makes one tail call, or branches into the OR of polynomially many children. Each node computes its children in polynomial time and stores an instance of polynomial size, and the depth is polynomial. The classical analysis bounds the number of leaves of the full search tree by p(n) · c^n for the classical base c and a fixed polynomial p, and the tree for a budget k is a subtree of it. The depth is at most 2n for Dominating Set (each step removes a set or an element, and the merge rule removes two sets and two elements and adds one), at most n for edge domination (each step lowers |U|), and at most 2n + n² for Independent Dominating Set (vertices, free vertices and edges). So the tree has at most (2n + n² + 1) · p(n) · c^n nodes.

**Dominating Set, Algorithm 4 of [1]** (numbering of the technical report). It works on the set cover instance with the sets N[v] over the vertex set.

- *Answer.* If no element is left, answer yes when k ≥ 0. If k ≤ 0, or some element lies in no set, answer no. If all sets have at most two elements, a maximum matching gives the minimum cover, which the node compares with k.
- *Tail call.* An element of frequency one forces its set, taken with budget k − 1. A set contained in another set is removed, and so is an element whose sets include all sets of another element, both with budget k. The counting rule of [1] takes a set with budget k − 1. The rule for a set R = {e₁, e₂} of two frequency-two elements, with second sets R₁ and R₂, replaces R, R₁, R₂ by (R₁ ∪ R₂) \ R on the elements outside R. The subset rules run first, so R₁ ≠ R₂ and R ⊄ Rᵢ. By the argument in [1], the minimum cover then drops by exactly one, so the call has budget k − 1.
- *OR.* Otherwise it branches on a set S of maximum size: take S with budget k − 1, or discard S with budget k.

**Independent Dominating Set, [7].** Vertices are free or marked, where a marked vertex may not enter the solution but must still be dominated. For a chosen vertex v, some free vertex u ∈ N[v] is in the solution. The algorithm branches over these u, removes N[u] in each branch, and lowers the budget by one. It marks the vertices tried earlier in the later branches. Its refinements choose which branchings to apply on vertices of small degree, and keep this form.

**Edge Dominating Set, Algorithm 4 of [6]** (numbering of the technical report). The vertices are split into a vertex cover C, an independent set I and undecided vertices U. A clique component H of G[U] is handled by a tail call on a graph with one new vertex joined to H, whose optimum is exactly one larger, so the call has budget k + 1. This rule is used for cliques of every size; the measure counts only U, so the analysis is unchanged, and the graph keeps at most 2n vertices. Otherwise the algorithm branches on an undecided vertex, either into I with its undecided neighbours into C, or into C, and on the paths and cycles of G[U] into two or a constant number of children. At a leaf, C is a vertex cover, and the smallest edge dominating set whose endpoints include C is computed through a maximum matching. Unweighted Minimum Maximal Matching has the same decision problem by the conversion in [6]. For the weighted versions, Algorithms 5 and 7 of [6] put isolated undecided vertices into I with budget k and handle cliques of two or three vertices by one tail call: for weighted edge domination with the budget raised by the weight of the new edge, for weighted minimum maximal matching with zero-weight new edges and budget k. Larger cliques are branched on. The leaves are a generalised edge cover or a perfect matching, both polynomial.

## 2. The quantum algorithm

The quantum walk of [2], given the bound T_n = p(n) · c^n, decides whether the tree has a marked leaf in time √T_n poly(n), with bounded error and in polynomial space. Its running time depends only on n. Running it for every budget gives the optimum. A solution follows by descending the tree from the root: run the detection on each child, move to one that contains a marked leaf, and read the solution off that leaf. With errors amplified to 1/poly(n) per call this costs a factor poly(n). The bases are √1.4969 ≤ 1.2235, 2^{0.424/2} ≤ 1.1583 and √1.3226 ≤ 1.1501. For weighted versions the budget is a weight bound, and for integer weights of polynomial bit length a binary search over the budget gives the optimum. ∎

The algorithms of [3] for Dominating Set, of [9] for Independent Dominating Set and of [8] for Edge Dominating Set and unweighted Minimum Maximal Matching would give O(1.2192^n), O(1.1555^n) and O(1.1472^n) by the same argument if they are backtracking trees in this sense. Their structure is not covered here.

## 3. Measurements

Each script runs the decision procedure on random graphs, takes the smallest accepted budget, and compares it with brute force.

| Script | Procedure | Graphs | Result |
|---|---|---|---|
| [`ds_tree.py`](ds_tree.py) | Algorithm 4 of [1], all rules in its order | 400, 4 to 15 vertices | equal to the domination number in every case ([`ds_tree.log`](ds_tree.log)) |
| [`ids_tree.py`](ids_tree.py) | the basic branching of [7], Lemma 1, with marking | 400, 3 to 13 vertices | equal to the independent domination number ([`ids_tree.log`](ids_tree.log)) |
| [`eds_tree.py`](eds_tree.py) | Algorithm 2 of [6]: clique rule, branching, paths and cycles, matching leaves | 300, 3 to 10 vertices | equal to the edge domination number ([`eds_tree.log`](eds_tree.log)) |

The scripts for [7] and [6] implement the basic versions, which have the same kinds of steps as the refined algorithms but not all their branching cases. The weighted rules and the bounds on the tree size are not run.

## 4. Limits

- The running times of [1], [6] and [7] are used as stated there, from their measure and conquer analyses, which are not reproduced here.
- The quantum walk of [2] is used as stated.

## 5. Formal verification

The Lean library [`lean/`](lean/) is built on Mathlib and uses only the standard axioms ([`lean/axioms.log`](lean/axioms.log)).

| Theorem | Statement |
|---|---|
| `base_le` | √1.4969 ≤ 1.2235 |
| `pow_base_le` | √(1.4969^n) ≤ 1.2235^n for every n |
| `edge_base_le` | √1.3226 ≤ 1.1501 |
| `indep_base_le` | 2^{53/250} ≤ 1.1583, where 53/250 = 0.424/2 |

Not formalized: the decision trees of Section 1, the classical analyses and the quantum walk.

## References

1. J. M. M. van Rooij and H. L. Bodlaender. Exact algorithms for dominating set. Discrete Applied Mathematics 159(17), 2011. Technical report UU-CS-2009-025.
2. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
3. Y. Iwata. A faster algorithm for dominating set analyzed by the potential method. IPEC 2011, LNCS 7112.
4. R. Wong, W.-L. Chang, W.-Y. Chung and A. V. Vasilakos. Biomolecular and quantum algorithms for the dominating set problem in arbitrary networks. Scientific Reports 13, 4205, 2023.
5. M. Fürer. Solving NP-complete problems with quantum search. LATIN 2008.
6. J. M. M. van Rooij and H. L. Bodlaender. Exact algorithms for edge domination. Algorithmica 64(4), 2012. Technical report UU-CS-2007-051.
7. N. Bourgeois, B. Escoffier and V. Th. Paschos. Fast algorithms for min independent dominating set. SIROCCO 2010. arXiv:0905.1993.
8. M. Xiao and H. Nagamochi. A refined exact algorithm for edge dominating set. Theoretical Computer Science 560, 2014.
9. N. Bourgeois, F. Della Croce, B. Escoffier and V. Th. Paschos. Fast algorithms for min independent dominating set. Discrete Applied Mathematics 161(4-5), 2013.
10. J. W. Moon and L. Moser. On cliques in graphs. Israel Journal of Mathematics 3, 1965.
