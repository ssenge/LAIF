# Dominating Set in polynomial space with a quantum algorithm

Written 7 Nov 2026.

Input: a graph G on n vertices and a number k. Output: whether G has a dominating set of at most k vertices, that is, a set D such that every vertex is in D or has a neighbour in D. The smallest such k, and a set, follow by binary search and self-reduction.

**Theorem 1.** Dominating Set has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O*(1.4969^{n/2}) ⊂ O(1.2235^n).

Status: Claim, implied by the quantum walk of [2] and the classical algorithm of [1]. The structure of the decision tree is checked by a script against brute force; the arithmetic of the base is in Lean.

## Before and after

| Problem | Before | After |
|---|---|---|
| Dominating Set, n vertices | O(2^{n/2}) quantum [4]; classically O*(1.4864^n) [3] and O*(1.4969^n) [1], both in polynomial space | O(1.2235^n), bounded error, polynomial space, no quantum random access memory |

This is a best known upper bound in this model, to our knowledge, and not a tight one.

**Prior work.** The algorithm of [1] is a measure and conquer analysis of a branch and reduce algorithm for Set Cover, applied to the sets N[v] over the vertex set. The quantum walk on backtracking trees is from [2], and the remark that quantum search applies to branching algorithms in general from [5]. To our knowledge, the quantum bound above has not been stated before.

## 1. The decision tree

Algorithm 4 of [1] works on a set cover instance (𝒮, 𝒰). In its decision form with a budget k, every step is one of three kinds.

- **Answer.** If 𝒰 is empty, answer yes if k ≥ 0. If k ≤ 0, or some element lies in no set, answer no. If all sets have at most two elements, a maximum matching gives the minimum cover in polynomial time, and the node compares it with k.
- **Tail call.** The reduction rules make one call. An element of frequency one forces its set, which is taken with budget k − 1. A set contained in another set is removed, and an element whose sets include all sets of another element is removed, with budget k. The counting rule of [1] takes a set with budget k − 1. The rule for a set R = {e₁, e₂} of two frequency-two elements, with second sets R₁ and R₂, replaces R, R₁, R₂ by Q = (R₁ ∪ R₂) \ R on 𝒰 \ R. By the argument in [1], the minimum cover of the new instance is exactly one smaller, so the call has budget k − 1.
- **OR.** Otherwise the algorithm branches on a set S of maximum size. The instance has a cover of at most k sets if and only if taking S leaves one with at most k − 1 sets or discarding S leaves one with at most k sets.

So the decision procedure is a backtracking tree. Each node computes its children in polynomial time and stores an instance of polynomial size, and the depth is at most 2n plus the number of tail calls, which is polynomial since each rule removes a set or an element. A marked leaf is an answer yes.

The analysis of [1] bounds the number of subproblems by α^κ for its measure κ ≤ (v_max + w_max) n, and the reduction rules do not increase the measure. The tree for a budget k is a subtree of the full search tree, so it has at most p(n) · 1.4969^n nodes for a fixed polynomial p.

## 2. The quantum algorithm

The quantum walk of [2], given the bound T_n = p(n) · 1.4969^n, decides whether the tree has a marked leaf in time √T_n poly(n), with bounded error and in polynomial space. Its running time depends only on n. Running it for k = 0, …, n gives the domination number, and a dominating set follows by self-reduction: for each vertex v in turn, ask whether a dominating set of the current size exists that contains v, by removing N[v] from the universe and lowering the budget, and keep v if the answer is yes. This costs a factor poly(n). ∎

The faster polynomial-space algorithm of [3], in O*(1.4864^n), would give O(1.2192^n) by the same argument if it is a backtracking tree in this sense. Its structure is not covered here.

## 3. Measurements

[`ds_tree.py`](ds_tree.py) implements the decision procedure of Section 1, with the rules in the order of Algorithm 4 of [1]. On 400 random graphs with 4 to 15 vertices, the smallest accepted budget equals the domination number computed by brute force in every case ([`ds_tree.log`](ds_tree.log)). The log also lists the largest tree sizes per budget; they are far below the worst-case bound, as expected on random graphs.

## 4. Limits

- The running time of [1] is used as stated there, from its measure and conquer analysis, which is not reproduced here.
- The quantum walk of [2] is used as stated.

## 5. Formal verification

The Lean library [`lean/`](lean/) is built on Mathlib and uses only the standard axioms ([`lean/axioms.log`](lean/axioms.log)).

| Theorem | Statement |
|---|---|
| `base_le` | √1.4969 ≤ 1.2235 |
| `pow_base_le` | √(1.4969^n) ≤ 1.2235^n for every n |

Not formalized: the decision tree of Section 1, the analysis of [1] and the quantum walk.

## References

1. J. M. M. van Rooij and H. L. Bodlaender. Exact algorithms for dominating set. Discrete Applied Mathematics 159(17), 2011. Technical report UU-CS-2009-025.
2. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
3. Y. Iwata. A faster algorithm for dominating set analyzed by the potential method. IPEC 2011, LNCS 7112.
4. R. Wong, W.-L. Chang, W.-Y. Chung and A. V. Vasilakos. Biomolecular and quantum algorithms for the dominating set problem in arbitrary networks. Scientific Reports 13, 4205, 2023.
5. M. Fürer. Solving NP-complete problems with quantum search. LATIN 2008.
