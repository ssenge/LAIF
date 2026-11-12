# Quantum Satisfiability and MaxSAT in Terms of Clauses and Formula Length

Written 10 Nov 2026; optimal MaxSAT assignments and the Lean library added 12 Nov 2026.

SAT asks whether a CNF formula with n variables, m clauses of any length and length L (the number of literal occurrences) has a satisfying assignment. MaxSAT asks, for a CNF formula and a number k, whether some assignment satisfies at least k clauses.

**Theorem 1.** SAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time 1.1058^m · poly(L). It finds a satisfying assignment if one exists.

Status: Claim, implied by the quantum walk on backtracking trees [1] applied to the algorithm of [2], with the case analysis of [2] as stated there. [`bounds.py`](bounds.py) checks √1.2226 ≤ 1.1058 and, in exact arithmetic, the six inequalities of the amortized proof of [2, Theorem 1]. The amortized node count itself is in [Lean](#lean), with the branching patterns and the reduction properties of [2] as hypotheses.

**Theorem 2.** MaxSAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time 1.1352^m · poly(L). It finds an assignment that satisfies the maximum number of clauses.

Status: Claim, implied by [1] applied to the algorithm of [4], whose last step uses the set cover algorithm of [5] as in [6], with the case analyses of [4], [5] and [6] as stated there, and the [self-reduction](#solutions-by-self-reduction) below for the assignment. [`bounds.py`](bounds.py) checks √1.2886 ≤ 1.1352. The counting lemma with attached subtrees, the greedy step of the self-reduction and the numeric bounds are in [Lean](#lean).

**Theorem 3.** SAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.0327^L). It finds a satisfying assignment if one exists.

Status: Claim, implied by [1] applied to the algorithm SparseSAT of [7], whose last step uses the (3, 2)-constraint satisfaction algorithm of [8], with the analyses of [7] and [8] as stated there. [`bounds.py`](bounds.py) checks √(2^{0.0926}) ≤ 1.0327.

**Before.** To our knowledge, no quantum bound for SAT or MaxSAT in terms of m or L has been stated. The best classical bounds are 1.2226^m for SAT [2], improving 1.234^m and 1.239^m [3], and 1.2886^m for MaxSAT [4]; in terms of L, the best classical bound is 1.0638^L [9], and 2^{0.0926 L} ≤ 1.0663^L is that of [7]. Quantum search and quantum maximum finding over all assignments take 2^{n/2}; Theorems 1 and 2 are smaller whenever m < 3.4461 n and m < 2.7330 n ([`bounds.log`](bounds.log)), and the bounds can be combined by taking the smaller.

The same approach, the walk of [1] on classical branching algorithms with polynomial space, was applied to graph colouring, domination problems and monotone local search in [11], which is the closest prior work.

## The tree for SAT

Algorithm 1 of [2] reduces the formula and then branches.

- **Single calls.** Five reduction rules: unit clauses and pure literals, subsumption, resolution on a (1, b)- or (2, 2)-literal, and two rules that set an autarkic set of literals to 1. Each preserves satisfiability, and together they run in polynomial time, since each assigns a variable or eliminates one by resolution [2, Lemmas 2 and 3].
- **Leaves.** The empty formula is satisfiable; a formula with the empty clause is not.
- **OR.** Every branching, for bad formulas in [2, Section 6.1] and for good formulas in [2, Section 6.2], picks a literal x and recurses on F with x = 1 and on F with x = 0, returning the OR. Deciding which case applies takes polynomial time.

So the algorithm is a backtracking tree in the sense of [1]. Each branch removes at least three clauses, so the depth is polynomial. The proof of [2, Theorem 1] bounds the number of nodes of the search tree directly: T(F) ≤ 2 · 1.2226^m − 1 for good formulas and T(F) ≤ (2/0.9136) · 1.2226^m − 1 for bad ones, by induction with the branching vectors (3, 4) and (3, 3) for bad formulas and (3, 5), (4, 4) and (3, 4) for good ones, where (3, 3) for bad formulas and (3, 4) for good ones are used only when both children are good. With the polynomial reduction steps as single-child nodes, the tree has at most 1.2226^m · poly(L) nodes, where L is the length of the formula. This explicit bound is the one the walk of [1] needs, and the walk decides satisfiability in √(1.2226^m) · poly(L) time. An assignment is found by descending the tree with the walk at each child; the variables removed by the reductions are then set in reverse order, a resolved variable to a value that satisfies its removed clauses and an autarkic set to 1.

## The tree for MaxSAT

The algorithm of [4] works on pairs (F, k) and is a decision procedure for them.

- **Single calls.** Nine reduction rules each replace (F, k) by an equivalent pair (F′, k′) with no more clauses, in polynomial time [4, Lemma 1]: they drop clauses with a literal and its negation, combine xC and x̄C into C, resolve (1, 1)-literals and some (2, 2)-literals, rewrite the clauses around some (2, 1)- and (i, 1)-literals with one clause fewer, set literals that occur in enough unit clauses, merge literals that dominate each other, and drop clauses with a dominating literal. Lemmas 2 and 3 of [4] cite further reduction rules of the same kind from earlier work.
- **Leaves.** If k ≤ 0 the answer is yes; if k exceeds the number of clauses left the answer is no.
- **OR.** Steps 1 to 6 branch on assignments: x = 1 against x = 0, or x = 1 against x = 0 together with D = 0 for a clause x̄D, each with the budget lowered by the clauses satisfied, or the literals of C₁, C₂ and D set to 0 against the resolvent F\x with budget k − 1. Some steps branch again inside a child before the analysis closes; these are further OR nodes. A branch is safe, so (F, k) is a yes-instance if and only if some child is.
- **Step 7.** When only (3, 1)- and (4, 1)-singletons remain, the instance is a Minimum Set Cover instance with sets of size at most four [6], solved by the polynomial-space algorithm of [5]. Some optimal assignment satisfies every clause without a negated singleton [6], so with m′ clauses left, (F, k) is a yes-instance if and only if a cover of size at most m′ − k exists. In decision form with a budget this algorithm is a backtracking tree, as described for Dominating Set in [quantum-dominating-set](../quantum-dominating-set/), and here it has at most 1.2576^m · poly(m) nodes [4, Lemma 5].

Every branching factor of Steps 1 to 6 is at most 1.2886, attained by the vector (6, 6, 5, 5), and the set cover subtrees at the leaves have at most 1.2576^m · poly(m) ≤ 1.2886^m · poly(m) nodes. So the tree has at most 1.2886^m · poly(L) nodes, and the walk of [1] decides (F, k) in √(1.2886^m) · poly(L) time. The optimum follows by a binary search over k with O(log m) calls, each with its error reduced to O(1/log m).

## The tree for SAT in terms of L

The algorithm SparseSAT of [7, Algorithm 6] has cases 0 to 12.

- **Single calls.** Cases 1 to 7 standardize the formula, set unit and pure literals, simplify pairs of variables that occur together twice, and apply resolution and backward resolution when admissible; case 9 tests a reduced version of F[l] in polynomial time.
- **OR.** Cases 8 to 11 branch into two calls and return their OR.
- **Case 12.** The formula is converted in polynomial time into a (3, 2)-constraint satisfaction instance with n/3 variables [7, Lemma 8] and solved by the branching algorithm of [8]. That algorithm is a backtracking tree, as used under quantum search for 3-colouring in [quantum-graph-colouring](../quantum-graph-colouring/), with at most 1.36443^{n/3} · poly(n) nodes.

There is no splitting into components and no other subroutine. The running time of SparseSAT, which includes the subtrees of case 12, is O(2^{0.0926 L}) [7, Corollary 31], and the tree has at most that many nodes up to a polynomial factor. The walk of [1] decides satisfiability in O(2^{0.0463 L} · poly(L)) ≤ O(1.0327^L) time, and an assignment is found by descending the tree and undoing the reductions as in Theorem 1.

## Solutions by self-reduction

The variables are fixed one at a time. For a variable x, set x = 1 and simplify: remove the satisfied clauses and the literal x̄, count the satisfied clauses, and drop empty clauses, which no assignment satisfies. For the result, the algorithm of Theorem 2 with a binary search over k gives the optimum. Keep x = 1 if the count plus this optimum equals the optimum of the current formula, and set x = 0 otherwise. Neither m, L nor n grows, so there are n steps with O(log m) calls each. With the error of each call reduced to O(1/(n log m)), the total error stays bounded and the time stays 1.1352^m · poly(L). For SAT the same steps keep a value with a yes answer.

## Lean

[`lean/`](lean/) is a Lean 4 library `SatTrees` (Lean v4.36.0-rc1, Mathlib commit d875a8de5222f62cf1c2fafc7984588adadc990a) with 14 theorems, no `sorry`, and only the standard axioms (propext, Classical.choice, Quot.sound), as printed by `lean/SatTreesAxioms.lean` into [`lean/axioms.txt`](lean/axioms.txt). Build with `lake exe cache get` and then `lake build` in `lean/`.

- `Tree.size_le_of_pays`: a potential Φ with 1 + Σ Φ(child) ≤ Φ at every node bounds the number of nodes by Φ(root).
- `Tree.size_le_of_branches` and `branch_step`: if Σ c^{μ(child)} ≤ c^μ at every node, which holds when c is at least the branching number of the node's branching vector, and a height h drops by one to each child, then the tree has at most (h(root) + 1) c^{μ(root)} nodes.
- `Tree.size_le_of_branchesAt`: the same count with attachment nodes, whose subtrees come from another algorithm (the set cover algorithm in Theorem 2, the constraint satisfaction algorithm in Theorem 3) and have at most p c^μ nodes. The bound is (h(root) + 1) p c^{μ(root)}.
- `sat_tree_size` and `amortized_inequalities`: the amortized count of [2, Theorem 1]. A tree whose nodes branch in the patterns of [2, Lemmas 6 and 7], with children reduced as in [2, Lemma 5], has at most 2 · 1.2226^m − 1 nodes on a good formula and (2/0.9136) · 1.2226^m − 1 on a bad one.
- `exists_step` and `greedy_optimal`: fixing the variables in order, each to a value that keeps the optimum of a function f over the completions, ends with an assignment that maximizes f.
- `sat_root`, `maxsat_cert` and `satl_root`: √1.2226 ≤ 1.1058; the branching number of (6, 6, 5, 5) and the set cover base 1.2576 are at most 1.2886, and √1.2886 ≤ 1.1352; √(2^{0.0926}) ≤ 1.0327.
- `xsat_root`, `x3sat_vectors` and `x3sat_sparse_root`: the bounds of [quantum-exact-satisfiability](../quantum-exact-satisfiability/).

Not formalized: the case analyses of [2], [4], [5], [6], [7] and [8], which enter the amortized count as hypotheses and the other theorems as cited bounds; the walk of [1] and the embedding of a backtracking tree in it; and the fact that simplifying a formula after fixing a variable preserves the optimum over the completions.

## Limits

- The case analyses of [2], [4], [5] and [6] are used as stated and are not reproduced here.
- [4] omits the proof of its Lemma 4 and some reduction rules behind its Lemmas 2 and 3, which it cites from earlier work.
- Theorems 1 and 2 carry a factor poly(L), which is not polynomial in m when clauses are long; the classical bounds of [2] and [4] carry the same factor.
- No script runs the algorithms of [2], [4], [5], [7] or [8].
- Theorem 3 uses the algorithm of [7]. The faster algorithm of [9], with base 1.0638, solves a 3-CNF part with a deterministic 3-SAT algorithm that is not a branching algorithm; a quantum form of it, and of the 1.0652^L algorithm of [10], is not treated here.

## References

1. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
2. H. Chu, M. Xiao and Z. Zhang. An improved upper bound for SAT. AAAI 2021; Theoretical Computer Science, 2021. arXiv:2007.03829.
3. M. Yamamoto. An improved O(1.234^m)-time deterministic algorithm for SAT. ISAAC 2005. E. A. Hirsch. New worst-case upper bounds for SAT. Journal of Automated Reasoning 24(4), 2000.
4. M. Xiao. An exact MaxSAT algorithm: further observations and further improvements. IJCAI 2022.
5. J. M. M. van Rooij and H. L. Bodlaender. Exact algorithms for dominating set. Discrete Applied Mathematics 159(17), 2011.
6. I. Bliznets and A. Golovnev. A new algorithm for parameterized MAX-SAT. IPEC 2012.
7. M. Wahlström. Algorithms, Measures and Upper Bounds for Satisfiability and Related Problems. PhD thesis, Linköping University, 2007, Chapter 4. M. Wahlström. An algorithm for the SAT problem for formulae of linear length. ESA 2005.
8. R. Beigel and D. Eppstein. 3-coloring in time O(1.3289^n). Journal of Algorithms 54(2), 2005.
9. J. Peng and M. Xiao. Further improvements for SAT in terms of formula length. arXiv:2105.06131, 2021.
10. J. Chen and Y. Liu. An improved SAT algorithm in terms of formula length. WADS 2009.
11. S. Senge. Polynomial-space quantum algorithms from classical branching: colouring, domination and monotone local search. arXiv:2611.12714, 2026.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the scripts and the Lean formalization, and to draft the text.
