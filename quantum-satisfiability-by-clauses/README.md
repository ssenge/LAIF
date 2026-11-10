# Quantum Satisfiability and MaxSAT in Terms of the Number of Clauses

Written 10 Nov 2026.

SAT asks whether a CNF formula with n variables and m clauses of any length has a satisfying assignment. MaxSAT asks, for a CNF formula and a number k, whether some assignment satisfies at least k clauses.

**Theorem 1.** SAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.1058^m). It finds a satisfying assignment if one exists.

Status: Claim, implied by the quantum walk on backtracking trees [1] applied to the algorithm of [2], with the case analysis of [2] as stated there. [`bounds.py`](bounds.py) checks √1.2226 ≤ 1.1058 and, in exact arithmetic, the six inequalities of the amortized proof of [2, Theorem 1].

**Theorem 2.** MaxSAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.1352^m). It finds an assignment that satisfies at least k clauses if one exists, and with a binary search over k a maximum one.

Status: Claim, implied by [1] applied to the algorithm of [4], whose last step uses the set cover algorithm of [5] as in [6], with the case analyses of [4], [5] and [6] as stated there. [`bounds.py`](bounds.py) checks √1.2886 ≤ 1.1352.

**Before.** To our knowledge, no quantum bound for SAT or MaxSAT in terms of m has been stated. The best classical bounds are 1.2226^m for SAT [2], improving 1.234^m and 1.239^m [3], and 1.2886^m for MaxSAT [4]. Quantum search and quantum maximum finding over all assignments take 2^{n/2}; Theorems 1 and 2 are smaller whenever m < 3.4461 n and m < 2.7330 n ([`bounds.log`](bounds.log)), and the bounds can be combined by taking the smaller.

## The tree for SAT

Algorithm 1 of [2] reduces the formula and then branches.

- **Single calls.** Five reduction rules: unit clauses and pure literals, subsumption, resolution on a (1, b)- or (2, 2)-literal, and two rules that set an autarkic set of literals to 1. Each preserves satisfiability, and together they run in polynomial time, since each assigns a variable or eliminates one by resolution [2, Lemmas 2 and 3].
- **Leaves.** The empty formula is satisfiable; a formula with the empty clause is not.
- **OR.** Every branching, for bad formulas in [2, Section 6.1] and for good formulas in [2, Section 6.2], picks a literal x and recurses on F with x = 1 and on F with x = 0, returning the OR. Deciding which case applies takes polynomial time.

So the algorithm is a backtracking tree in the sense of [1]. Each branch removes at least three clauses, so the depth is polynomial. The proof of [2, Theorem 1] bounds the number of branching nodes of the search tree directly: T(F) ≤ 2 · 1.2226^m − 1 for good formulas and T(F) ≤ (2/0.9136) · 1.2226^m − 1 for bad ones, by induction with the branching vectors (3, 4) and (3, 3) for bad formulas and (3, 5), (4, 4) and (3, 4) for good ones, where (3, 3) for bad formulas and (3, 4) for good ones are used only when both children are good. With the polynomial reduction steps as single-child nodes, the tree has at most 1.2226^m · poly(L) nodes, where L is the length of the formula. This explicit bound is the one the walk of [1] needs, and the walk decides satisfiability in √(1.2226^m) · poly(L) time. An assignment is found by descending the tree with the walk at each child; the variables removed by the reductions are then set in reverse order, a resolved variable to a value that satisfies its removed clauses and an autarkic set to 1.

## The tree for MaxSAT

The algorithm of [4] works on pairs (F, k) and is a decision procedure for them.

- **Single calls.** Nine reduction rules each replace (F, k) by an equivalent pair (F′, k′) with no more clauses, in polynomial time [4, Lemma 1]: they drop clauses with a literal and its negation, combine xC and x̄C into C, resolve (1, 1)-literals and some (2, 2)-literals, rewrite the clauses around some (2, 1)- and (i, 1)-literals with one clause fewer, set literals that occur in enough unit clauses, merge literals that dominate each other, and drop clauses with a dominating literal. Lemmas 2 and 3 of [4] cite further reduction rules of the same kind from earlier work.
- **OR.** Steps 1 to 6 branch on assignments: x = 1 against x = 0, or x = 1 against x = 0 together with D = 0 for a clause x̄D, or a set of clauses set to 0 against the resolvent F\x with k − 1, each with the budget lowered by the clauses satisfied. Some steps branch again inside a child before the analysis closes; these are further OR nodes. A branch is safe, so (F, k) is a yes-instance if and only if some child is.
- **Step 7.** When only (3, 1)- and (4, 1)-singletons remain, the instance is a Minimum Set Cover instance with sets of size at most four [6], solved by the polynomial-space algorithm of [5]. In decision form with a budget this algorithm is a backtracking tree, as described for Dominating Set in [quantum-dominating-set](../quantum-dominating-set/), and here it has at most 1.2576^m · poly(m) nodes [4, Lemma 5].

Every branching factor of Steps 1 to 6 is at most 1.2886, attained by the vector (6, 6, 5, 5), and the set cover subtrees at the leaves have at most 1.2576^m · poly(m) ≤ 1.2886^m · poly(m) nodes. So the tree has at most 1.2886^m · poly(L) nodes, and the walk of [1] decides (F, k) in √(1.2886^m) · poly(L) ≤ O(1.1352^m) time. An assignment is found by descending the tree, and the optimum by a binary search over k with O(log m) calls, each with its error reduced to O(1/log m).

## Limits

- The case analyses of [2], [4], [5] and [6] are used as stated and are not reproduced here; [`bounds.py`](bounds.py) checks only the arithmetic of the amortized proof of [2] and the square roots.
- [4] omits the proof of its Lemma 4 and some reduction rules behind its Lemmas 2 and 3, which it cites from earlier work.
- No script runs the algorithms of [2], [4] or [5].

## References

1. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
2. H. Chu, M. Xiao and Z. Zhang. An improved upper bound for SAT. AAAI 2021; Theoretical Computer Science, 2021. arXiv:2007.03829.
3. M. Yamamoto. An improved O(1.234^m)-time deterministic algorithm for SAT. ISAAC 2005. E. A. Hirsch. New worst-case upper bounds for SAT. Journal of Automated Reasoning 24(4), 2000.
4. M. Xiao. An exact MaxSAT algorithm: further observations and further improvements. IJCAI 2022.
5. J. M. M. van Rooij and H. L. Bodlaender. Exact algorithms for dominating set. Discrete Applied Mathematics 159(17), 2011.
6. I. Bliznets and A. Golovnev. A new algorithm for parameterized MAX-SAT. IPEC 2012.
