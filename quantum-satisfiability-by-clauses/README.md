# Quantum Satisfiability in Terms of the Number of Clauses

Written 10 Nov 2026.

SAT asks whether a CNF formula with n variables and m clauses of any length has a satisfying assignment.

**Theorem 1.** SAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.1058^m). It finds a satisfying assignment if one exists.

Status: Claim, implied by the quantum walk on backtracking trees [1] applied to the algorithm of [2], with the case analysis of [2] as stated there. [`bounds.py`](bounds.py) checks √1.2226 ≤ 1.1058 and, in exact arithmetic, the six inequalities of the amortized proof of [2, Theorem 1].

**Before.** To our knowledge, no quantum bound for SAT in terms of m has been stated. The best classical bound is 1.2226^m [2], improving 1.234^m and 1.239^m [3]. Quantum search over all assignments takes 2^{n/2}; Theorem 1 is smaller whenever m < 3.4461 n ([`bounds.log`](bounds.log)), and the two can be combined by taking the smaller.

## The tree

Algorithm 1 of [2] reduces the formula and then branches.

- **Single calls.** Five reduction rules: unit clauses and pure literals, subsumption, resolution on a (1, b)- or (2, 2)-literal, and two rules that set an autarkic set of literals to 1. Each preserves satisfiability, and together they run in polynomial time, since each assigns a variable or eliminates one by resolution [2, Lemmas 2 and 3].
- **Leaves.** The empty formula is satisfiable; a formula with the empty clause is not.
- **OR.** Every branching, for bad formulas in [2, Section 6.1] and for good formulas in [2, Section 6.2], picks a literal x and recurses on F with x = 1 and on F with x = 0, returning the OR. Deciding which case applies takes polynomial time.

So the algorithm is a backtracking tree in the sense of [1]. Each branch removes at least three clauses, so the depth is polynomial. The proof of [2, Theorem 1] bounds the number of branching nodes of the search tree directly: T(F) ≤ 2 · 1.2226^m − 1 for good formulas and T(F) ≤ (2/0.9136) · 1.2226^m − 1 for bad ones, by induction with the branching vectors (3, 4) and (3, 3) for bad formulas and (3, 5), (4, 4) and (3, 4) for good ones, where (3, 3) for bad formulas and (3, 4) for good ones are used only when both children are good. With the polynomial reduction steps as single-child nodes, the tree has at most 1.2226^m · poly(L) nodes, where L is the length of the formula. This explicit bound is the one the walk of [1] needs, and the walk decides satisfiability in √(1.2226^m) · poly(L) time. An assignment is found by descending the tree with the walk at each child; the variables removed by the reductions are then set in reverse order, a resolved variable to a value that satisfies its removed clauses and an autarkic set to 1.

## Limits

- The case analysis of [2] is used as stated and is not reproduced here; [`bounds.py`](bounds.py) checks only the arithmetic of its amortized proof.
- No script runs the algorithm of [2].

## References

1. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
2. H. Chu, M. Xiao and Z. Zhang. An improved upper bound for SAT. AAAI 2021; Theoretical Computer Science, 2021. arXiv:2007.03829.
3. M. Yamamoto. An improved O(1.234^m)-time deterministic algorithm for SAT. ISAAC 2005. E. A. Hirsch. New worst-case upper bounds for SAT. Journal of Automated Reasoning 24(4), 2000.
