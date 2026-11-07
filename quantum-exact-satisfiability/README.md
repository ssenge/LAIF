# Quantum Exact Satisfiability

Written 7 Nov 2026.

Exact Satisfiability (XSAT) asks for an assignment to a CNF formula with n variables that sets exactly one literal of every clause to 1. X3SAT is the case of clauses with at most three literals.

**Theorem 1.** XSAT, and hence X3SAT, has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.0805^n). It finds a satisfying assignment if one exists.

Status: Claim, implied by the quantum walk on backtracking trees [1] applied to the DPLL algorithm of [2], with the running-time analysis of [2] as stated there. [2] is an unrefereed preprint. [`bounds.py`](bounds.py) checks √1.1674 ≤ 1.0805.

**Before.** To our knowledge, the only quantum algorithm stated for XSAT is the search over a subspace of [3], with O(2^{(n − M′)/2}) queries, where M′ is the number of linearly independent clauses. That bound is the better one only for formulas with M′ > 0.7766 n ([`bounds.log`](bounds.log)); the two can be combined by taking the smaller. Quantum search over all assignments takes 2^{n/2} ≈ 1.4142^n.

## The tree

The algorithm XSAT(ϕ) of [2] applies 14 lines in order of priority.

- **Single calls.** Lines 1 to 9 and 11 are simplification rules: each returns 0 for a clause that cannot be exactly satisfied, or fixes literals, links two literals, drops a constant, removes a subsumed clause, or applies resolution, and then makes one recursive call. Line 10 either simplifies, with one call, or branches. In the cases of Line 12 with a 1-j orientation, the rule links two literals or rewrites a clause and passes to Line 11 (Lemma 2 of [2]).
- **OR.** Lines 10, 12 and 13 branch into two calls, on x = 1 and x = 0 for a variable x or on δ = 1 and δ = 0 for a subclause δ, and return their OR.
- **Leaves.** Line 14 decides formulas in which every variable occurs at most twice in polynomial time.

So the decision procedure is a backtracking tree in the sense of [1]. Every rule removes a variable, a clause or a literal, so the depth is polynomial. The measure μ ≤ n gives each variable weight 1 or 0.8823, never increases under the rules, and every branching factor is at most 1.1674, so the tree has at most 1.1674^n · poly(n) nodes. This explicit bound is the one the walk of [1] needs. The walk decides satisfiability in √(1.1674^n) · poly(n) time, and an assignment is found by descending the tree with the walk at each child.

## Limits

- The case analysis of [2] is used as stated and is not reproduced here.
- No script runs the algorithm of [2]; [`bounds.py`](bounds.py) checks only the square root and the crossover with [3].

## References

1. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
2. G. Hoi. An improved exact algorithm for the exact satisfiability problem. arXiv:2010.03850, 2020.
3. S. Mandrà, G. G. Guerreschi and A. Aspuru-Guzik. Faster than classical quantum algorithm for dense formulas of exact satisfiability and occupation problems. New Journal of Physics 18, 2016. arXiv:1512.00859.
