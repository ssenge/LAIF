# Quantum Exact Satisfiability

Written 7 Nov 2026; X3SAT added 10 Nov 2026, X3SAT in terms of clauses 12 Nov 2026.

Exact Satisfiability (XSAT) asks for an assignment to a CNF formula with n variables that sets exactly one literal of every clause to 1. X3SAT is the case of clauses with at most three literals.

**Theorem 1.** XSAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time poly(L) + O(1.0805^n), where L is the length of the formula. It finds a satisfying assignment if one exists.

Status: Claim, implied by the quantum walk on backtracking trees [1] applied to the DPLL algorithm of [2], with the running-time analysis of [2] as stated there. [2] is an unrefereed preprint. [`bounds.py`](bounds.py) checks √1.1674 ≤ 1.0805, and the same inequality is `xsat_root` in the Lean library of [quantum-satisfiability-by-clauses](../quantum-satisfiability-by-clauses/#lean).

**Theorem 2.** X3SAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.0490^n). It finds a satisfying assignment if one exists.

Status: Claim, implied by [1] applied to the X3SAT algorithm of [4], with the case analysis of [4] as stated there. [`bounds.py`](bounds.py) checks √τ(12, 4) ≤ 1.0490 and the other branching numbers quoted below. In the Lean library of [quantum-satisfiability-by-clauses](../quantum-satisfiability-by-clauses/#lean), `x3sat_vectors` shows that 1.1003 is at least the branching numbers of (12, 4), (11, 5), (9, 6) and (8, 7), and `x3sat_sparse_root` shows 2^{2/15} ≤ 1.1003 and √1.1003 ≤ 1.0490.

**Theorem 3.** X3SAT has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O(1.0764^m) on formulas with m clauses. It finds a satisfying assignment if one exists.

Status: Claim, implied by [1] applied to the X3SAT algorithm of [7] with its splitting into components replaced as described below, with the case analysis of [7] as stated there. [`bounds.py`](bounds.py) checks τ(7, 3) ≤ 1.1586 ≤ 1.0764², and `x3satm_cert` in the Lean library of [quantum-satisfiability-by-clauses](../quantum-satisfiability-by-clauses/#lean) proves that 1.1586 is at least the branching numbers of (7, 3), (6, 4) and (5, 5) and that 1.1586 ≤ 1.0764².

**Before.** To our knowledge, the only quantum algorithm stated for XSAT is the search over a subspace of [3], with O(2^{(n − M′)/2}) queries, where M′ is the number of linearly independent clauses. That bound is the better one only for formulas with M′ > 0.7766 n against Theorem 1 and M′ > 0.8620 n against Theorem 2 ([`bounds.log`](bounds.log)); the bounds can be combined by taking the smallest. Quantum search over all assignments takes 2^{n/2} ≈ 1.4142^n. The best classical bounds are 1.1674^n for XSAT [2] and 1.0984^n for X3SAT [5], and in terms of clauses 1.15855^m for X3SAT [7], which is τ(7, 3) = 1.158552 rounded down. To our knowledge, no quantum bound for X3SAT in terms of m has been stated. Theorem 3 is smaller than Theorem 2 whenever m < 0.6497 n ([`bounds.log`](bounds.log)).

The same approach, the walk of [1] on classical branching algorithms with polynomial space, was applied to graph colouring, domination problems and monotone local search in [6], which is the closest prior work.

## The tree for XSAT

The algorithm XSAT(ϕ) of [2] applies 14 lines in order of priority.

- **Single calls.** Lines 1 to 9 and 11 are simplification rules: each returns 0 for a clause that cannot be exactly satisfied, or fixes literals, links two literals, drops a constant, removes a subsumed clause, or applies resolution, and then makes one recursive call. Line 10 either simplifies, with one call, or branches. In the cases of Line 12 with a 1-j orientation, the rule links two literals or rewrites a clause and passes to Line 11 (Lemma 2 of [2]).
- **OR.** Lines 10, 12 and 13 branch into two calls, on x = 1 and x = 0 for a variable x or on δ = 1 and δ = 0 for a subclause δ, and return their OR.
- **Leaves.** Line 14 decides formulas in which every variable occurs at most twice in polynomial time.

So the decision procedure is a backtracking tree in the sense of [1]. Every rule removes a variable, a clause or a literal, so the depth is polynomial. The measure μ ≤ n gives each variable weight 1 or 0.8823, never increases under the rules, and every branching factor is at most 1.1674, so the tree has at most 1.1674^n · poly(n) nodes. This explicit bound is the one the walk of [1] needs. The formula is first shortened in poly(L) time: a maximal linearly independent set of the clause equations (the literals of a clause sum to 1, with x̄ = 1 − x) is kept, since every assignment that satisfies them satisfies the others. At most n + 1 clauses remain, and the length stays at most n(n + 1), since the number of clauses does not grow and simplified clauses have at most n literals. The walk then decides satisfiability in √(1.1674^n) · poly(n) time, and an assignment is found by descending the tree with the walk at each child.

## The tree for X3SAT

The X3SAT algorithm of [4, Section 3.3] reduces the formula and then branches on the first case that matches.

- **Single calls.** Reductions (1) to (8), (14) and (15) fix literals, link two literals or drop a clause; they run in polynomial time [4, Lemma 4]. Reductions (16) to (25) remove certain cycles; (19) and (23) only rewrite the formula and are applied only when the next step removes a variable or branches. Reductions (24) and (25) replace two variables by one fresh variable. So no step adds variables, and the depth is polynomial.
- **OR.** The branchings make two or three recursive calls, on x = 1 and x = 0, on x₁ = 1, x₂ = 1 and x₁ = x₂ = 0, or on a subclause C′ set to 1 or to 0, and return the OR. Every branching vector is (12, 4) or better; the others in Table 1(b) of [4] are (11, 5), (9, 6) and (8, 7).
- **Leaves.** A formula in which every variable occurs at most twice is decided in polynomial time. A formula with at most 2n/15 variables that occur three or more times is decided by enumerating their assignments, each followed by the polynomial test; in the tree this is binary branching on those variables, with at most 2^{2n/15} leaves.

So the decision procedure is a backtracking tree in the sense of [1]. Since 2^{2/15} < τ(12, 4), induction on n bounds the number of leaves by τ(12, 4)^n = 2^{0.13787 n}, as in [4, Theorem 1], and the tree has at most 2^{0.13787 n} · poly(n) nodes. The walk of [1] decides satisfiability in √(2^{0.13787 n}) · poly(n) ≤ O(1.0490^n) time, and an assignment is found by descending the tree with the walk at each child.

## The tree for X3SAT in terms of clauses

The algorithm X3SAT of [7] reduces the formula with fourteen transformation rules and then takes the first case that matches.

- **Single calls.** The rules fix literals, link two literals, replace a clause by another or remove a clause, in polynomial time; none of them adds a clause.
- **Leaves.** A formula with fewer than six clauses is decided by exhaustive search, and a formula in which every variable occurs at most twice by a perfect matching, both in polynomial time.
- **OR.** Cases 5 to 7 branch on a literal set to 1 and to 0, with the forced values propagated, and return the OR. When the connected-clauses principle of [7] applies, the branching literal is the one that a subformula of four clauses shares with the rest.
- **Components.** Case 4 splits the formula into connected components and returns the AND of the calls on them. In the tree, a node instead decides every component with fewer than six clauses by exhaustive search, answers no if one has no solution and removes them otherwise, and keeps the other components together in one formula, on which it branches at a literal chosen as in [7].

Every branching of [7, Theorem 7] is analysed on a connected simplified formula with at least six clauses and counts the clauses removed near the branching literal. In this tree the component of the branching literal is such a formula, the case that applies is the one for that component, and the other components are not changed by the branching. So every branching has a vector dominated by (7, 3), (6, 4) or (5, 5) in m, with branching number at most 1.1586, and every branch removes at least three clauses. The counting lemma with measure and height m bounds the tree by 1.1586^m · poly(m) nodes, and the walk of [1] decides satisfiability in √(1.1586^m) · poly(m) ≤ O(1.0764^m) time. A solution follows by self-reduction: fix the variables one at a time, each to a value for which the simplified formula is still satisfiable.

## Limits

- The case analyses of [2], [4] and [7] are used as stated and are not reproduced here.
- Theorem 2 uses the algorithm of [4]. The faster classical algorithm of [5] decides subformulas with up to n/2 variables inside one step (interface replacement); a quantum form of it is not treated here.
- No script runs the algorithms of [2], [4] or [7]; [`bounds.py`](bounds.py) checks only the square roots, the branching numbers quoted above and the crossovers.

## References

1. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
2. G. Hoi. An improved exact algorithm for the exact satisfiability problem. arXiv:2010.03850, 2020.
3. S. Mandrà, G. G. Guerreschi and A. Aspuru-Guzik. Faster than classical quantum algorithm for dense formulas of exact satisfiability and occupation problems. New Journal of Physics 18, 2016. arXiv:1512.00859.
4. J. M. Byskov, B. A. Madsen and B. Skjernaa. New algorithms for exact satisfiability. Theoretical Computer Science 332, 2005. BRICS Report RS-03-30, 2003.
5. M. Wahlström. Algorithms, Measures and Upper Bounds for Satisfiability and Related Problems. PhD thesis, Linköping Studies in Science and Technology, Dissertation No. 1079, Linköping University, 2007.
6. S. Senge. Polynomial-space quantum algorithms from classical branching: colouring, domination and monotone local search. arXiv:2611.12714, 2026.
7. J. Zhou and M. Yin. New worst-case upper bound for X3SAT. arXiv:1102.4926, 2011.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the scripts and the Lean formalization, and to draft the text.
