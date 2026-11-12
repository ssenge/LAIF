# Max-Cut, Max Bisection and Max 2-CSP with a quantum algorithm, in terms of the number of constraints

Written 12 Nov 2026.

Input: a Max 2-CSP instance with n variables over a fixed domain of r values, m binary constraints and integer (or rational) scores of polynomial bit length. Output: the largest total score of an assignment, and an assignment that attains it. Weighted Max-Cut, Max-DiCut and Max 2-SAT are cases with r = 2.

**Theorem 1.** Max 2-CSP has a quantum algorithm with bounded error and polynomial space in time r^{(9/100 + o(1)) m}. It runs in time r^{(7/80 + o(1)) m} if every variable is in at most 4 constraints, and in time r^{(1/10 + o(1)) n} if every variable is in exactly 3. For r = 2, including weighted Max-Cut, these are O(1.0644^m), O(1.0626^m) and O(1.0718^n).

**Theorem 2 (halving form).** Take a recursive decision procedure whose value calls are on instances of at most half the size, with a measure B that satisfies (M1) below. B may be as large at a value call as at its caller. Then the procedure has a quantum algorithm with polynomial space in time √B(x) · n^{O(log n)}.

**Theorem 3.** The same bounds hold for Max 2-CSP with a cardinality constraint, where exactly k variables take a fixed value. For r = 2 this includes Max Bisection, Min Bisection, Densest k-Subgraph and Max k-Vertex Cover.

Status: Claim. The time recursion of Theorem 2 and the constants are in Lean, with the walk as a named hypothesis. That the cited classical algorithms satisfy the conditions is argued here from their analyses.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Exact exponential algorithms, quantum | Max 2-CSP, Max-Cut, m constraints | 2^{(9/50 + o(1)) m} = 1.1329^m [3]; 2^{(7/48 + o(1)) m} = 1.1064^m with exponential space, implied by [4]; 2^{0.095 m} = 1.0681^m quantum, implied by [6], [1] | 1.0644^m | Time, bounded error, polynomial space | Claim; time recursion and constants in Lean |
| same | every variable in at most 4 constraints | 2^{(7/40 + o(1)) m} [3]; 2^{3m/32} = 1.0672^m quantum, implied by [6], [1] | 1.0626^m | As above | As above |
| same | cubic constraint graphs, n variables | 2^{(1/5 + o(1)) n} [3]; 2^{(0.1398 + o(1)) n} with exponential space [4]; 2^{n/8} = 1.0906^n quantum, implied by [6], [2] | 1.0718^n | As above | As above |
| same | Max Bisection, Min Bisection, m edges | 2^{(9/50 + o(1)) m} [3, Theorem 3.3], [11]; 2^{(7/48 + o(1)) m} with exponential space, implied by [4], [11]; 2^{m/10} = 1.0718^m quantum, implied by [6], [2], [11] | 1.0644^m | As above | As above |
| same | Max Bisection, Min Bisection, cubic graphs | 2^{(1/5 + o(1)) n} [3], [11]; 2^{(0.1398 + o(1)) n} with exponential space, implied by [4], [11]; 2^{n/8} = 1.0906^n quantum, implied by [6], [2], [11] | 1.0718^n | As above | As above |

Each base in the last column is the square root of the classical bound of [3], rounded up to the digits shown. These are best known upper bounds, to our knowledge, and not tight ones.

**Direct applications.** The walk of [6] on the tree of [1], with the components of a split processed one after another in the same tree, gives Max 2-SAT, and mixtures of OR and AND clauses on two variables, in O(2^{0.0791 m}) ⊂ O(1.0564^m) with polynomial space, from the weight w_e = 0.15819 of [1, Table 2]. The same gives the implied quantum bounds in the table. All of these are below the 2^{n/2} of search when m < 6.32 n, respectively m < 5.55 n, since m ≥ 3n/2 after the reductions of vertices of degree at most 2.

**Prior work.** The walk on backtracking trees is from [6], and the walk on computation trees, with a separate cost for each vertex, from [7]. Its Theorem 4 is the tool used here. Theorem 1 of [8] treats recursive procedures whose value calls lower the log measure by a constant factor. A quantum algorithm for exact optimization in terms of n, below 2^{n/2} under a condition on the spectrum, is in [9].

## 1. The model and Theorem 2

The model is that of [8]. A recursive decision procedure takes an instance x, with recursion depth D = poly(n). In polynomial time it goes into one of these cases. A **Leaf** answers. An **OR** node lists polynomially many children and answers their OR. An **SEQ** node runs polynomially many **value calls**, adaptively, and then answers, or makes a **tail call** and answers as it does. An optimization value is reached by thresholds, and a maximum with offsets is an OR. The OR-tree of x is reached through OR edges and tail edges. A measure B(x) ≥ 2 is computable in polynomial time.

- **(M1)** For x the input or the target of a value call, and every antichain X in the OR-tree of x, Σ_{a∈X} B(a) ≤ n^C B(x).
- **(H0)** A size |x| ∈ ℕ is computable in polynomial time, and |c| ≤ |x| for every child and tail call c of x.
- **(H2)** Every value call y at a node v has 2|y| ≤ |v|, |v| ≥ 1, and log B(y) ≤ log B(v) + C log n.

**Proof of Theorem 2.** Level j holds the instances with |x| < 2^j. Solve_{j,m} decides every x of level j with log B(x) ≤ m. It runs the walk of [7] on the OR-tree of x. A child of an OR node is computed in polynomial time. The value calls at an SEQ node v run the fixed circuit Solve_{j−1, m_v}, with m_v = log B(v) + q log n, and the tail is the single child. By (H0) every node of the tree has size at most |x|. By (H2) every value call is of level j − 1, with log measure at most m_v. So the steps and the layout are functions of the parent, as [7] requires. At level 0 there are no value calls.

Let q bound, as powers of n, the walk overhead, the number of children and calls, the depth times the constant of (M1), and the local work. Let Q_j(m) be the time of Solve_{j,m}. We show Q_j(m)² ≤ n^{2q} e^m n^{b(j+1)}, with b = 7q + 1.

A child c of v has t_c² ≤ n^q (1 + n^q Q_{j−1}(m_v)²) ≤ n^q (1 + n^{4q} n^{bj} B(v)). By (M1) at each depth, Σ_v B(v) ≤ n^q e^m, and the number of nodes is at most the same. So T′ = Σ_c t_c² ≤ e^m (n^{3q} + n^{7q} n^{bj}) ≤ e^m n^{b(j+1)}, and the walk gives Q_j(m)² ≤ n^{2q} T′. The top level is j = ⌈log₂(n + 1)⌉, so the time is √B(x) n^{O(log n)}.

Errors are reduced in place at each level by alternating projections [10], as in [8]. Only one call runs at a time, so the qubits of a level are those of the level below plus a polynomial, and there are O(log n) levels. ∎

Theorem 1 of [8] needs the log measure of a value call to drop by a constant factor, and gives a polynomial overhead. Theorem 2 needs only that the size halves. When an instance splits into independent parts, the largest part is the tail and the others are value calls, each with at most half of the vertices.

## 2. Max 2-CSP: Theorem 1

Vertices of degree 0, 1 and 2 are reduced first, in polynomial time, so n ≤ 2m/3 and n^{O(log n)} = r^{o(m)}.

**Cubic instances [3, §3].** The instance carries a separation (L, S, R) of the constraint graph, with no edge between L and R, and |L₃| ≤ |R₃| for the vertices of degree 3. The measure is

    μ = w_s |S₃| + w_{s,2} |S₂| + w_r |R₃| + w_b [|R₃| = |L₃|] + w_c [|R₃| = |L₃| + 1] + w_d log_{3/2}(|R₃| + |S₃|),

with w_s = 7/10, w_{s,2} = 3/5, w_r = 1/5 + O(ε), w_b = 1/5, w_c = 1/10 and w_d = w_b + 1. Vertices of degree at most 2 are reduced first. Then separator vertices with no neighbour on one side are moved to the other side. Then the algorithm branches on the r values of a separator vertex. This is an OR with Σ r^{μ(I_i)} ≤ r^{μ(I)}.

When S is empty and both sides are nonempty, the graph is cubic, so |L| ≤ |R|. This is an SEQ node: a value call on L, and a tail on R, which [3, Lemma 1.2] separates again, from the bisection bound of [5]. Then 2|L| ≤ |L| + |R| and μ(L) ≤ w_r |R₃| + w_d log |R₃| ≤ μ, which is (H2). When L and R are balanced, the value call has the same measure as its caller. This is why Theorem 1 of [8] does not apply and Theorem 2 does.

**General instances [2, Theorem 22].** A reduction tree is computed from the constraint graph alone, in the order of [2]. It reduces vertices of degree at most 2 and branches on vertices of degree at least 4, until the components are cubic. At a branching vertex the procedure is an OR over its r values. For each value, the remaining components are value calls, except one of largest size, which is the tail. A cubic component is handed to the cubic procedure as a tail.

The measure is n^{C′} r^{d+1}, for d the depth of [2, Theorem 22], with C′ a constant that covers the factor r^{w_d log_{3/2} n} of the cubic measure. The depth d is the largest value, over the cubic leaves below, of α m_i plus the number of branchings on the way, with α = 2/15 + O(ε). Each branching lowers d by one, and a component has d at most that of its node. By [2, Theorem 22] and [3, Theorem 3.1], d ≤ (9/50 + O(ε)) m + O(1), and d ≤ (7/40 + O(ε)) m + O(1) at maximum degree 4.

Theorem 2 then gives r^{(9/100 + O(ε)) m} n^{O(log n)} for every fixed ε > 0, which is r^{(9/100 + o(1)) m}. An optimal assignment comes by self-reduction.

## 2b. A cardinality constraint: Theorem 3

Fix a value a* of the domain. A score is now a **count table**, a map from {0, …, n} to the scores and −∞, whose entry c belongs to the partial assignments with c variables at a*. Two tables multiply by the max-plus convolution (s ⊗ s′)(c) = max_{i+j=c} (s(i) + s′(j)), and add by the entrywise maximum. Each operation takes polynomial time. Variables in no constraint are set aside first, and their table is multiplied in at the end, so the tables of the rest have length at most 2m/3 + 1 after the reductions. An instance has unary and binary scores and one nullary score τ. The unary score of a variable at a* is shifted by one count. The value table of an instance is the entrywise maximum, over all assignments, of the product of its scores, and the question is whether its entry k is at least a threshold t.

The steps of §2 are reductions of vertices of degree at most 2, merging of parallel edges, and branching on the values of a vertex. Each of them forms the new scores from the old ones by sums and maxima only. With tables, the same formulas use ⊗ and entrywise maxima, and the constraint graph changes exactly as before. In [11] the algorithms of [2] are extended in this way to polynomial scores over a ring. Here the scores are tables over the max-plus semiring. So the OR-tree, the separations and the measure are those of §2.

At a split into components, each component C other than the tail needs its whole table. Entry c is a value of the instance (C, c), found by thresholds with value calls, so there are polynomially many calls. These calls have the size and the measure of the value call on C in §2. The product of the tables of these components multiplies into τ of the tail, which is again an instance of the same kind. A leaf has no variables and answers whether τ(k) ≥ t. (M1), (H0) and (H2) hold as in §2, and Theorem 2 gives the bounds of Theorem 1.

Max Bisection takes r = 2, cut edges scored 1 and k = ⌊n/2⌋, and Min Bisection takes the negated scores. Densest k-Subgraph scores the edges with both ends at a*, and Max k-Vertex Cover scores those with at least one end at a*. The versions with at most k variables at a* take the maximum over the entries up to k. The implied quantum bounds in the table come from the walk of [6] on a plain tree with these tables and the leaf test τ(k) ≥ t, with the components of a split processed one after another. Such a tree has r to the total number of branchings, not to the depth over components. In general this number is at most m/5 [2, Lemma 4]. On cubic graphs every branching removes at least 4 vertices, the branching vertex and its three neighbours, which then have degree 2 and are reduced, so it is at most n/4.

## 3. Measurements

`sim/bounds.py` recomputes the bases and the implied bounds. It checks the weights of [3] against its constraints (8) to (24) in exact arithmetic, and the exponents 2/15 and 7/40. `sim/cardinality.py` runs the procedure of §2b with count tables: reductions of degree at most 2, branching, and splits whose smaller components return their whole table, every count at once, to the nullary score of the tail. The value calls by thresholds, the preference order of [2], the separation of [3] and domains with r > 2 are not part of the script. On 600 random instances with up to 11 variables it agrees with brute force at every count. These are bisection, densest subgraph, partial vertex cover and arbitrary integer scores, each run once with the reductions and once without, so that splits occur. Run both with `python <name>.py` in `sim/`. They exit nonzero on a failed check, and the logs are alongside.

## 4. Limits

- The bounds hold with a factor n^{O(log n)} and r^{o(m)}, for fixed r, and there is no gate count. They say nothing about instances that fit on current devices.
- The classical algorithms and their analyses [1], [2], [3], [11] are used as stated. That they satisfy (M1), (H0) and (H2) is argued here from their structure. The separation of [3, Lemma 1.2] and the preference order of [2] are used as deterministic polynomial-time steps, with fixed tie-breaking.
- Nested walks are not simulated as circuits. The walk with quantum steps rests on the argument in §1 and in [8].

## 5. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry`, `axiom` or `native_decide` in the sources. `lake env lean QuantumBranching/Axioms.lean` and `lake env lean Max2CSPAxioms.lean` print the axioms of the theorems below and of the modules of [8], in `axioms.txt`. They are only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

| Part | Theorems | Hypotheses |
|---|---|---|
| Theorem 2, time | `Setting.htime_bound`, `Setting.hsearch_valid`, `Setting.treeSqH_le`, `Setting.stepH_sq_le`, `Setting.hTime_sq` | `WalkBound` |
| Theorem 2, levels | `Setting.size_le_of_mem_nodes`, `Setting.call_size`, `Setting.calls_nil_of_size`, `Setting.call_hLevel`, `Setting.hsum_nodes_le` | |
| Constants | `maxtwosat_cert`, `maxtwocsp_cert`, `smc_weights` | |

**Assuming.** The walk bound `WalkBound`, for Theorem 4 of [7], as an inequality on real functions in the record `Primitives` of `lean/QuantumBranching/Model.lean`, as in [8]. (M1), (H0) and (H2) are fields of `Setting.HConditions`. `hsearch_valid` gives the acceptance of the walk from the semantics of the procedure, and the size and measure levels of every value call. The modules of [8] that Theorem 2 uses are included.

Theorem 3 uses the same constants.

**Not formalized.** Circuits, gate counts and the space; the walk itself; the error reduction at each level; that the classical algorithms of §2 satisfy the conditions; and the count tables of §2b.

## References

1. S. Gaspers, G. B. Sorkin. A universally fastest algorithm for Max 2-Sat, Max 2-CSP, and everything in between. Journal of Computer and System Sciences 78(1), 2012. arXiv:0906.3527.
2. A. D. Scott, G. B. Sorkin. Linear-programming design and analysis of fast algorithms for Max 2-CSP. Discrete Optimization 4(3-4), 2007. arXiv:cs/0604080.
3. S. Gaspers, G. B. Sorkin. Separate, measure and conquer: faster polynomial-space algorithms for Max 2-CSP and counting dominating sets. ICALP 2015, LNCS 9134. arXiv:1404.0753.
4. S. Gaspers. Path decompositions of sparse graphs via Gaussian sweeps and faster exponential algorithms. arXiv:2611.05146, 2026.
5. B. Monien, R. Preis. Upper bounds on the bisection width of 3- and 4-regular graphs. Journal of Discrete Algorithms 4(3), 2006.
6. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14, 2018. arXiv:1509.02374.
7. J. Vihrovs. Quantum search on computation trees. arXiv:2505.22405.
8. Vertex Cover and Independent Set with a quantum algorithm, Theorem 1. [quantum-vertex-cover](../quantum-vertex-cover/).
9. M. B. Hastings. A short path quantum algorithm for exact optimization. Quantum 2, 78, 2018. arXiv:1802.10124.
10. C. Marriott, J. Watrous. Quantum Arthur-Merlin games. Computational Complexity 14, 2005.
11. A. D. Scott, G. B. Sorkin. Polynomial constraint satisfaction problems, graph bisection, and the Ising partition function. ACM Transactions on Algorithms, 2009. arXiv:cs/0604079.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
