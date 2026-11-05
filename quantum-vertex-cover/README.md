# Vertex Cover and Independent Set with a quantum algorithm

Written 5 Nov 2026.

Input: a graph G and a number k. Output: whether G has a vertex cover of at most k vertices, and one if it does. For Maximum Independent Set the input is a graph on n vertices, and the output a largest set of pairwise non-adjacent vertices.

**Theorem 1.** Let a recursive decision procedure and a measure B satisfy the conditions (M1) to (M3) below. Then it has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time √B(x) · poly(n). The exponent of the polynomial is fixed.

**Theorem 2.** Consequently Vertex Cover has a quantum algorithm running in time O*(1.25281^{k/2}) ⊂ O*(1.1193^k), and Maximum Independent Set one running in time O*(1.19951^{n/2}) ⊂ O*(1.0953^n), both with bounded error and polynomial space. The table below lists further cases.

Status: Claim. The counting lemmas, the semantics of the recursion, the recursion of the costs, the level scan and the table arithmetic are in Lean, with the quantum primitives as named hypotheses. That the cited classical algorithms satisfy (M1) to (M3) is argued here from their analyses.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Parameterized algorithms, quantum | Vertex Cover, parameter k | 1.25281^k randomized [7], 1.25284^k deterministic [1]; 1.175^k quantum [10]; about 1.1287^k implied by [8], [11] | 1.1193^k (1.1194^k from [1] alone) | Time, bounded error, polynomial space | Claim; lemmas and cost recursion in Lean |
| same | max degree 4 | 1.21103^k [7]; 1.21131^k [1]; about 1.1024^k implied by [8], [1] | 1.1005^k (1.1006^k) | As above | As above |
| same | max degree 5 | 1.24382^k [7]; 1.24394^k [1] | 1.1153^k (1.1154^k) | As above | As above |
| same | max degree 6 | 1.25210^k [7]; 1.25214^k [1] | 1.1190^k | As above | As above |
| Exact exponential algorithms, quantum | Maximum Independent Set | 1.19951^n [6]; 1.1488^n quantum [12]; about 1.1337^n implied by [8], [4] | 1.0953^n | As above | As above |
| same | max degree 5 | 1.17354^n [5] | 1.0834^n | As above | As above |
| same | max degree 6 | 1.18922^n [6] | 1.0906^n | As above | As above |
| same | max degree 7 | 1.19698^n [6] | 1.0941^n | As above | As above |

Each base is the square root of the smallest classical one in its row, rounded up to the digits shown. Theorem 1 gives the exact square root with a polynomial factor. A value in brackets uses only the deterministic classical analysis, without the generated rules of [7].

These are best known upper bounds, to our knowledge, and not tight ones.

**Direct applications.** The tools alone, with no value calls, give Vertex Cover above LP in O*(1.5214^μ) from [8], [2]; Vertex Cover of maximum degree 3 in O*(1.0637^k) from [16], [7], and O*(1.0697^k) from [8], [2], [3]; Independent Set of maximum degree 3 in O*(1.0375^n) from [16], [7], and O*(1.0410^n) from [8], [3]; and of maximum degree 4 in O*(1.0665^n) from [16], [7], [4], and O*(1.0666^n) from [8], [4]. To our knowledge they have not been stated before.

**Implied bounds.** The implied entries are the plain search trees confirmed here. For Independent Set, branching on a vertex of degree at least 5 gives T(n) = T(n−1) + T(n−6), of base 1.28520, above the plain tree of [4]. Older algorithms have smaller bases, such as 1.2210 in [17], which would give about 1.1050^n if its separation step can be carried with a global budget. For degree 4 in k, Proposition 28 of [1] with [4] has base 1.2152. Line 2 of Branch4 in [1] can also be replaced by setting V₃ aside and solving it last with a global budget, with a small change of the measure, and in degree 4 this keeps the deterministic base above. So Theorem 1 is what is used where the value calls of [5] at vertex cuts enter: degrees 5 and 6 in k, general Vertex Cover, and Independent Set of degree at least 5.

**Prior work.** The quantum walk on backtracking trees is from Montanaro [8], and the walk on computation trees, with a separate cost for each vertex, from Vihrovs [9], whose Theorem 4 is the tool used here. Nested search for recursive decomposition goes back to Fürer [13], and the disjunctive divide and conquer recurrence is treated in [9]. Quantum bounds for Vertex Cover and Independent Set are in [10] and [12]. The classical bounds are from the works in the table. To our knowledge, what is new here is the set of conditions under which value calls with a shrinking log measure cost only a polynomial factor in total, the level scan that puts independent parts into this form, the use of these for the measure and conquer analyses above, and the resulting bounds.

## 1. The model

A **recursive decision procedure** takes an instance x of polynomial size, with depth of recursion at most D = poly(n). In polynomial time it goes into one of these cases.

- **Leaf.** It answers yes or no.
- **OR.** It lists polynomially many children, and answers the OR of their answers.
- **SEQ.** It runs polynomially many **value calls**, adaptively, each depending on the earlier answers. Then it answers from them, or makes a **tail call** and answers as that call does.
- **Box.** It answers through a quantum subroutine in time √B(x) poly(n), as a fixed unitary.

Optimization reduces to polynomially many thresholds on a budget. A maximum with offsets is an OR in this form.

A **measure** is a function B(x) ≥ 2, computable in polynomial time. The OR-tree of x is reached through OR edges and tail edges. For a constant C:

- **(M1)** For x the input or the target of a value call, and every antichain X in the OR-tree of x, Σ_{a∈X} B(a) ≤ n^C B(x).
- **(M2)** For every value call y at a node v, log B(y) ≤ (3/4) log B(v) + C log n.
- **(M3)** For every node x, the number of nodes of the full call tree below x, through OR, tail and value edges, plus Σ B(a) over its Box nodes a, is at most n^C B(x).

**Lemma 0 (macro steps).** Let the OR-tree be cut into macro steps, each with a root r, at most s nodes, each of measure at most K B(r), and with Σ B(c) ≤ B(r) over the roots c at its lower boundary. Then (M1) holds at a root with the factor (D + 1) s K.

*Proof.* The roots at fixed macro depth j have total measure at most B(x), by induction. Each element a of an antichain lies in the macro step of a root r(a). For fixed j these elements contribute at most s K Σ B(r) ≤ s K B(x). Sum over j ≤ D. ∎

The local inequality Σ B(c) ≤ B(r) is the case s = K = 1. Branching sequences of constant depth, and amortized bonuses of bounded size, are the cases of constant s and K.

## 2. The algorithm

**The tool.** A computation tree [9] has depth D, and each vertex v is computed from its parent in t_v known steps, classical or quantum. Theorem 4 of [9] detects a marked leaf with O(√(T′D)) uses of a walk operator, for any T′ ≥ Σ_v t_v². It accepts with probability at least 1/2 with a marked leaf and at most 1/4 without. Gate counts in [9] are stated with random access gates, used only to reach the registers of one level. In the circuit model this costs a factor poly(D, width).

**Solve_m**, for every x with log B(x) ≤ m:

1. If m ≤ W log n, traverse the full call tree of x. By (M3) this is polynomial. Make it reversible by pebbling [15].
2. Otherwise run the walk on the OR-tree of x. A child of an OR node is computed in polynomial time. At an SEQ node, each value call runs the fixed circuit Solve_{m_v} with m_v = (3/4) log B(v) + q log n, for q below, and the tail is the single child, or a marked leaf child gives the answer. A Box or a Leaf gets a leaf child marked by its answer. Each child is computed, its answer copied and the rest uncomputed, so only the description of the node stays on the path, and the running call uses one shared ancilla register. The padding to m_v makes the steps and the layout functions of the parent and the index, as the walk requires.
3. Reduce the error in place, as below, and output the result.

The witness comes by self-reduction: for each vertex v, decide (G − v, k − 1), and keep the change if the answer is yes.

**Proof of the time.** Let q ≥ 1 bound, as powers of n, the walk overhead, the number of children and calls, the width of a level, and the constants above. Take W = 22q + 3 and A = 7q + 4W + 1. We show Q(m)² ≤ n^A e^m, for Q(m) the size of Solve_m.

For m ≤ W log n, (M3) gives at most τ = n^{q+W} steps, and pebbling gives τ^{1.585} polylog(τ), so Q(m)² ≤ n^{q+4W}, in polynomial space for large n.

For larger m, a child c of v has t_c² ≤ n^q (1 + n^q Q(m_v)² + B(v)), with the last term only for a Box. By (M1) at each depth, Σ_v B(v) ≤ n^q e^m, and the number of nodes is at most the same. If m_v ≤ W log n, then Q(m_v)² ≤ n^{q+4W}. Otherwise (3/4) log B(v) ≥ (W − q) log n, so B(v)^{−1/4} ≤ n^{−(W−q)/3}, and since m_v < m by W > 8q,

    Q(m_v)² ≤ n^A e^{m_v} = n^{A+q} B(v)^{3/4} ≤ n^{A+q−(W−q)/3} B(v).

So T′ = e^m (2n^{3q} + n^{5q+4W} + n^{A+5q−(W−q)/3}), and with Q(m)² ≤ n^{2q} T′, each term is at most n^{A−1} e^m since (W − q)/3 = 7q + 1. Hence Q(m)² ≤ 4 n^{A−1} e^m ≤ n^A e^m. Here A and W enter the circuit only through counters of logarithmic size and through n ≥ n₀(A, W), so q does not depend on them. ∎

The nodes of high measure gain the factor B(v)^{−1/4} from (M2), which pays for the polynomial factors of a level above W log n, and (M3) makes the cost polynomial below it. Any constant below 1 in place of 3/4 in (M2) works.

**Errors.** A step with error probability ε is within amplitude √(2ε) of the exact one, and the walk operators are block diagonal in the path, so the error of one use is a maximum over branches. With ε ≤ exp(−4L − n), for a polynomial bound L on log B, the error over the at most e^L poly(n) uses of one run is negligible, and each level reduces it afresh.

**Error reduction in place.** Side-by-side copies at each of the O(log L) levels would multiply the qubits to n^{O(log n)}. Instead use alternating projections [14]: on one register alternate the walk V, a test of its output, V†, and a test of the all-zero state, writing each outcome to a new bit. Let X_i = 1 if outcome i equals outcome i − 1, with outcome 0 = 1. The start lies in one Jordan block, so the X_i are independent with the acceptance probability p as mean. Compare their count with 3r/8, copy, and uncompute, with r ≥ 32(4L + n). Only one call runs at a time, so the qubits of a level are poly(n) plus those of the largest lower level, over O(log L) levels, so they are polynomial.

## 3. Independent parts

**Lemma 2 (level scan).** Let a node v with budget k be a disjoint union of parts with minimum budgets c_i, with answer yes if Σ c_i ≤ k. Let g_i(b) ≥ 0 bound the log measure of part i with budget b, nondecreasing in b. Suppose that Σ_i g_i(c_i) ≤ log B(v) + c₀ when Σ_i c_i ≤ k, and g_i(k − Σ_{j≠i} c_j) ≤ log B(v) + c₀ when Σ_{j≠i} c_j ≤ k. Sort the values g_i(b) into levels. While at least two parts are unsolved, take the next level m. If none is left, or 2m > log B(v) + c₀, answer no. Otherwise test each unsolved part at the budgets with g_i(b) ≤ m, in increasing order, as long as two are unsolved. The last part is the tail, with the remaining budget. Each value call has log measure at most (1/2)(log B(v) + c₀), which gives (M2) with 1/2 in place of 3/4.

A no at level m on a feasible instance would leave two parts with g_i(c_i) ≥ m, so 2m ≤ log B(v) + c₀, against the test. Lean has the budget form of this scan, with a measure linear in the budget.

## 4. Randomized subroutines

**Theorem 3.** Let a one-sided randomized algorithm follow a path of polynomial length, answering yes with probability at least 1/B(x) on a yes instance and never on a no instance. Then amplitude amplification [16] gives a quantum algorithm in time √B(x) poly(n), polynomial space.

The coins are a register, and the path is computed reversibly. Lemma 2 of [7] gives such a path, with B = 2^{μ(I)}. This gives the Box, and the rows for [7].

## 5. Application

- **Vertex Cover, [1].** Branch4 line 2 solves the subcubic part, then the rest. With g₁ the logarithm of the cheaper bound on the subcubic part and g₂ = φ on the rest, inequality (4) of [1] on the parameters of the part and the additivity of μ give the condition of Lemma 2. A solved part has budget at least 2, so a tail on the rest has log measure at most φ, as 2b ≥ α. A tail on the subcubic part exceeds B(v) by at most e^α, and it leaves Branch4 for good. The branch sequences fit Lemma 0. Dovetailing between two algorithms is replaced by a choice from their computable bounds, since the analysis uses only the minimum. The same holds for Lemma 15 of [1], whose formula d = 2c(a + b)/(a + 2c) is homogeneous of degree 1, so halving a, b, c halves d.
- **Vertex Cover above LP, [2].** Since μ is additive over components, the budget can stay global, and branching inside one component gives the same drops of μ. This is a plain search tree, and it is how the algorithm is used below Branch4.
- **Maximum Independent Set, [3] to [6].** The algorithms for degree 3 and 4 make calls of constant size, on components or reducible vertex sets, or on line graphs, all polynomial. The degree-5 algorithm of [5] has steps with value calls at a vertex cut, on G[V₁] and its variants, and a tail, with recurrences C(μ) ≤ 2C(x) + C(μ − x) and C(μ) ≤ 4C(x) + C(μ − x), up to a shift of 0.175. Take V₁ as the side of smaller measure, as its divide-and-conquer theorems allow, so x ≤ μ/2. The form 4c^{x+0.175} + c^{μ−x+0.175} ≤ c^μ is convex in x, so the ends of [w₃, μ/2] are enough, and at c = 1.17 it holds for μ ≥ 28.5. So (M2) holds. Degrees 6, 7, 8 and the general case have tail calls.
- **Randomized rows, [7].** Its subcubic rules give Theorem 3 directly. Its bounds in k use the frameworks of [1], with the randomized algorithms below them as Box leaves and value calls.

## 6. Measurements

These test the walk and the conditions on small search trees, in `sim/`, with a plain branching for Vertex Cover in `tree.py`. They do not test the bounds of Theorem 2, and they do not run nested walks as circuits.

- `weighted.py` runs the walk with t_v = 1 + B(v)^{3/8} on 27 search trees, by exact linear algebra. With a marked leaf the root has weight at least 0.500 on eigenvalue 1. Without one its weight on phases |θ| ≤ ε stays within ε²(1 + DT), reaching 0.994 of it.
- `spectrum.py` runs the walk of [8] on 76 trees of up to 339 nodes. The phase at root weight 1/4 times √(Tn) stays between 1.82 and 2.05.
- `qiskit_check.py` runs phase estimation as circuits in Aer, noiseless, at up to 13 qubits. The 8 instances with a cover accept with probability at least 0.742, and the 8 without at most 0.040. The gates are dense unitaries computed from the tree.
- `measure.py` tests (M1) for B = x^budget. On 36 trees the largest antichain sum over B(root) is 1.000 at x = 1.4656, the root of the branching vector (1, 3), and it reaches 9.566 at x = 1.1. It also runs the level scan on 180 budgets on disjoint unions, with every answer equal to brute force.
- `nesting.py` evaluates the recursion of the costs with q = C = 1, W = 25. The exponent of Q²/B stays at most 55.25 up to measure n^{800}, and stops growing. It also enumerates the alternating projections: the joint law of the X_i equals the product law to within 10⁻¹⁶.

Run each with `python name.py`, in `sim/`, with numpy and scipy, and qiskit and qiskit-aer for `qiskit_check.py`. Each exits nonzero on a failed check, and the logs are alongside.

## 7. Limits

- This is an upper bound with a fixed polynomial, and there is no gate count. The exponent of the polynomial in this argument is large, and a polynomial factor that depends on the number of calls is needed in general. So this says nothing about instances that fit on current devices.
- The classical bounds are used as stated. That their analyses give (M1) to (M3) is argued here at the level of their structure, and the individual recurrences are taken from the sources. The algorithms for degree 3, 4 and 5 were read in their technical report versions.
- The rules of [7] are generated by a program and are taken as stated, including its degree-4 framework. The rows in brackets do not depend on them.
- Nested walks are not simulated as circuits, and the walk with steps that are themselves quantum rests on the argument in §2.

## 8. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry`, `axiom` or `native_decide` in the sources. `lake env lean QuantumBranching/Axioms.lean` prints the axioms of 78 theorems: only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

| Part | Theorems | Hypotheses |
|---|---|---|
| Lemma 0, counting | `card_le_of_sum_le`, `card_lt_of_sum_le`, `FinTree.lemma0`, `FinTree.macro_sum_le`, `FinTree.sum_level_le` | |
| Semantics of the recursion | `Proc.answer_iff_marked`, `Proc.orTree_root`, `ORTree.isAntichain_levelNodes` | Box answers and value calls exact |
| Recursion of the costs | `quadratic_bound`, `inner_estimate`, `padLevel_drop`, `decrease_condition`, `decrease_sharp`, `four_terms` | Walk bound as an inequality |
| Lemma 2 | `scan_answer_iff`, `scan_tests`, `scan_rounds_le`, `value_call_log_measure`, `value_call_M2` | |
| Theorem 3, Lemma 10 of [1] | `iterations_le`, `pairing_half` | |
| Error reduction | `agree_prob`, `pathProb_eq`, `bernoulli_sum`, `reduction_error`, `amplitude_budget`, `amplitude_distance` | `ErrorReduction`, `AmplitudeError` |
| Table | `quantum_le_classical`, `table_tight_deg4`, `table_tight_mis4`, and strict inequalities for each row | |
| Theorem 1, time | `theorem1`, `Setting.time_bound`, `Setting.search_valid`, `Setting.treeSq_le`, `Setting.quadratic_bound_setting`, `qubits_levels`, `qubits_polynomial` | `WalkBound`, `Pebbling` |
| Consistency | `hypotheses_satisfiable`, `setting_satisfiable`, `M3_box_gap` | |

**Assuming.** The hypotheses are named in `lean/QuantumBranching/Model.lean`. They are inequalities on real functions in a record `Primitives`, with no circuit model: the time and acceptance of the walk for any T′ ≥ T, the error reduction, the amplitude error, and pebbling. `hypotheses_satisfiable` shows that they are consistent. (M1), (M2) and (M3) are fields of `Setting.Conditions`. In `theorem1` the time is a closed formula, shown to bound the base run and the sum of squared steps at every level, and `search_valid` adds the acceptance and the drop of the level. `quadratic_bound` proves the same bound by induction, for any cost function that meets the walk bound. `theorem1` holds for n at least some N₀, and q does not depend on n, W or A.

**Not formalized.** Circuits, gate counts and the absence of quantum random access memory; the walk itself, the known-times oracle and the shared register; Jordan's lemma and Hoeffding's inequality, where only the two-dimensional fact and the product form are proved; pebbling and its space; the link from `walkAccept` to a circuit; the link between Lemma 0 on `FinTree` and (M1) on `ORTree`; the level form of the scan; and that the classical algorithms of §5 satisfy (M1) to (M3).

## References

1. D. G. Harris, N. S. Narayanaswamy. A faster algorithm for Vertex Cover parameterized by solution size. STACS 2024, arXiv:2205.08022.
2. D. Lokshtanov, N. S. Narayanaswamy, V. Raman, M. S. Ramanujan, S. Saurabh. Faster parameterized algorithms using linear programming. ACM Transactions on Algorithms 11(2), 2014, arXiv:1203.0833.
3. M. Xiao, H. Nagamochi. Confining sets and avoiding bottleneck cases: a simple maximum independent set algorithm in degree-3 graphs. Theoretical Computer Science 469, 2013.
4. M. Xiao, H. Nagamochi. A refined algorithm for maximum independent set in degree-4 graphs. Journal of Combinatorial Optimization 34, 2017.
5. M. Xiao, H. Nagamochi. An exact algorithm for maximum independent set in degree-5 graphs. Discrete Applied Mathematics 199, 2016.
6. M. Xiao, H. Nagamochi. Exact algorithms for maximum independent set. Information and Computation 255, 2017, arXiv:1312.6260.
7. K. Clinch, S. Gaspers, T. Z. He, S. Mackenzie, T. Zhang. A faster randomized algorithm for Vertex Cover: an automated approach. arXiv:2510.09027.
8. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14, 2018, arXiv:1509.02374.
9. J. Vihrovs. Quantum search on computation trees. arXiv:2505.22405.
10. A. Jeļisejevs. Bachelor's thesis, University of Latvia, 2021. The bound O(1.175^k k^{O(1)} + n√m) is as stated in its abstract.
11. J. Chen, I. A. Kanj, G. Xia. Improved upper bounds for vertex cover. Theoretical Computer Science 411, 2010.
12. S. Dörn. Quantum complexity bounds for independent set problems. arXiv:quant-ph/0510084.
13. M. Fürer. Solving NP-complete problems with quantum search. LATIN 2008, LNCS 4957.
14. C. Marriott, J. Watrous. Quantum Arthur-Merlin games. Computational Complexity 14, 2005.
15. C. H. Bennett. Time/space trade-offs for reversible computation. SIAM Journal on Computing 18, 1989.
16. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 2002.
17. F. V. Fomin, F. Grandoni, D. Kratsch. A measure & conquer approach for the analysis of exact algorithms. Journal of the ACM 56(5), 2009.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
