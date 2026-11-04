# LP-type problems with quantum queries

Sebastian Senge, Independent Researcher. Written 4 Nov 2026.

**Setting.** An **LP-type problem** is a finite set H of n constraints and a function f from subsets of H to an ordered set, with:
- monotonicity: f(F) ≤ f(G) for F ⊆ G;
- locality: if F ⊆ G, f(F) = f(G), and f(G ∪ {h}) > f(G), then f(F ∪ {h}) > f(F).

Say h **violates** S if f(S ∪ {h}) > f(S). A **basis** of S is a minimal subset with the same value as S. The **combinatorial dimension** δ is the largest size of a basis. A query returns one constraint. Everything computed from known constraints costs no queries.

Examples, with the conditions that make them LP-type: smallest enclosing ball in R^d, with f(∅) below every radius (δ = d + 1); LP with d variables, feasible, with a box and a lexicographic value (δ = d, or d + 1 if infeasibility must be handled); distance between two convex hulls and hard-margin separation (δ = d + 1 when disjoint, d + 2 otherwise). These conditions were checked on small cases, not in general.

| | Problem | Quantum queries | Classical queries | Status |
|---|---|---|---|---|
| Thm 1 | LP-type, combinatorial dimension δ | O(δ²√n log n + δ√n log^{3/2} n), capped at n, plus O(δ log n) solver calls on O(δ² + log n) constraints | n | Failure probability and expected cost in Lean, assuming Grover search and the sample sizes; the rest is a claim |
| Cor 2 | Exact smallest enclosing ball in R^d | as Thm 1 with δ = d + 1, Ω(√(nd)) | Θ(n) | Claim |
| Cor 3 | Exact LP, with a row query returning the whole row | as Thm 1 with δ = d, Ω(√(nd)) | Θ(n) | Claim |

Queries only. Each oracle call still runs t violation tests, so gate counts keep that factor.

This is a minor result.

**Earlier work.** For fixed dimension, Sadakane, Sugawara and Tokuyama (Interdisciplinary Information Sciences 8(2), 2002) give minimum enclosing ball in O(√n · min{log^d Γ · log n, log^{2d+1} n}) and fixed-dimensional LP in O(√n log^{2d−1} n). They call the ball an LP-type problem. For fixed δ, Õ(√n) for all LP-type problems should also follow from Beigi and Taghavi's Theorem 4(ii) (arXiv:1905.13095) on Sharir-Welzl: T ≈ 2^δ n, G about (ln n)^δ/δ!, giving √n · 2^{δ/2} (ln n)^{δ/2}/√δ!. This route is a claim and is not in Lean. For small δ that route has fewer logs than Theorem 1, as upper bounds. It is query complexity only.

The algorithm is Objois and Vladu's quantum Clarkson (arXiv:2510.08348), for exact LP with Õ(√n d³) row queries. Our contribution, which to our knowledge has not been stated before:

1. Polynomial dependence on δ for abstract LP-type problems, with no dependence on bit length, from the sampling lemma below.
2. d²√n in place of d³√n for exact LP, in the model where a row query returns the whole row. Objois and Vladu count calls to a one-bit oracle per solution, under which their t calls are right, so this is a change of accounting and not an error of theirs. Apers and Gribling (arXiv:2311.03215) define a row query to return the entire row. For bit-bounded LPs a cutting-plane route seems to give about d² log Γ too, so the point is independence from Γ. The lower bound is Ω(√(nd)), so d² is not known to be tight.

## 1. Facts

Call h ∈ S **extreme** in S if f(S ∖ {h}) < f(S).

**Fact 1.** S has at most δ extreme elements, since every basis of S contains all of them. If h is extreme and B ⊆ S ∖ {h} is a basis, then f(S ∖ {h}) ≥ f(B) = f(S), a contradiction.

**Fact 2.** h ∉ S violates S iff h is extreme in S ∪ {h}. This is the definition.

**Fact 3.** If no element of a set A violates S, then f(S ∪ A) = f(S). Add the elements one at a time. By locality, an element that does not violate S does not violate a superset with the same value.

**Fact 4.** If f(S) < f(H) and B is a basis of H, then some element of B violates S. Otherwise f(H) = f(B) ≤ f(S ∪ B) = f(S) by Fact 3. And if nothing violates S, then f(S) = f(H), again by Fact 3.

## 2. The sampling lemma

**Lemma 1.** Let w be non-negative weights and Z ≥ 0, and let S contain each h independently with probability p_h, where p_h = 1 if s w_h ≥ Z and p_h ≥ s w_h / Z otherwise. Let V be the violators of S. Then E[w(V)] ≤ δ Z / s. Z need not be the total weight.

*Proof.* If p_h = 0 then w_h = 0, so such h contribute nothing. Otherwise, for a set A not containing h, independence gives P[S ∖ {h} = A, h ∉ S] = ((1 − p_h)/p_h) · P[S ∖ {h} = A, h ∈ S]. By Fact 2, h violates A iff h is extreme in A ∪ {h}. Summing over A,

P[h ∈ V] = ((1 − p_h)/p_h) · P[h ∈ S and h is extreme in S].

If p_h = 1 this is 0. Otherwise w_h (1 − p_h)/p_h ≤ w_h / p_h ≤ Z / s. So E[w(V)] ≤ (Z/s) · Σ_h P[h ∈ S and h is extreme in S] = (Z/s) · E[number of extreme elements of S] ≤ δ Z / s, by Fact 1. ∎

## 3. The algorithm

Let s = 2δ² and T = ⌈12 δ ln n⌉. Keep the sets S₀, S₁, … . If n ≤ 4s, read everything. The weight of h at round t is w_t(h) = 2 to the number of τ < t such that h violates S_τ. With one query for h it is known, since the solutions S_τ are classical.

For t = 0, 1, …, T − 1:
1. Compute an estimate W̃ of W_t.
2. Draw S_t with each h independently with probability min(1, s w_t(h) / W̃), and read its constraints.
3. Solve S_t classically.
4. Search H for a violator of S_t. If there is none, output the solution of S_t.

**Sampling.** For each draw, in each round and for each estimate, take a new random function u : H → [0, 1], independent of W̃ and all earlier draws. This costs no queries, though it does cost gates. An element is marked if u(h) < min(1, s w_t(h)/W̃), and one query decides it. Find all marked elements by repeated Grover search, excluding those found. If k are marked this costs O(√(nk)) in expectation, plus O(√(n log n)) for a final "none" with error 1/n³ (de Wolf's exercise, Objois and Vladu's Claim 6). Reusing u breaks the independence that Lemma 1 needs. Objois and Vladu take the median-size sample in their Claim 5. Here the cost is bounded by truncating the whole run, which keeps independence.

**Estimating W.** W_{t+1} is between W_t and 2W_t, and W₀ = n. Draw with s′ = O(log n) in place of s, and the previous estimate in place of W̃, then let W̃ be half the Horvitz-Thompson sum over the sample. That sum is unbiased whatever the previous estimate was, so E[W̃ | past] = W_t / 2. The sampling probability is 1 if W̃ = 0. `sim/lptype.py` uses s′ = 64.

**Theorem 1.** Let δ ≥ 1. With probability at least 2/3 the algorithm outputs f(H) and a basis, using O(δ²√n log n + δ√n log^{3/2} n) queries in the worst case.

*Proof.* By Fact 4, stopping is correct. Consider first the run with no limit on queries, and suppose it has not stopped after T rounds. By Fact 4 each round has a violator in the basis B of H, and |B| ≤ δ. So some b ∈ B violates at least T/δ of the sets, and W_T ≥ 2^{T/δ}. On the other hand W_{t+1} = W_t + w_t(V_t). Lemma 1 with Z = W̃ gives E[w_t(V_t) | past, W̃] ≤ δW̃/s, so E[W_{t+1} | past] ≤ W_t (1 + δ/(2s)), with no assumption on W̃ being accurate. So E[W_T] ≤ n exp(T δ/(2s)) = n e^{T/(4δ)} for s = 2δ², and Markov gives

P[not stopped] ≤ n e^{T/(4δ)} / 2^{T/δ} = n e^{−0.443 T/δ} ≤ n^{1 − 5.3} = n^{−4.3}.

For cost: W₀ is exact, and by a Chernoff bound on the sum, which is a sum of independent terms each at most (previous estimate)/s′ or fixed, each estimate is within a constant factor of W_t in every round, with high probability, for a large enough s′. On that event every sample has O(δ² + log n) elements with high probability, and a round has expected cost O(δ√n + √(n log n)). So T rounds cost O(δ²√n log n + δ√n log^{3/2} n) in expectation. Stop the run at 10 times that many queries, and report failure. By Markov this adds error at most 1/10. It changes nothing else, as stopping only adds a failure event. Each search errs with probability at most 1/n³, and there are O(δ³ log n + δ log² n) searches on the expected path, with δ² ≤ n by the shortcut, so search errors add o(1) in total. Exact sampling and an exact "no violator" were assumed above, and the argument here is that this total variation term covers them. ∎

The Chernoff step above is argued here and not in Lean.

**Lower bounds.** Take d groups of n/d points, each point at 0, or at e_j if marked, in group j. If k groups have a marked point, then r² is 0 for k = 0, 1/4 for k = 1, and 1 − 1/k for k ≥ 2, so the radius computes the parity of the OR of each group. By adversary composition that needs Ω(√(nd)) queries, and Ω(n) randomized. For d = 1 this is plain OR.

## 4. Practical reading

`sim/check.log`, budget 16, δ = d + 1 ≤ 6. On "gaussian" and "one outlier", queries/√n grows from about 900 to 1800 at n = 2¹⁰ to about 3900 to 5800 at n = 2²⁰. Holding that flat gives a crossover with reading all n points near n ≈ 2 × 10⁷, and a fit linear in log n gives about 3 × 10⁷ to 7 × 10⁷, extrapolated beyond what was measured. On "sphere" the first sample already determines the ball, so about 210 to 300 √n queries.

## 5. Measurements

`sim/check.py`: the classical solver agrees with brute force on 2250 small inputs. Clarkson agrees with the solver on 640 of 640 runs at budget 32, d ≤ 5, n ≤ 5000, though 160 of these use the n ≤ 4s shortcut and read everything. They stopped in at most 14 rounds, and at n = 2²⁰ the rounds reach 15 to 23, growing about 1.1 to 1.3 per doubling, which is where the log comes from. In the cost table at budget 16, every output is checked by testing that no point violates it, which proves optimality as the ball is optimal on a subset. Fitted exponents at n ≤ 2²⁰ are 0.51 on "sphere" and 0.64 to 0.74 otherwise, consistent with the log factor. `sim/qiskit_check.py`: every search a circuit, 20 runs on d = 1 and n ≤ 64, 0 wrong, at most 7 qubits, 11,260 circuits. It tests the construction and shows no gain.

**Numerics.** The theorem assumes exact arithmetic. The script is floating point with tolerance 1e-7, absolute as well as relative, so its tests hold at unit scale only. The solver's agreement at other scales is not claimed here, and `sim/lptype.py` does not compute a basis, only a ball.

## 6. Limits

- Queries only. Every oracle call runs the violation tests, and sampling needs a new random function per draw, so a gate count keeps those costs and is not worked out.
- For fixed δ, Õ(√n) was already claimed in 2002 for the ball and for LP, and should follow in general from decision trees. What is left here is the polynomial dependence on δ.
- The d² bound for exact LP holds in the model where a row query returns the whole row. d² is not known to be tight.
- The constants are large: reading all points stays cheaper until n of about 10⁷ or more in the runs above.

## 7. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry` and no `axiom` declaration. `lake env lean LPType/Axioms.lean` prints the axioms of 54 theorems: only `propext`, `Classical.choice` and `Quot.sound`.

| Part | Theorems |
|---|---|
| Definitions, Facts 1 to 4 | `Problem`, `Violates`, `Extreme`, `IsBasis`, `combDim`, `fact1`, `fact2`, `fact3`, `fact4`, `fact4_of_no_violator`, `stopping_correct` |
| Lemma 1 | `lemma1`, `lemma1_general`, `prob_violator_identity` |
| Weight growth | `pigeonhole`, `exists_many_violations`, `two_rpow_le_histTotal`, `expect_potential_le_on`, `clarkson_step`, `expected_W_le`, `expected_W_le_exp` |
| Failure probability | `prob_notStopped_mul_le`, `markov_arith`, `failure_prob_le` (n^{−1.3}), `failure_prob_le_sharp` (n^{−4.3}) |
| An instance | `maxProblem`, `maxProblem_combDim`, `maxProblem_failure_prob` |
| Query counts | `queryCount_le`, `findAll_expected_cost_le`, `expected_queries_le`, `expected_queries_le_log` |
| Conditioned sampling, not used by Theorem 1 | `conditioned_step`, `failure_prob_le_redraw` |

**Assuming.** `GroverFindAll` and `GroverFindOne` in `lean/LPType/Model.lean`, on an explicit query model. `expected_queries_le` also assumes the mean sample sizes over the whole run, `hR` and `hS`, which Section 3 argues by a Chernoff bound.

**Not formalized.** The Chernoff bound on the estimates, and with it the worst-case query count after truncation. Search errors: sampling and "no violator" are exact in the Lean process. The new random function per draw is modelled only as independence. Solver call counts, the cap at n, the lower bounds, Corollaries 2 and 3, and the ball as an LP-type problem.

## References

1. K. Sadakane, N. Sugawara, T. Tokuyama. Quantum computation in computational geometry. Interdisciplinary Information Sciences 8(2):129-136, 2002.
2. É. Objois, A. Vladu. Adaptive sparsification for linear programming. arXiv:2510.08348.
3. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. arXiv:1905.13095.
4. S. Apers, S. Gribling. Quantum speedups for linear programming via interior point methods. arXiv:2311.03215.
5. R. de Wolf. Quantum computing: lecture notes. arXiv:1907.09415.
6. H. Buhrman, R. Cleve, R. de Wolf, C. Zalka. Bounds for small-error and zero-error quantum algorithms. arXiv:cs/9904019.
7. K. L. Clarkson. Las Vegas algorithms for linear and integer programming when the dimension is small. J. ACM 42(2), 1995.
8. M. Sharir, E. Welzl. A combinatorial bound for linear programming and related problems. STACS 1992.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
