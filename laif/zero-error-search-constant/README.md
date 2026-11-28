# The optimal constant of zero-error quantum search

2026-11-26

A zero-error search algorithm must halt with probability 1 and output a marked item with certainty. Its cost is the expected number of oracle rounds. A weakly measured amplitude amplification loop [2] finds one of k marked items among N with the leading constant 1/2 + 1/π, in units of (π/4)√(N/k), and it is optimal within its family of one-checkpoint protocols [2]. With m parallel queries per round, circuits in [1] reach the same constant in units of (π/4)√(N/(mk)) for m, k powers of two up to 1024. Lower bounds of order √(N/(mk)) are known [1, 3], with constant 1/2 for m = k = 1 (implied by [3]). This folder proves that no zero-error algorithm does better than 1/2 + 1/π, and gives a protocol that reaches it for every m and k. The optimal constant is exactly 1/2 + 1/π. For finding both of two marked items with one query per round, exact certificates pin the optimum at N = 64, 256 and 1024, and for N = 256 and 1024 it lies below every strategy that finds the items one after the other.

## Setting

The setting is that of [1, Appendix E.1]. There are N items, and S is an unknown set of k marked items, with k known. The oracle O_S maps |b⟩|x⟩ to |b ⊕ [x ∈ S]⟩|x⟩. A round applies O_S to at most m disjoint registers at once. Between rounds the algorithm may apply any unitary that does not depend on S, measure, and branch on the outcomes. It must halt with probability 1 and output an element of S with certainty. The cost is the expected number of rounds on the worst-case S. A random relabelling of the items, at no query cost, makes this equal to the average over all S, so the bounds below hold for both.

Write sin θ = 1/√N and sin θ_m = √(m/N), with θ, θ_m ∈ (0, π/2].

## Results

| Quantity | Previous best bound | This folder |
|---|---|---|
| Zero-error search, k marked items known, at most m parallel queries per round: expected rounds divided by (π/4)√(N/(mk)), as N → ∞ | at most 1/2 + 1/π ≈ 0.8183 for m = 1 [2] and for m, k powers of two up to 1024 [1, Appendix E]; at least 1/2 for m = k = 1, implied by [3] | **exactly 1/2 + 1/π**, for every m and k |
| The same for one marked item and every N ≥ 2, m ≤ N | | **at least (π/4 + 1/2 − θ)/(2θ_m)** rounds |
| Optimum over algorithms with at most T rounds, m = k = 1, numerical | | 0.7811, 0.8097, 0.8161, 0.8178, 0.8182 at N = 16, 64, 256, 1024, 4096 |
| Zero-error search for both of k = 2 marked items, m = 1: optimal expected queries divided by (π/4)√N·(1 + 1/√2) | about 0.82, verified circuits [1, Appendix E]; lower bounds of order √(Nk) | **between 0.7555 and 0.7557 at N = 256, between 0.7580 and 0.7585 at N = 1024** (exact certificates, Theorem 5) |

**Theorem 1.** For one marked item, every N ≥ 2 and every 1 ≤ m ≤ N, every zero-error algorithm uses at least

  E[rounds] ≥ (π/4 + 1/2 − θ) / (2θ_m)

expected rounds. As N → ∞ with m fixed, the bound equals (1/2 + 1/π)·(π/4)√(N/m) − 1/(2√m) + o(1).

**Corollary 2.** For k marked items, let M = ⌊N/k⌋ ≥ m. Every zero-error algorithm uses at least (π/4 + 1/2 − arcsin(1/√M)) / (2 arcsin √(m/M)) expected rounds. So for fixed m and k the ratio to (π/4)√(N/(mk)) is at least 1/2 + 1/π − o(1).

**Proposition 3.** For every fixed m and k, there is a zero-error algorithm with (1/2 + 1/π)·(π/4)√(N/(mk))·(1 + o(1)) expected rounds as N → ∞. With Corollary 2, the optimal constant is exactly 1/2 + 1/π.

For m = k = 1 the bound of Theorem 1 lies about half a round below the optimum over algorithms with at most T rounds:

| N | 16 | 64 | 256 | 1024 | 4096 |
|---|---|---|---|---|---|
| Theorem 1 | 2.0435 | 4.6281 | 9.7765 | 20.0630 | 40.6311 |
| Optimum, at most T rounds | 2.4539 | 5.0875 | 10.2560 | 20.5523 | 41.1252 |
| Optimum divided by (π/4)√N | 0.7811 | 0.8097 | 0.8161 | 0.8178 | 0.8182 |

The optimum is that of a semidefinite program over the Gram matrices of all algorithms with at most T rounds (T = 24, 36, 60, 120, 220), described below. It changes by at most 10⁻⁴ when T is doubled (N ≤ 256). The unrestricted optimum lies between the two rows.

## Finding both of two marked items

Now k = 2, m = 1, and the algorithm must halt with probability 1 and output the whole set S with certainty (Find-All). The cost is the expected number of queries, worst case or, by relabelling, the average over S. A sequential strategy first runs a zero-error search that outputs one marked item y, and then a zero-error search for the other one among the N − 1 items other than y.

**Theorem 5.** The optimal expected number of queries E\*(N) of zero-error Find-All for k = 2 and m = 1 satisfies

| N | 64 | 256 | 1024 |
|---|---|---|---|
| Lower bound on E\*(N) | 7.98521 | 16.20883 | 32.52491 |
| Upper bound on E\*(N) | 7.98539 | 16.21068 | 32.54286 |
| Ratio to (π/4)√N·(1 + 1/√2) | 0.7444 to 0.7445 | 0.7555 to 0.7557 | 0.7580 to 0.7585 |
| Every sequential strategy, at least (Theorem 1, Corollary 2) | 7.7042 | 16.5181 | 34.0908 |

Lower bounds are rounded down and upper bounds up. At N = 4096 the same certificate (T = 210) gives E\*(4096) ≥ 65.09729, a ratio of at least 0.7586. For N = 256 and N = 1024 the upper bound lies below the bound for every sequential strategy, so finding the two items coherently is strictly cheaper than finding them one after the other. The sequential bound adds Corollary 2 for the first search (k = 2, M = N/2) and Theorem 1 for the second (one marked item among N − 1).

**The program.** Relabel the items at random, so the Gram matrix C_t of the not yet halted states before query t (rows and columns indexed by the 2-sets S) is invariant under all permutations of the items. Such a matrix has three coefficients in the basis J_0, J_1, J_2 of the Johnson scheme J(N, 2) (|S ∩ S'| = 0, 1, 2), its eigenvalues are explicit linear forms in them, and its diagonal coefficient is the probability of not having halted. Write the state before query t as Σ_x |x⟩|φ_{x,S}⟩ + |⊥⟩|φ_{⊥,S}⟩, with x the queried item and ⊥ a query that does nothing. Then C_t = Σ_x Γ_x + G with positive semidefinite Γ_x = (⟨φ_{x,S}|φ_{x,S'}⟩) and G. After the query, C' = Σ_x σ_x ∘ Γ_x + G, where σ_x(S, S') = −1 if x lies in exactly one of S and S'. Halting with the output S removes a diagonal part d_t·I, so C_{t+1} = C' − d_t·I is positive semidefinite. The expected cost is Σ_t (C_t)_{SS}. By the symmetry, Γ_x is a Stab(x)-invariant matrix with 7 free coefficients, and it is positive semidefinite exactly when its compressions to the isotypic components of Stab(x) on 2-sets (2 trivial, 2 standard, 1 of type (N − 3, 2)) are, which are 2 × 2, 2 × 2 and 1 × 1 matrices. The program over all T rounds thus has size independent of N.

Every algorithm gives a feasible point, and every feasible point is an algorithm: given states with Gram matrix C_t, an isometry that does not depend on S maps them to states with the decomposition Σ_x Γ_x + G (equal Gram matrices), and an isometry maps the states after the query, with Gram matrix d_t·I + C_{t+1}, to √d_t |S⟩|halt⟩ + |continue⟩|ψ_S⟩ with Gram(ψ_S) = C_{t+1}. Measuring the flag halts with the correct output.

**The certificates.** The lower bound runs the program for T rounds with C_T free, which only drops cost. Multipliers for its constraints, rational and with exact arithmetic, make the Lagrangian constant: it equals 1 − ⟨y_0, (1, 1, 1)⟩ for all primal points, and the conic multipliers are checked positive semidefinite in exact fractions, so every algorithm costs at least that much. The upper bound is a rational feasible point checked in exact fractions (positive semidefinite blocks and Johnson eigenvalues, exact equalities). The first two rounds lie on faces of the cone (all states agree before the first query, and C_1 has no (N − 3, 2) part), and the point keeps these faces exactly. After T rounds the remaining mass restarts an exact deterministic algorithm, exact amplitude amplification for one of two items and then for the last one, with R = 10, 22, 43 queries. T = 34, 60, 110.

## Proof of Theorem 1

**Normal form.** Index the rounds of each branch by its oracle calls. All operations between two rounds, including measurements and classical loops, form one S-independent instrument whose outcomes are "continue" and "halt with output z". Replace the algorithm by its random relabelling, and keep the relabelling and every outcome except halting coherent. At the start of round t, on marked item y, the part of the state that has not halted is then a vector ψ_y. Its squared norm a_t is the probability of not having halted, the same for every y, and the expected number of rounds is the sum of a_t over t ≥ 0. A permutation σ of the items maps ψ_y to ψ_σ(y) by a unitary. Hence ⟨ψ_x, ψ_y⟩ = b for all x ≠ y, and b is real, since the transposition of x and y exchanges ψ_x and ψ_y. Let ψ̄ be the mean of the ψ_y. Then ‖ψ̄‖² = (a + (N − 1)b)/N and ⟨ψ̄, ψ_y − ψ̄⟩ = 0. Define ω ∈ [0, π/2] by cos ω = ‖ψ̄‖/√a. At the start all ψ_y coincide, so a_0 = 1 and ω_0 = 0.

**Halting.** Zero error means that a halting branch on input y outputs y, so its vector lies in the subspace where the output register holds y. The halted parts for different y are therefore orthogonal and, by symmetry, have the same squared norm d. Halting lowers a by d and leaves b unchanged. In terms of u = b/a, cos²ω = 1/N + (1 − 1/N)u.

**Lemma 3 (one round).** One round changes ω by at most 2θ_m.

*Proof.* In the basis |+⟩, |−⟩ of the target qubits, O_S acts on a register as the phase (−1)^{[x ∈ S]} when the target is |−⟩ and as the identity when it is |+⟩. For S = {y}, m registers in a basis state therefore pick up the phase (−1)^{[y ∈ A]}, where A is the set of items held an odd number of times by registers with target |−⟩, and |A| ≤ m. So the round maps ψ_y to (I − 2Π_y)ψ_y with Π_y = Σ_{A ∋ y} P_A, for orthogonal projectors P_A that sum to the identity. This holds for any target states, including weak checks and targets entangled with the workspace. Hence Π_y is a projector and Σ_y Π_y = Σ_A |A| P_A ≤ m I.

Let β = ‖ψ̄‖. If β = 0 then ω = π/2 and the new angle, at most π/2, is at most ω + 2θ_m. Otherwise let δ_y = ψ_y − ψ̄ and p = mean_y ‖Π_y ψ̄‖² / β², so p ≤ m/N. The new mean ψ̄′ satisfies

  ‖ψ̄′‖ ≥ Re⟨ψ̄, ψ̄′⟩/β = β − (2/β) mean_y (‖Π_y ψ̄‖² + Re⟨Π_y ψ̄, δ_y⟩).

The δ_y have mean zero, so mean_y ⟨Π_y ψ̄, δ_y⟩ = mean_y ⟨(Π_y − p)ψ̄, δ_y⟩. By the Cauchy-Schwarz inequality this is at most (mean_y ‖(Π_y − p)ψ̄‖²)^{1/2} (mean_y ‖δ_y‖²)^{1/2} = (p(1 − p))^{1/2} β · √a sin ω. With sin²θ_p = p this gives

  ‖ψ̄′‖ ≥ √a (cos ω (1 − 2p) − 2 sin ω (p(1 − p))^{1/2}) = √a cos(ω + 2θ_p) ≥ √a cos(ω + 2θ_m)

when ω + 2θ_m ≤ π/2, so the new angle is at most ω + 2θ_m. When ω + 2θ_m > π/2 this holds trivially, since every angle is at most π/2. The round is its own inverse, so the same bound from the new state back to the old one gives the other direction. ∎

The bound is tight. At ω = 0, a round with P_A spread uniformly over the m-element sets A has Σ_y Π_y = m I, so ψ̄′ = (1 − 2m/N)ψ̄ = cos(2θ_m)ψ̄ and ω moves by exactly 2θ_m. Unitaries between rounds change neither a nor b.

**Potential.** Let K = 1/(2θ_m), c = π/4 + 1/2 − θ and ω* = π/2 − θ/2. Define h(ω) = K(c − ω) for ω ≤ ω* and h(ω) = K(c − 2ω* + ω) for ω ≥ ω*, and Φ = a·h(ω).

**Lemma 4.** (a) A round lowers Φ by at most a. (b) Halting never lowers Φ.

*Proof.* (a) h is Lipschitz with constant K, and Lemma 3 moves ω by at most 2θ_m = 1/K at fixed a. (b) At fixed b, the derivative of a·h(ω) in a is h(ω) + h′(ω)(cos²ω − 1/N)/sin 2ω. Halting lowers a, so it suffices that h(ω) sin 2ω + h′(ω)(cos²ω − 1/N) ≤ 0 on (0, π/2), with one-sided derivatives at ω*.

On (0, ω*] this reads (c − ω) sin 2ω ≤ cos²ω − 1/N. The tangent line of cot at π/4 gives cot ω ≥ 1 + π/2 − 2ω on (0, π/2), so cos²ω ≥ (π/4 + 1/2 − ω) sin 2ω = (c + θ − ω) sin 2ω. Where sin 2ω ≥ 1/√N, which on (0, ω*] means ω ≥ θ/2, this leaves θ sin 2ω − 1/N ≥ θ/√N − 1/N ≥ 0, since θ ≥ sin θ = 1/√N. For ω < θ/2 we have 2ω < θ ≤ π/4. Then cos²ω ≥ (1 + cos θ)/2 and (c − ω) sin 2ω ≤ c sin θ, so cos²ω − (c − ω) sin 2ω − 1/N ≥ F(x) with x = 1/√N and F(x) = (1 + √(1 − x²))/2 − (π/4 + 1/2 − arcsin x)x − x². F decreases on (0, 1/√2], since F′(x) ≤ 1/2 − π/4 − 1/2 + π/4 − 2x < 0, and F(1/√2) = 0.

On [ω*, π/2), c − 2ω* + ω ≤ 1/2 − π/4 < 0, and cos²ω ≤ sin²(θ/2) = (1 − √(1 − 1/N))/2 ≤ 1/N, so both terms are at most 0. ∎

**Proof of Theorem 1.** By Lemma 4, Φ_{t+1} ≥ Φ_t − a_t, so a_0 + ... + a_{T−1} ≥ Φ_0 − Φ_T. The algorithm halts with probability 1 and h is bounded, so Φ_T → 0. Hence E[rounds] ≥ Φ_0 = K c = (π/4 + 1/2 − θ)/(2θ_m). ∎

**Proof of Corollary 2.** Given one marked item among M, form N items from k copies of the M items plus N − kM dummies. A register that holds a dummy has its target swapped with a |+⟩ ancilla before the oracle call and back after it, so the dummies are never marked. The copies of the marked item are k marked items, one round on the large instance costs one round on the small one, and any marked item found names the original. An algorithm for k marked items therefore yields one for a single marked item among M, with at most the same worst-case expected number of rounds. ∎

## Proof of Proposition 3

Let the m registers hold a tuple (x_1, ..., x_m) of items and define the predicate f(x_1, ..., x_m) = parity of the number of j with x_j ∈ S. Take one logical qubit with basis states |+⟩^⊗m ± |−⟩^⊗m (normalized). A round leaves |+⟩^⊗m unchanged and multiplies |−⟩^⊗m by (−1)^f, so on the logical qubit it acts as the marking oracle of f. Any algorithm that queries a marking oracle of f therefore runs with one round per query.

For tuples drawn uniformly, f = 1 with probability p = (1 − (1 − 2k/N)^m)/2, which is known, and 1/√p = √(N/(mk))(1 + O(mk/N)). The weakly measured loop of [2, Theorem 3.1], evaluated in this oracle model as in [1, Eq. (9)], halts with a tuple with f = 1 after (1/2 + 1/π)(π/4)/√p·(1 + o(1)) expected queries, with no false positives. Such a tuple holds a marked item, and one more round, checking the m registers in parallel, finds it. ∎

## Scope

- The lower bound covers every algorithm in the setting above, with intermediate measurements, classical control and any workspace, and every N, m and k. Theorem 1 holds at every finite N. The constant 1/2 + 1/π in Corollary 2 and Proposition 3 is asymptotic in N for fixed m and k.
- Theorems 1 to 3 concern finding one marked item (Find-Any). For finding all marked items, Theorem 5 covers k = 2, m = 1 at the three values of N in its table. Its bounds are exact rational certificates, checked in exact arithmetic; the program and the realization of feasible points are proved on paper. The constant as N → ∞ is not covered.
- The optima in the table come from a semidefinite program in double precision. Lemma 3, Lemma 4 and the potential steps are also checked numerically: on random instances, through the exact one-round program, on fine grids for N up to 10⁶, and along the optimal trajectories.
- Lean 4 with Mathlib (folder `lean/`, only the standard axioms) checks Lemma 3 for every finite family of vectors in a real inner product space and every family of orthogonal projections with Σ_y ‖Π_y v‖² ≤ m‖v‖² (`angle_step`, both directions in `angle_step_abs`). Complex states are covered by viewing the complex space as a real one, with the real part of the inner product. Lean also checks the halting condition on both branches (`halting_left`, `halting_right`), Lemma 4 (`round_step`, `halting_mono`, `halting_mono'`), and the telescoping step (`lower_bound`): every trajectory of states (a_t, b_t) from a = b = 1 to a_T = 0, whose rounds move ω by at most δ and whose halting steps lower a and keep the state feasible, has π/4 + 1/2 − θ ≤ δ Σ_t a_t. On paper only: the normal form of an algorithm as such a trajectory (relabelling, the real off-diagonal b, the identity ‖ψ̄‖² = (a + (N − 1)b)/N), the limit T → ∞ for algorithms without a bound on the number of rounds, Corollary 2 and Proposition 3.
- Non-vacuity in Lean: a one-dimensional family with N = 4 and m = 1 attains the bound of Lemma 3 exactly (the angle moves from 0 to π/3 = 2 arcsin(1/2)), and exact Grover search at N = 4 is a trajectory that satisfies every hypothesis of `lower_bound`, whose conclusion has π/4 + 1/2 − θ > 0 (`cc_pos`).

## Files

- `sim/bss.py`: the semidefinite program over Gram matrices for m = k = 1. It covers all algorithms with at most T rounds, with halting, and prints the optimal expected number of queries.
- `sim/parallel.py`: the exact one-round program for at most m parallel queries (set phases with |A| ≤ m), and the largest change of ω.
- `sim/findall2.py`: the Find-All program for k = 2 (Stab(x) blocks, Johnson eigenvalues, a selftest against the dense program `sim/findall.py`).
- `sim/cert_dual.py` and `sim/cert_primal.py`: the exact lower and upper certificates of Theorem 5 (`cert_dual.py N T eps`, `cert_primal.py N T eps`; the table uses `cert_dual.py 64 34 1e-5`, `256 60 1e-6`, `1024 110 1e-7`, `4096 210 1e-7` and `cert_primal.py` with the same N, T and eps = 1e-7).
- `lean/`: the Lean library `ZeroErrorSearch` (`Basic.lean`: the scalar inequalities, the halting condition and Lemma 3; `Potential.lean`: the potential, Lemma 4 and the telescoping bound), `Axioms.lean` and its output `axioms.txt`.
- `sim/check_lb.py`: asserts for Lemma 3 (random families of vectors and the one-round program), for the halting condition of Lemma 4 (N from 2 to 10⁶), for Theorem 1 against the optimum, and for the potential along the optimal trajectories.

## References

1. S. Shirobokov et al., Discovering formally verified quantum programs with AI, arXiv:2611.09822 (2026).
2. W. Fang, C. Heunen, Weakly measured loops for quantum amplitude amplification: oracle savings and adaptive search with unknown target probability, arXiv:2609.39621 (2026).
3. C. Zalka, Grover's quantum searching algorithm is optimal, Phys. Rev. A 60, 2746 (1999), arXiv:quant-ph/9711070.

## Use of AI

The results, proofs and scripts were developed with the help of an AI system (Claude Opus 5.5), which also checked them.
