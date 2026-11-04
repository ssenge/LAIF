# Global maximum of totally monotone matrices, and convex polygon diameter, with quantum queries

Sebastian Senge, Independent Researcher. Written 4 Nov 2026.

M is an r × c matrix with entries in a finite ordered set, and a query (i, j) returns M[i, j]. M is **totally monotone** if for i < i′ and j < j′, M[i, j] < M[i, j′] implies M[i′, j] < M[i′, j′]. Every inverse Monge matrix (M[i, j] + M[i′, j′] ≥ M[i, j′] + M[i′, j]) is totally monotone. The task is to find the largest entry. Write n = max(r, c). Classically this is Θ(n): SMAWK [1] reads O(r + c) entries, and Theorem 2 gives the lower bound for square matrices. Plain quantum maximum finding on all entries costs Θ(√(rc)), which is also Θ(n) for square matrices, so structure is needed.

For a totally monotone M the leftmost row maxima p(i) are nondecreasing in i. Leftmost matters: `[[1, 1], [2, 0]]` is totally monotone, and taking column 2 for row 1 would hide the maximum of row 2. So every quantum maximum finding here runs on the pair (value, −index). Minima are the same problem up to sign and column order.

| | Result | Queries | Kind | Status |
|---|---|---|---|---|
| Thm 1 | Global maximum, explicit nested search, any depth d | O(C^d √n · n^{1/(2d+2)}), so n^{3/4} at d = 1 and √n · 2^{O(√(log n log log n))} at best d | explicit algorithm | Claim. Lean has the recursion's arithmetic and the correctness of the classical skeleton |
| Thm 2 | Lower bounds, inverse Monge inputs | Ω(√n) quantum, Ω(n) classical randomized | proved below | Claim. Lean has the hard family; the OR bounds are cited |
| Thm 3 | "Is the maximum ≥ θ?" | O(√n log n) | adversary composition | Lean, assuming the two theorems of Lee et al. [2] |
| Cor | The maximum and its position | O(√n log³ n log log n) | same | Claim. Lean has the strict test, the bisection and the round count, with exact decisions |
| Thm 4 | Diameter of a convex polygon | decision O(√n log^{3/2} n), value O(√n log^{7/2} n log log n); Ω(√n) and classical Ω(n) | same | Claim. Lean has the monotonicity |

So the complexity of the maximum is Θ̃(√n), against Θ(n) classically. Theorem 3's algorithm exists through Lee et al. and is not gate-efficient as stated, and these are query counts on a noiseless model.

**Prior work.** Searches on 4 Nov 2026, in several wordings, found no quantum result on Monge or totally monotone matrix search, or on convex polygon diameter. The closest result is Õ(n^{3/4}) for the diameter of a general point set, seen only in a repository record (University of Latvia). An empty search is weak evidence. The guessing decision trees of [3, 4] do not give this on the routes I tried: see the remark in Section 3.

## 1. Lower bounds

**Theorem 2.** For h ∈ {0,1}^n let M_h[i, j] = −(i − j)² for i ≠ j and M_h[i, i] = h_i. Then M_h is inverse Monge and its maximum is OR(h). So computing the maximum needs Ω(n) classical randomized and Ω(√n) quantum queries.

*Proof.* It suffices to check adjacent 2 × 2 blocks. With D = M[i, j] + M[i+1, j+1] − M[i, j+1] − M[i+1, j], the base matrix has D = 2. Changing a diagonal entry by h ≤ 1 changes D for a block in which that entry is on the main diagonal of the block by +h, and for a block in which it is on the anti-diagonal by −h, so D ≥ 1 either way. ∎

## 2. An explicit algorithm

**Depth 0.** Search all rc cells by quantum maximum finding: √(rc).

**Depth d.** Pick k = ⌈r^{1/(d+1)}⌉ rows evenly. Compute their row maxima in bisection order: find p for the middle row on the current window, then recurse on the rows above with window [l, p] and on the rows below with window [p, u]. Bisection shares windows: at level j of bisection the windows have total width at most c + 2^j, over 2^j rows. So by Cauchy-Schwarz the level costs at most √(2^j (c + 2^j)), and the sum is O(√(k(c + k))). This leaves k + 1 row blocks with windows of widths c_i, where Σc_i ≤ c + k. Run the depth d − 1 algorithm on each block, inside a quantum search for the maximum over blocks. Blocks have known cost bounds t_i, so variable-time search costs C √(Σ t_i²), with C polylogarithmic (Ambainis, quant-ph/0609168 and arXiv:1010.4458). C must absorb three things that these citations do not state directly. The inner runs have bounded error and need error reduction and uncomputation at each level. All k row maxima must be right, which puts a log k factor on the first term. And a maximum over blocks needs more than search, since Dürr-Høyer wants a uniformly random marked item: use the prefix bisection of Section 3 instead, at polylog cost.

**Theorem 1.** The depth d cost is T_d(r, c) ≤ O(C^d) √(c + r) · r^{1/(2d+2)}.

*Proof.* Induction with a_d = 1/(2d+2), so a_0 = 1/2 matches T_0 = √(rc). T_d(r, c) ≲ √(k(c + k)) + C √(Σ_i T_{d−1}(r/k, c_i)²) ≲ √(k(c + r)) + C^d √(c + r) (r/k)^{a_{d−1}}. With k = r^{1/(d+1)}, the first term is √(c + r) r^{1/(2d+2)}, and the second has exponent (1 − 1/(d+1)) · 1/(2d) = 1/(2d+2). ∎

At d = 1 there is no nesting: compute √r row maxima, then run one maximum finding over the n^{3/2} remaining cells, for n^{3/4}. Up to that log factor, since d = 1 still needs √r correct row maxima. Choosing d ≈ √(log n / log C) gives √n · 2^{O(√(log n log log n))}.

Correctness: for x with leftmost row maxima p, the rows above the middle row have their leftmost maximum in [l, p], and those below in [p, u], by monotonicity. So each row's maximum lies in its window, and the windows contain the global maximum.

## 3. Removing the overhead

Nesting pays C per level. The adversary bound has no such loss.

**Definitions (Lee, Mittal, Reichardt, Špalek, Szegedy, arXiv:1011.3020, Definition 3.1).** Let D be a set of inputs with Δ_j[x, y] = 1 if x_j ≠ y_j and 0 otherwise. For a matrix A on D × D,

    γ₂(A|Δ) = min max( max_x Σ_j ‖u_{xj}‖², max_y Σ_j ‖v_{yj}‖² )  subject to  A[x, y] = Σ_j Δ_j[x, y] ⟨u_{xj}, v_{yj}⟩.

For f on D, put F_f[x, y] = 1 if f(x) = f(y), and 0 otherwise, and γ(f) = γ₂(J − F_f|Δ). This has constraints on **all** pairs. Their Theorem 3.4 gives Adv±(f) ≤ γ(f) ≤ 2 Adv±(f), with equality Adv±(f) = γ(f) for Boolean output. Their Theorem 1.1 gives Q(f) = Θ(Adv±(f)). So Q(f) = O(γ(f)) for every f, and γ(f) = O(Q(f)).

**Lemma A (sequential composition).** Let A: D → E, and for each a ∈ E let G_a be a function on D_a = A⁻¹(a), with h(x) = G_{A(x)}(x). Then γ(h) ≤ 2γ(A) + max_a γ(G_a).

*Proof.* Let α(x, y) = 1 if A(x) ≠ A(y), and β(x, y) = 1 if h(x) ≠ h(y). Then

    β = α + (1 − α)β − (1 − β)α.

Check: the right side equals α + β − αβ − α + αβ = β. Term 1 is J − F_A. Term 2 on a pair with A(x) = A(y) = a is J − F_{G_a}, and it vanishes on other pairs. Tagging vectors with A(x), so that vectors of different classes are orthogonal, gives a factorization of cost max_a γ(G_a). Term 3 is (J − F_A) restricted to pairs with h(x) = h(y). Tagging the factorization of J − F_A with h(x) gives this at cost γ(A). Filtered factorizations add by direct sum, and their costs add. ∎

**Lemma B (OR).** For Boolean g_1, …, g_k on D, with OR(x) = ∨_i g_i(x), γ(OR) ≤ √(Σ_i γ(g_i)²).

*Proof.* Let a_i = γ(g_i), S = √(Σ a_i²), and let (u^i, v^i) factor J − F_{g_i}, with squared norm at most a_i on each input. If some a_i = 0 then g_i is constant on D: constant 1 makes OR constant, and constant 0 can be dropped. So take all a_i > 0. If OR(x) = 0 put

    U_x = ⊕_i √(a_i) u^i_x,   W_x = ⊕_i √(a_i) v^i_x,

both of squared norm at most Σ a_i² = S². If OR(y) = 1 fix i = i(y) with g_i(y) = 1, and put T_y = a_i^{−1/2} u^i_y and V_y = a_i^{−1/2} v^i_y on block i and 0 elsewhere, both of squared norm at most 1. For OR(x) = 0 and OR(y) = 1, g_{i(y)} differs on x, y, so Σ_j Δ_j ⟨U_{xj}, V_{yj}⟩ = 1 and Σ_j Δ_j ⟨T_{yj}, W_{xj}⟩ = 1. Now use two orthogonal slots:

    OR(x) = 0:  L_x = S^{−1/2} (U_x, 0),  R_x = S^{−1/2} (0, W_x);
    OR(y) = 1:  L_y = S^{1/2} (0, T_y),   R_y = S^{1/2} (V_y, 0).

Pairs with different OR give 1 in both orders. Pairs with the same OR give 0, since their nonzero slots differ. All squared norms are at most S. ∎

**Theorem 3.** On totally monotone r × c matrices and for fixed θ, the function F(M) = [max M ≥ θ] has γ(F) ≤ (2κ + 1) ⌈log₂(r + 1)⌉ √(c + r), where κ is a constant from maximum finding. So Q(F) = O(√n log n).

*Proof.* Fix rows s..t and columns l..u, with r = t − s + 1, c = u − l + 1. Let D[s, t, l, u] be the totally monotone inputs whose leftmost maxima on rows s..t lie in [l, u]. Let F[s, t, l, u] be "some entry in rows s..t and columns l..u is ≥ θ". On this domain that is the same as some row maximum being ≥ θ. Let Γ(r, c) be the largest γ over such domains, with Γ(0, c) = 0.

Base: r = 1 is an OR of c bits, and each bit has γ = 1, so Γ(1, c) ≤ √c by Lemma B.

Step: m = ⌊(s + t) / 2⌋, A(x) = p(m). A is computed by maximum finding on [l, u], so γ(A) ≤ κ√c, using γ(f) = O(Q(f)). On D_p = A⁻¹(p) the monotonicity gives D_p ⊆ D[s, m − 1, l, p] ∩ D[m + 1, t, p, u], and

    F[s, t, l, u] = [x_{m,p} ≥ θ] ∨ F[s, m − 1, l, p] ∨ F[m + 1, t, p, u].

Restriction to a subdomain does not raise γ. Lemmas A and B give, with r₁ + r₂ = r − 1 and c₁ + c₂ = c + 1,

    Γ(r, c) ≤ 2κ√c + √(1 + Γ(r₁, c₁)² + Γ(r₂, c₂)²).

Induction with ℓ(r) = ⌈log₂(r + 1)⌉ and a = 2κ + 1: assuming Γ(r_i, c_i) ≤ a ℓ(r_i) √(c_i + r_i), where ℓ(r_i) ≤ ℓ(r) − 1, the square root is at most 1 + a(ℓ(r) − 1) √(c + r), since (c₁ + r₁) + (c₂ + r₂) = c + r. So Γ(r, c) ≤ 2κ√c + 1 + a(ℓ(r) − 1)√(c + r) ≤ a ℓ(r) √(c + r). ∎

**Corollary (the maximum, with no dependence on the value range).** Deleting rows keeps total monotonicity, so the proof of Theorem 3 applies to any subset of rows, and to the strict test "some entry > θ". Fix a random order of the rows. Let S be the rows with a maximum above the current θ. Bisect on prefixes of the order with the decision, with error reduced by a factor O(log log n). This gives the first row of S in the order, which is uniform in S, in O(log n) decisions. Read that row's maximum by maximum finding, at O(√c), and set θ to it. In expectation S halves, so O(log r) rounds suffice. The total is O(√n log³ n log log n) queries, with the position of the maximum included.

**What is explicit.** Lee et al. Theorem 4.1 turns any factorization into a query algorithm, built from reflections. So the algorithm exists and its queries are O(γ), but no time bound follows. The recursion can be walked in principle by Jeffery's subroutine composition (arXiv:2209.14146) or transducers (Belovs, Jeffery, Yolcu), which I have not worked out. `sim/check.log` evaluates the recursion on single inputs at 1.96 to 2.01 √n log₂ n from n = 64 to 4096. This checks the recursion only, and the constant κ is unknown.

**Remark (decision trees).** Lin and Lin's O(√(TG)) theorem (arXiv:1410.0932) and Beigi and Taghavi's generalized form (arXiv:1905.13095) do not give this on the routes I tried. SMAWK has T = O(n), but its comparisons have no strong predictor, so G is of order n and √(TG) is of order n. The flat scheme has G of order √n log n but T of order n^{3/2}, which also gives n. A tree with T = Õ(n) and G polylogarithmic would give Õ(√n), and I did not exclude one.

## 4. Convex polygon diameter

**Input.** The vertices v_0, …, v_{n−1} of a strictly convex polygon, counterclockwise, in an array. A query returns one vertex. Task: largest distance between two vertices.

**Monotonicity.** Split the vertices into two arcs a_1, …, a_s and b_1, …, b_t, consecutive around the polygon, with M[i, j] = |a_i b_j|. For i < i′ and j < j′, the segments a_i b_j and a_{i′} b_{j′} are the diagonals of the convex quadrilateral a_i, a_{i′}, b_j, b_{j′}, so they cross at some P. Then

    |a_i b_j| + |a_{i′} b_{j′}| = |a_i P| + |P b_j| + |a_{i′} P| + |P b_{j′}| ≥ |a_i b_{j′}| + |a_{i′} b_j|,

so M is inverse Monge. Squared distances compare the same way within a row, so they are totally monotone, and they stay integers on integer coordinates.

**Theorem 4.** The diameter decision has γ = O(√n log^{3/2} n), so Q = O(√n log^{3/2} n). The diameter itself costs O(√n log^{7/2} n log log n). Ω(√n) quantum and Ω(n) classical queries are needed.

*Proof.* Halve the vertex sequence recursively. Every pair is separated at exactly one node of the recursion, where it appears in a matrix for two arcs of sizes s + t = n/2^ℓ. There are 2^ℓ such matrices at level ℓ. One matrix query is two vertex queries, or four with uncomputation, so the query complexity in the vertex model is at most 4 times that of Theorem 3, and since γ = O(Q) each matrix has γ ≤ O(log n) √(n/2^ℓ) in the vertex model. Lemma B over all matrices gives squared cost O(log² n) Σ_ℓ 2^ℓ · n/2^ℓ = O(n log³ n).

Lower bound: take n/2 antipodal pairs of rational points on a circle of radius R, which are in strictly convex position, so all these pairs have distance 2R and no other pair exceeds it. Take one vertex v from each pair and move it to (1 + ε)v when its bit is 1. For small enough ε this keeps strict convexity, since that is an open condition on finitely many points, and a moved vertex has distance (2 + ε)R from its antipode. So the decision [diameter > 2R] computes OR of n/2 bits.

For the value, run the prefix bisection of Theorem 3's corollary on the vertices. A prefix P restricts each matrix to the pairs with an endpoint in P, which is two submatrices, both totally monotone, at the same cost bound. When bisection returns a vertex, read its farthest vertex by maximum finding, at O(√n). ∎

## 5. Practical reading

Asymptotics only. `sim/grover_law.log` gives 35 n^{3/4} (monge) to 51 n^{3/4} (hard1) oracle applications at n = 2048 for d = 1, at a budget of 16 per search. SMAWK, measured in `sim/smawk.log`, reads 3.5n to 5n entries, so the quantum algorithm wins only above n of order 10⁴. Deeper nesting at C = 4 only beats plain search around n ≈ 2000 (`sim/check.log`).

## 6. Measurements

`sim/check.py`: 1500 runs of the depth d algorithm agree with brute force; polygons agree with brute force and rotating calipers on 144 runs; the hard family stays inverse Monge. `sim/grover_law.py`: exact Grover statistics, d = 1, with no wrong answers at budget 16 and above in the runs of `grover_law.log`. `sim/qiskit_check.py`: every search a circuit, at most 8 qubits, 30 runs, 0 wrong.

## 7. Limits

- Queries only. Neither a gate count nor a running time follows for Theorem 3 and its consequences. The explicit algorithm of Section 2 stops at n^{1/2+o(1)}, and its C is polylogarithmic and not computed.
- The constant κ of Theorem 3 is unknown, so the log factors say nothing at practical sizes.
- Classically SMAWK reads only 3.5n to 5n entries in the runs here, so the depth 1 algorithm wins only above n of order 10⁴, by extrapolation, on a noiseless model.

## 8. Importance

Totally monotone search is a standard classical tool (SMAWK is used for all-farthest-neighbours in convex polygons, and for many dynamic programs). This shows that the maximum of such a matrix, which has no fast generic quantum search on all its entries, needs only Θ̃(√n) queries. It is a query result, and I do not know of an application that gains in time.

## 9. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry`. `lake env lean Monge/Axioms.lean` prints the axioms of 45 theorems: only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

**Proved outright**
- Total monotonicity: `InverseMonge.totallyMonotone`, `TotallyMonotone.rowMax_monotone`, `TotallyMonotone.window`.
- The hard family: `hard_inverseMonge`, `hard_isGreatest`, `hard_entry_eq_of_bit_eq`.
- The classical skeleton of the algorithm: `globalMax_spec`, with width sums `levelCost_le`, `totalCost_le`.
- Polygons: `arc_inverseMonge`, `arc_sq_totallyMonotone`, `diagonals_cross`.
- Filtered γ₂: Lemma A (`gam_seq_le`), Lemma B (`gam_or_le`), the recurrence (`recurrence_solution`), and `theorem3_gamma` on γ.
- The corollary's round count: `mean_rounds_le`, `maximum_mean_cost`.
- The arithmetic of Theorem 1: `expo_step`, `nested_bound`.

**Assuming** (named hypotheses in `lean/Monge/Model.lean`, passed as arguments)
- `LeeQueryAdv C`: Lee et al. Theorem 1.1, Q = Θ(Adv±).
- `LeeAdvGamma`: Lee et al. Theorem 3.4.
- `DurrHoyer κ₀`: leftmost maximum on c positions costs at most κ₀√c.
- `NestedStep C T`: the recursion for T in Theorem 1's arithmetic.

With these, `theorem3_query_le` and `theorem3_sqrt_log` give Q ≤ K√n log₂ n, with K independent of r, c, alphabet and θ.

**Not formalized.** `queryQ` and `advPM` are concrete definitions, but no proof unfolds them, so whether they match the literature rests on reading them. The hypotheses are not proved consistent. The corollary as a `queryQ` theorem is missing: error reduction, adaptive composition and the step from mean to worst case. So are the quantum algorithm and variable-time search of Theorem 1, the OR lower bounds of Theorem 2, and Theorem 4 apart from its monotonicity.

## References

1. A. Aggarwal, M. Klawe, S. Moran, P. Shor, R. Wilber. Geometric applications of a matrix-searching algorithm. Algorithmica 2, 1987.
2. T. Lee, R. Mittal, B. Reichardt, R. Špalek, M. Szegedy. Quantum query complexity of state conversion. FOCS 2011. arXiv:1011.3020.
3. C. Y.-Y. Lin, H.-H. Lin. Upper bounds on quantum query complexity inspired by the Elitzur-Vaidman bomb tester. CCC 2015. arXiv:1410.0932.
4. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. Quantum 4, 2020. arXiv:1905.13095.
5. A. Ambainis. Quantum search with variable times. STACS 2008. arXiv:quant-ph/0609168. Variable time amplitude amplification and quantum algorithms for linear algebra problems. STACS 2012. arXiv:1010.4458.
6. S. Jeffery. Quantum subroutine composition. arXiv:2209.14146.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
