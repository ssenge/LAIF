# Minimum degree with quantum cut queries: a tight bound for integer weights

Sebastian Senge, Independent Researcher. Written 3 Nov 2026.

In [1] it is conjectured that computing the minimum degree of a simple graph requires Ω(√n) quantum cut queries. This file proves the bound for integer-weighted graphs with weights of O(n² log n) bits. The simple-graph question stays open.

| # | Result | Status |
|---|---|---|
| 1 | Ω(√n) quantum cut queries for exact minimum degree, integer weights of O(n² log n) bits | proved below |
| 2 | Ω(√n) for the global minimum cut value at the same weight scale | corollary |
| 3 | Sparsity lemma for near-solutions of the cut relations | proved below |
| 4 | Ω(√n) in the modular model, weights in Z_M with the oracle returning the cut mod M, M = 2^k ≥ 4 | proved below |
| 5 | n/5 − 2 classical randomized cut queries on the same kind of family, so a Θ(√n) against Θ(n) separation | proved in Section 10 |
| 6 | Ω(n/log n) classical randomized cut queries on simple graphs, by a reduction from set disjointness | proved in Section 10 |

`sim/check_lower_bound.py` tests the lattice identities and the expansion exactly on small instances. Its sparsity tests are weak: sizes are small, the degree bounds of Section 4 are never tight there, and near-solutions are only rounded exact solutions, so τ is never stressed. The proof is what carries the bound. Section 9 states which steps are machine-checked in Lean. Theorem 1 itself is not.

## Model

The vertex set is V with |V| = n, E is the set of unordered pairs, and a graph is a vector A ∈ Z_{≥0}^E. For x ∈ {0,1}^n let δ_x ∈ {0,1}^E be the indicator of the pairs separated by x, so that cut_A(x) = ⟨A, δ_x⟩. Let N exceed the largest cut value in the input class. A query is the unitary

    |x, z⟩ → exp(2πi z cut_A(x) / N) |x, z⟩,   z ∈ Z_N.

A Fourier transform on the second register turns this into |x, y⟩ → |x, y + cut_A(x) mod N⟩, so the two forms are equivalent. An algorithm with any other answer register is simulated with two queries of this form per query, by computing into a fresh register and uncomputing. This changes T by a factor of at most 2, and below T counts queries of the form above. Unitaries that do not depend on A act between queries.

‖θ‖ denotes the distance from θ to the nearest integer, and elements of R/Z are treated with this norm.

**Theorem 1.** A quantum algorithm that computes the minimum degree with error at most 1/3 on all n-vertex graphs with integer weights in [0, 2^{Cn² log n}], for a suitable constant C, makes Ω(√n) queries.

Quantum minimum finding over singleton cuts gives the matching O(√n) upper bound, as noted in [1].

## 1. The hard family

**Lattice basis.** For a pair {u,v} with u, v ≠ 0 and {u,v} ≠ {1,2}, let

    b_uv = e_uv − e_0u − e_0v + e_01 + e_02 − e_12.

Write deg for the degree map, deg(A)_v = Σ_w A_vw. Then deg(b_uv) = 0. There are J = C(n,2) − n such vectors, which is the rank of ker deg. Each b_uv is the only one containing e_uv, with coefficient 1, so they form a Z-basis of ker(deg) ∩ Z^E: subtracting the right multiples leaves a kernel vector supported on the star of 0 and e_12, and that vector is 0.

**Decomposition.** Take F ∈ (R/Z)^E. Choose β_0 with 2β_0 = F_01 + F_02 − F_12 and set β_v = F_0v − β_0 for v ≠ 0. Then, in R/Z,

    F_uv = β_u + β_v + ε_uv,   with ε_uv = ⟨b_uv, F⟩ when b_uv is defined and ε_uv = 0 otherwise. (1)

**Degree shifts.** For each v fix two other vertices a, c and let B_v = e_va + e_vc − e_ac. Then deg(B_v) = 2e_v. By (1), ⟨B_v, F⟩ = 2β_v + ⟨B_v, ε⟩ in R/Z, so ‖⟨B_v, F⟩ − 2β_v‖ ≤ 3 max_e ‖ε_e‖.

**The input.** Let G = lcm(1, …, n), so log G = O(n). For h ∈ {0,1}^n and a ∈ Z^J let

    A(h, a) = W₀·1 + G Σ_v h_v B_v + Σ_j a_j b_j.

Every vertex has degree (n−1)W₀ + 2G h_v, so the minimum degree is (n−1)W₀ unless h = 1^n.

**The distribution of a.** Fix η ∈ (0, 1/2]. Let φ(θ) = max(0, 1 − ‖θ‖/η), and draw the a_j independently from

    f(a) = ∫_{−1/2}^{1/2} φ(θ) e^{−2πi aθ} dθ = η (sin(πηa) / (πηa))²,

with f(0) = η. This is a probability distribution on Z with E e^{2πi aθ} = φ(θ) for all θ. Since f(a) ≤ 1/(π²ηa²), taking L = ⌈100J/η⌉ gives Pr[∃j: |a_j| > L] < 1/100.

**Sizes.** The entries of each b_j and B_v lie in {0, ±1}. Put W₀ = JL + nG, so that weights lie in [0, W_max] with W_max = 2JL + 2nG whenever all |a_j| ≤ L. For small η this is at most 3JL. Take N = n²·3JL. Then b := ηN ≤ 100 n⁶ for all small η, a bound that does not depend on η.

The oracle formula makes sense for every a ∈ Z^J, inside or outside the range. If a is out of range the algorithm has no correctness guarantee, but its acceptance probability is still in [0,1].

## 2. Expansion over labels

A path p fixes the query basis states (x^s, z^s), s = 1..T, and an output basis state. The final state of the algorithm on input A is Σ_p α_p exp(2πi⟨A, F_p⟩) |end(p)⟩, with F_p = Σ_s (z^s/N) δ_{x^s}. Let θ(F) = (⟨b_j, F⟩)_j ∈ Γ := (N^{−1}Z/Z)^J. Then

    P(h) := E_a Pr[accept on A(h,a)] = Σ_{p,p'} α_p ᾱ_{p'} exp(2πi⟨A(h,0), F_p − F_{p'}⟩) Π_j φ(θ_j(F_p − F_{p'})),

summing over pairs with the same accepting end. Hence

    P(h) = Σ_{u ∈ U} φ(u) K_u(h),   φ(u) = Π_j φ(u_j) ∈ [0,1],

where U ⊆ Γ is the set of labels with all ‖u_j‖ ≤ η that occur as θ(F_p − F_{p'}), and K_u(h) collects the pairs with label u. There are at most (2b+1)^J labels.

**Each |K_u(h)| ≤ 1.** Consider the unitary evolution on the algorithm's space tensored with C[Γ], where a query acts as |x,z⟩|θ⟩ → exp(2πi z⟨A(h,0), δ_x⟩/N) |x,z⟩|θ + (z/N)θ(δ_x)⟩. Starting at θ = 0 it produces a unit vector Ψ_h, and K_u(h) = ⟨Ψ_h| Π_acc ⊗ S_u |Ψ_h⟩ for the shift S_u on C[Γ]. Both factors have norm at most 1.

## 3. Sparsity lemma

**Lemma 2.** Let F = Σ_{s=1}^R t_s δ_{x^s} with t_s ∈ R/Z and x^s ∈ {0,1}^n. Suppose ‖⟨b_j, F⟩‖ ≤ η for all j. Let m ≥ 1 and let G be a multiple of lcm(1, …, m). Put τ = G·4n^{2n+4}·η. Then

    #{v : ‖G⟨B_v, F⟩‖ > τ} ≤ 1 + (R+1)(1 + log n / (2 log(m+1))).

For m = n the right side is at most 1 + (3/2)(R+1). For η = 0 the set on the left is exactly {v : G⟨B_v, F⟩ ≠ 0}.

*Proof.* Let φ_v = Σ_s t_s x^s_v and H_s = 2t_s, and let c_v = (x^s_v)_s ∈ {0,1}^R. Since (δ_x)_uv = x_u + x_v − 2x_u x_v, for u ≠ v we get Σ_s H_s c_v(s) c_u(s) = φ_u + φ_v − F_uv. Write ⟨c_u, c_v⟩_H for that form, and γ = φ − β with β from (1). Then

    ⟨c_u, c_v⟩_H = γ_u + γ_v − ε_uv (u ≠ v),   ⟨c_v, c_v⟩_H = 2φ_v.

Fix the base vertex 0. Let y_v = c_v − c_0 ∈ {0,±1}^R, and let ŷ_v = (y_v, 1) ∈ Z^{R+1}. Extend the form by Ĥ = (H, −2β_0) on the last coordinate. A direct expansion gives, for u, v ≠ 0,

    ⟨ŷ_u, ŷ_v⟩_Ĥ = −ε_uv + ε_u0 + ε_v0 (u ≠ v),   ⟨ŷ_v, ŷ_v⟩_Ĥ = 2β_v + 2ε_v0.

By (1), ε_v0 = 0 for all v. So off-diagonal entries are −ε_uv, of norm at most η, and the diagonal is exactly 2β_v.

Let Y be the set in the lemma without the vertex 0, and let r = |Y|. Let K ⊂ Z^Y be the lattice of integer dependencies among (ŷ_v)_{v∈Y}, and let ρ ≤ R+1 be the rank of these vectors, so that κ := rank K = r − ρ. If κ = 0 we are done, so let κ ≥ 1.

*Size of K.* K is a saturated lattice, so det K equals the determinant of the saturated lattice K^⊥ ∩ Z^Y. That lattice contains the lattice spanned by ρ independent rows of the matrix (ŷ_v), whose rows have entries in {0,±1} and norm at most √r. So det K ≤ r^{ρ/2} ≤ n^{n/2}. By Minkowski's second theorem, with λ_i ≥ 1 for a sublattice of Z^Y, the largest successive minimum is at most κ^{κ/2} det K ≤ n^n. A lattice has a basis with ‖b_i‖ ≤ max(1, i/2) λ_i, a standard consequence (see Cassels, An Introduction to the Geometry of Numbers). So K has a basis λ^{(1)}, …, λ^{(κ)} with ‖λ^{(i)}‖₂ ≤ n^{n+1}, hence ℓ₁ norm at most n^{n+2}.

*Divisibility.* For λ ∈ K and u ∈ Y, pairing Σ_v λ_v ŷ_v = 0 with ŷ_u gives

    ‖λ_u · 2β_u‖ ≤ ‖λ‖₁ η.

Let g_u be the gcd of λ^{(i)}_u over i, with g_u = 0 if all vanish. Integers a_1, …, a_κ of absolute value at most A have gcd g = Σ c_i a_i with Σ|c_i| ≤ 2κA + 1: take a_k of largest absolute value, reduce each c_i with i < k into [0, |a_k|/g) and compensate in c_k. This gives ‖g_u · 2β_u‖ ≤ (2κ n^{n+1} + 1) n^{n+2} η ≤ 3 n^{2n+4} η. If 1 ≤ g_u ≤ m then g_u divides G, so ‖G · 2β_u‖ ≤ G · 3n^{2n+4} η, and by the Degree shifts bound ‖G⟨B_u, F⟩‖ ≤ τ. That contradicts u ∈ Y. So every u ∈ Y has g_u = 0 or g_u ≥ m+1.

*Counting.* Let B be the κ×r matrix with rows λ^{(i)}. It has a nonzero κ×κ minor on some column set I. Column u is divisible by g_u, so all g_u on I are nonzero and hence at least m+1, and the minor has absolute value at least (m+1)^κ. By Cauchy-Binet, det K ≥ (m+1)^κ. Together with det K ≤ r^{ρ/2} this gives κ ≤ ρ log r / (2 log(m+1)), so r ≤ (R+1)(1 + log n / (2 log(m+1))). Adding back vertex 0 gives the bound. ∎

The factor G is there only to remove the logarithm. With G = 1, Lemma 2 still applies with m = 1 and the theorem loses a factor of log n. The bit length of the weights hardly changes, because J log b dominates it.

Dyadic t_s can approximate any rational, for example 1/3, and then F is close to an exact solution modulo 3. So near-solutions over Z_N behave like solutions over all of Q/Z, which is why the proof does not stop at the 2-rank of Z_{2^k}.

The kernel K can be nonzero. An exact instance has n = 13, N = 12, R = 60, r = 12, ρ = 11 and K spanned by (3,3,3,−3,−3,−3,2,2,2,−2,−2,−2).

**Exact 2-group case.** If all ⟨b_j, F⟩ = 0, G = 1 and N is a power of 2, then every nonzero 2β_u has 2-power order, so every λ ∈ K has λ_u even for all u ∈ Y. A saturated lattice inside 2Z^Y is 0, so K = 0 and r ≤ R+1.

## 4. Low-degree polynomial

Fix T. For u ∈ U fix one pair with that label and call its difference F_u, which has at most 2T terms. Any pair (p, p') with label u has F := F_p − F_{p'} with F − F_u of at most 4T terms and θ(F − F_u) = 0. So

    K_u(h) = exp(2πi Σ_v h_v φ_{u,v}) q_u(h),   φ_{u,v} = G⟨B_v, F_u⟩ mod 1.

Here q_u collects the rest. By Lemma 2 with η = 0 and m = n, each pair depends on at most 6T + 3 of the h_v, and for h_v ∈ {0,1} each factor equals 1 + h_v(e^{2πiG⟨B_v, F − F_u⟩} − 1). So q_u is a multilinear polynomial of degree at most 6T + 3, and |q_u(h)| = |K_u(h)| ≤ 1 on the cube.

By Lemma 2 with the given η and R = 2T, the set Y_u = {v : ‖φ_{u,v}‖ > τ} has at most 3T + 3 elements. Define

    P̃(h) = Σ_{u∈U} φ(u) q_u(h) Π_{v∈Y_u} (1 + h_v(e^{2πi φ_{u,v}} − 1)).

Then deg P̃ ≤ 9T + 6, and reducing with h_v² = h_v makes it multilinear without raising the degree. On the cube

    |P(h) − P̃(h)| ≤ Σ_{u∈U} |exp(2πi Σ_{v∉Y_u} h_v φ_{u,v}) − 1| ≤ (2b+1)^J · 2πnτ.

Since b ≤ 100n⁶ does not depend on η, we can pick η with log(1/η) = O(n² log n) so that this is at most 1/100. This is where the large weights come from: W_max and N are 1/η times a polynomial in n.

## 5. Proof of Theorem 1

Let the algorithm accept when it reports (n−1)W₀. With probability at least 0.99 over a, the input is in range. So P(h) ≥ 0.66 if h ≠ 1^n and P(1^n) ≤ 0.35. Q = Re P̃ is a real multilinear polynomial with Q ∈ [−0.01, 1.01] on the cube, Q ≥ 0.65 for h ≠ 1^n, and Q(1^n) ≤ 0.36. After rescaling to [0,1] and composing with 3x² − 2x³, which triples the degree, Q approximates AND_n within error below 1/3. The approximate degree of AND_n is Θ(√n) [2, 3], so 3(9T + 6) = Ω(√n). ∎

## 6. Corollaries and the modular model

**Global minimum cut.** Take a graph A on V, and let V' = V ∪ K' with |K'| = n. Join all pairs inside K' and across (V, K') with weight W* = n W_max. A cut query on this graph takes one query on A plus known numbers. The calculation of Appendix D in [1], scaled by W*, shows each non-singleton cut and each singleton of K' has value at least (2n−1)W*, while a singleton v ∈ V has value d_v + nW*. Since d_v ≤ (n−1)W*, the minimum cut value is δ(A) + nW*. So the global minimum cut value of weighted graphs needs Ω(√n) quantum cut queries at this weight scale. In [1] it is asked whether o(n) quantum cut queries suffice for this problem, and this does not answer that.

**Modular model.** Let the weights lie in Z_M and the oracle return the cut mod M, with M = 2^k ≥ 4. Fix c with nc even. Promise: every degree mod M lies in {c, c+2}. Task: decide whether some vertex has degree c. Take G = 1, replace W₀·1 by a fixed graph A₀ with deg(A₀) = c·1, which exists because deg maps onto the vectors of even sum, and draw a uniformly from Z_M^J. Then φ is the indicator of 0, so U = {0} and P is exactly a polynomial in h. A pair has R ≤ 2T terms, so the exact 2-group case gives deg P ≤ 2T + 2, and T = Ω(√n). No large weights are needed. The shift has to be even and nonzero mod M: an odd degree difference would show up in the parities, which one query reads by Bernstein-Vazirani, and for M = 2 a shift of 2 is invisible.

## 7. Limits

- **Simple graphs are not covered.** The question in [1] is about simple graphs. Weights here have Θ(n² log n) bits, and no reduction from these weights to simple graphs on poly(n) vertices is known to me. A blow-up has to answer queries that split blocks, and those are not cut queries on the original graph.
- **What breaks for small weights.** For W = O(1) the box ‖u_j‖ ≤ η covers a constant fraction of the circle, φ no longer forces F close to Im C + Z^E, and the union over labels in Section 4 is far too large. The bound Σ_u |K_u(h)|² ≤ 1 from Parseval only halves the exponent in (2b+1)^J.
- **Weight scale.** I did not try to minimize the bits. Using fewer than J hidden directions would shorten them, but a sublattice weakens Lemma 2, and getting to poly(n) values would need a different argument for the error term.
- **Consistency with known upper bounds.** The gap 2G is far below any weight scale visible to approximate degrees, so polylog(n) approximation of the minimum degree [4] is not contradicted. Degree parity costs one query, and all degrees here have fixed parity.

## 8. Importance

Modest. It settles a weighted variant of a conjecture in [1] with a tight bound, using a short argument. The stated simple-graph version remains open, and the weights are far larger than anything an application would use. To our knowledge the integer-weighted lower bound is new. The classical results add little: Proposition 8 is elementary and may well be folklore, although I have not seen it stated, and Theorem 7 only removes its log factor, for huge weights.

## 9. Formal verification

The files `lean/CutQuery/Core.lean`, `lean/CutQuery/Counting.lean` and `lean/CutQuery/Classical.lean` are checked with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. They contain no `sorry`, and every theorem listed in `lean/CutQuery/Axioms.lean` uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). To build them, run `lake exe cache get` and `lake build` in `lean/`.

**Machine-checked:**

| Paper step | Lean theorem |
|---|---|
| Decomposition (1) | `decomposition` |
| Form identities of Lemma 2 | `pr_yhat`, `pr_yhat_offdiag`, `pr_yhat_diag` |
| Divisibility, exact and near | `smul_diag_eq_zero`, `norm_smul_diag_le`, `near_divisibility`, `norm_smul_of_dvd` |
| Exact 2-group case of Lemma 2, in full: r ≤ R+1 | `dep_eq_zero_of_two_power`, `exact_sparsity_two_group` |
| Bézout with Σ\|c_i\| ≤ 2κA + 1 | `bezout_bounded` |
| A nonzero minor with divisible columns is at least ∏\|g_u\| | `prod_abs_le_abs_det` |
| Nullity from (m+1)^{2κ} ≤ r^ρ | `two_mul_le_of_pow_le`, `mul_log_le_of_pow_le` |
| Polynomial and error bound of Section 4, as a statement about given q_u, Y_u | `polynomial_assembly` |
| Lemma 3 | `invisible_change`, `invisible_degree` |
| Lemma 4: character step, ε = 0 and G · 2β_u ≠ 0 from G w^u ∉ Λ | `exists_character_of_notMem`, `exists_forms` |
| Lemma 4: the injection and (n+1)^κ ≤ \|det M\| for cut queries, given the block M | `prod_le_natAbs_det`, `visible_count`, `lemma4_count` |
| Lemma 4 with \|det M\| ≤ ρ! in place of Hadamard: r ≤ 2ρ, weaker than r ≤ (3/2)ρ | `card_le_two_mul` |
| Lemma 5: rounding along the kernel | `round_solution`, `round_solution_mulVec` |
| Lemma 6: the pointwise telescoping, the final sum, ξ ≤ 0.007 | `prod_sub_le`, `geom_le`, `xi_value` |
| Theorem 7: averaging over v and the final constants | `average_visible`, `classical_constants`, `queries_of_ratio` |

**On paper only:**

- In Lemma 2: det K = det(K^⊥ ∩ Z^Y) ≤ r^{ρ/2}, Minkowski's second theorem and the short basis, and the Cauchy-Binet step det K ≥ (m+1)^κ. Lemma 2 for η > 0, and for general G, is therefore not machine-checked as a whole.
- Section 1: the Fejér distribution and its characteristic function, the tail bound, the sizes of W₀, N and b.
- Section 2: the quantum model, the label expansion and |K_u(h)| ≤ 1.
- Section 4: the hypotheses of `polynomial_assembly`, namely that q_u is a polynomial and is bounded, and the step to the real part.
- Section 5: the approximate degree of AND_n, which enters as a cited theorem.
- Section 6: the corollaries.
- Section 10: Proposition 8. Hadamard's inequality, used for the constant 3/2. The existence of the block M. The Cramer entry bounds of Lemma 5. The variation of the Fejér density and the sum over Z^J in Lemma 6. The reduction to a decision tree, the map Φ_v and the bit size of the weights. Theorem 7 is therefore not machine-checked as a whole.

## 10. Classical lower bound and the separation

**Theorem 7.** A randomized classical algorithm that computes the minimum degree with error at most 1/3 on all n-vertex graphs with integer weights of at most C n log n bits, for a suitable constant C, makes at least n/5 − 2 cut queries in the worst case.

Querying all singletons gives n queries, so the classical complexity is Θ(n). Together with Theorem 1 and quantum minimum finding, exact minimum degree on integer-weighted graphs has a quadratic separation at weights of O(n² log n) bits: Θ(√n) quantum queries against Θ(n) classical queries. Theorem 7 holds at this scale too, since a lower bound at smaller weights transfers to larger weights. Theorem 1 does not transfer the other way, so it says nothing at O(n log n) bits.

The family is the one of Section 1 with η redefined below. Fix a list X of T query sets, with T < n, and let

    w_j = (⟨b_j, δ_{x^s}⟩)_s,   w^v = (⟨B_v, δ_{x^s}⟩)_s,   Λ = the subgroup of Z^T generated by the w_j,
    Y(X) = {v : G w^v ∉ Λ}.

**Lemma 3 (invisible changes).** If v ∉ Y(X), there is γ ∈ Z^J such that D = G B_v − Σ_j γ_j b_j satisfies ⟨D, δ_{x^s}⟩ = 0 for all s. Then deg(D) = 2G e_v.

*Proof.* G w^v = Σ_j γ_j w_j says exactly this, and deg(b_j) = 0, deg(B_v) = 2e_v. ∎

**Lemma 4 (few visible vertices).** |Y(X)| ≤ 1 + (3/2)(T + 1), when G is a multiple of lcm(1, …, n).

*Proof.* Take u ∈ Y(X). The class of G w^u in the finitely generated group Z^T/Λ is nonzero, and characters into R/Z separate points of such a group. So there is t ∈ (R/Z)^T with ⟨t, w_j⟩ = 0 for all j and G⟨t, w^u⟩ ≠ 0. Put F^u = Σ_s t_s δ_{x^s}. Then ⟨b_j, F^u⟩ = ⟨t, w_j⟩ = 0, so all labels vanish and ε = 0 in (1), and ⟨B_u, F^u⟩ = ⟨t, w^u⟩ = 2β_u. Write β^u for the β of F^u, so that G · 2β^u_u ≠ 0.

The vectors ŷ_v of Lemma 2 depend only on X. Let Y' = Y(X) without vertex 0, r = |Y'|, let K be the lattice of integer dependencies among (ŷ_v)_{v∈Y'}, and let ρ ≤ T + 1 be their rank. If r ≥ 1 then ρ ≥ 1, since the last coordinate of every ŷ_v is 1. Pairing a dependency λ with ŷ_u under the form of F^u gives λ_u · 2β^u_u = 0, using ε = 0. Let g_u be the gcd of the coordinate u over K, with g_u = 0 if it vanishes on K. Then g_u · 2β^u_u = 0. If 1 ≤ g_u ≤ n, then g_u divides G, which contradicts G · 2β^u_u ≠ 0. So g_u = 0 or g_u ≥ n + 1.

Choose ρ independent rows and a set P of ρ columns on which they form an invertible integer matrix M, with entries in {0, ±1}, and let Q = Y' \ P, M' the remaining block on those rows, κ = |Q| = r − ρ. For q ∈ Q, Cramer's rule gives a dependency whose coordinate q equals det M ≠ 0, so g_q ≥ n + 1. The map z ↦ M'z + M Z^ρ from ∏_q [0, g_q) to Z^ρ / M Z^ρ is injective: if M'z − M'z' = Mp, then (−p, z − z') is a dependency among the chosen rows, hence among all rows, so g_q divides z_q − z'_q for each q and z = z'. So (n + 1)^κ ≤ ∏_q g_q ≤ |det M| ≤ ρ^{ρ/2} by Hadamard. Since ρ ≤ r ≤ n, this gives κ ≤ ρ/2, so r ≤ (3/2)(T + 1). ∎

The same injection replaces the determinant duality in the counting step of Lemma 2 when η = 0. For η > 0 the bound det K ≤ r^{ρ/2} is still needed to get the short basis.

**Lemma 5 (small solutions).** The γ of Lemma 3 can be chosen with ‖γ‖₁ ≤ E := (2Gρ + J(ρ + 1))(6√ρ)^ρ, where ρ ≤ T is the rank of the w_j.

*Proof.* If ρ = 0 then all w_j vanish, so G w^v = 0 and γ = 0 works. Let ρ ≥ 1. The entries of the w_j have absolute value at most 6 and those of G w^v at most 2G. Pick an invertible ρ×ρ block M of the matrix (w_j). Restriction to its ρ rows is injective on the column space, and G w^v lies in the column space since v ∉ Y(X), so a solution on those rows solves the whole system; the same holds for the kernel vectors below. Cramer's rule gives a rational solution γ' of Σ_j γ'_j w_j = G w^v supported on the ρ pivot columns, with entries at most 2G(6√ρ)^ρ, since |det M| ≥ 1. It also gives, for each non-pivot column q, an integer kernel vector κ_q with support of size at most ρ + 1 and entries at most (6√ρ)^ρ, and these span the rational kernel. Take any integer solution γ⁰ and write γ⁰ − γ' = Σ_q r_q κ_q. Then γ = γ⁰ − Σ_q ⌊r_q⌋ κ_q is an integer solution equal to γ' + Σ_q {r_q} κ_q. ∎

**Lemma 6 (Fejér shifts).** For the distribution f, Σ_a |f(a+1) − f(a)| ≤ (8/3)η. For integers E ≥ 1 and J ≥ 1,

    Σ_{a ∈ Z^J} sup_{‖e‖_∞ ≤ E} |f^J(a + e) − f^J(a)| ≤ 6EηJ · exp(6EηJ).

*Proof.* f(x) = η g(ηx) with g(y) = (sin(πy)/(πy))². Hence Σ_a |f(a+1) − f(a)| is at most η times the total variation of g. On (0, ∞) the function g falls from 1 to 0 on [0, 1], and on each [k, k+1] it rises and falls once, because g' has the sign of sin(πy)(πy cos(πy) − sin(πy)) and tan x = x has one root per branch. The height on [k, k+1] is at most 1/(π²k²). So the variation on (0, ∞) is at most 1 + 2Σ_{k≥1} 1/(π²k²) = 4/3, which gives 8/3 on the line.

Let V(a) = Σ_{i=−E}^{E−1} |f(a+i+1) − f(a+i)|, and let U(a) = sup_{|e|≤E} f(a+e) ≤ f(a) + V(a). Then Σ_a V(a) ≤ 2E(8/3)η ≤ 6Eη and Σ_a U(a) ≤ 1 + 6Eη. Replacing coordinates one at a time,

    |f^J(a+e) − f^J(a)| ≤ Σ_j ∏_{i<j} U(a_i) · V(a_j) · ∏_{i>j} f(a_i),

and summing over a gives at most Σ_j (1 + 6Eη)^{j−1} · 6Eη = (1 + 6Eη)^J − 1 ≤ 6EηJ · exp(6EηJ). ∎

*Proof of Theorem 7.* We may assume T < n. Let E be the bound of Lemma 5 at ρ = n, which is increasing in ρ, so log E = O(n log n), since log G = O(n). Set η = 1/(1000 J E), so that ξ := 6EηJ exp(6EηJ) ≤ 0.007. With L = ⌈100J/η⌉ and W₀ as in Section 1, the weights have O(n log n) bits whenever all |a_j| ≤ L.

Let μ be the distribution with a drawn from f^J, and with h = 1^n with probability 1/2, and otherwise h = 1^n − e_v for a uniform v. The minimum degree is c + 2G when h = 1^n and c otherwise, with c = (n−1)W₀. Inputs with some |a_j| > L have probability below 1/100. So by averaging over the coins, some deterministic decision tree of depth T has error at most 1/3 + 1/100 under μ. Extend it to answers that do not occur in range, keeping its depth at most T. A path of fewer queries obeys the same bounds.

Let S be the set of a for which the tree on A(1^n, a) outputs "not c", and let α = f^J(S). The error on h = 1^n is at least 1 − α. For a ∈ S let P(a) be its root-to-leaf path and X the queries on it. Fix v, and let S_v = {a ∈ S : v ∉ Y(X of P(a))}. For each leaf with v ∉ Y(X) fix γ as in Lemmas 3 and 5, and define Φ_v(a) = a + γ on S_v. The input A(1^n − e_v, a + γ) equals A(1^n, a) minus the vector D of Lemma 3, so all answers along P(a) agree, the tree reaches the same leaf, and it outputs "not c", which is wrong because vertex v has degree c.

Φ_v is injective on S_v: running the tree on (1^n − e_v, a') determines the leaf, hence γ, hence a. Lemma 6 applies with ⌊E⌋ since γ is an integer vector with ‖γ‖_∞ ≤ ‖γ‖₁ ≤ E, so

    Pr[error | h = 1^n − e_v] ≥ f^J(Φ_v(S_v)) ≥ f^J(S_v) − ξ.

By Lemma 4 each path has at most 1 + (3/2)(T+1) visible vertices, so E_v f^J(S_v) ≥ α(1 − (1.5T + 2.5)/n). Hence the error under μ is at least

    (1/2)(1 − α) + (1/2)(α(1 − (1.5T + 2.5)/n) − ξ) ≥ 1/2 − (1.5T + 2.5)/(2n) − ξ/2.

Comparing with 1/3 + 1/100 gives (1.5T + 2.5)/n ≥ 0.31 − ξ ≥ 0.30, so T ≥ n/5 − 2. ∎

**Proposition 8.** A randomized classical algorithm that computes the minimum degree of n-vertex simple graphs with error at most 1/3 makes Ω(n/log n) cut queries.

*Proof.* Alice holds x ∈ {0,1}^k and Bob holds y ∈ {0,1}^k, with k = n − 7 and shared coins. The graph has vertices v_1, …, v_k and seven hubs A₁, A₂, B₁, B₂, H₁, H₂, H₃ that form a clique. Each v_i is adjacent to A₁ and B₁, to A₂ if x_i = 1, and to B₂ if y_i = 1. Then deg(v_i) = 2 + x_i + y_i and every hub has degree at least 6, so the minimum degree is 2 exactly when some i has x_i = y_i = 0. Both players know each query set, since it depends only on the coins and the earlier answers. Alice sends the number of edges at A₂ that cross it, Bob does the same for B₂, and the remaining edges are public, so a query costs O(log n) bits. Deciding disjointness of the complements of x and y needs Ω(k) bits [5, 6]. ∎

Quantum minimum finding over singleton queries takes O(√n) queries, so simple graphs already show a separation of O(√n) against Ω(n/log n). The reduction gives no useful quantum bound, because a query set in superposition would have to travel between the players, at a cost of n qubits per query.

**Scope.** `sim/check_classical.py` tests Lemmas 3 to 6 and the coupling on adaptive trees at small sizes, with the limits listed in its docstring. It does not test the error probabilities or the true scale of η. Theorem 7 needs huge weights, and on simple graphs the classical bound is Proposition 8. A plain information count gives only O(1) at any answer length, since the output is about one bit.

## References

[1] S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022. arXiv:2201.05674.

[2] N. Nisan, M. Szegedy. On the degree of Boolean functions as real polynomials. Computational Complexity, 1994.

[3] R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. J. ACM, 2001.

[4] T. Lee, M. Santha, S. Zhang. Quantum algorithms for graph problems with cut queries. SODA 2021. arXiv:2007.08285.

[5] B. Kalyanasundaram, G. Schnitger. The probabilistic communication complexity of set intersection. SIAM J. Discrete Math., 1992.

[6] A. Razborov. On the distributional complexity of disjointness. Theoretical Computer Science, 1992.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text. No person has reviewed the proofs.
