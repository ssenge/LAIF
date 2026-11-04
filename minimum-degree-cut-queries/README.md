# Minimum degree with quantum cut queries: a tight bound for integer weights of Θ(n² log n) bits

Sebastian Senge, Independent Researcher. Written 3 Nov 2026.

In [1] it is conjectured that computing the minimum degree of a simple graph requires Ω(√n) quantum cut queries. This file proves the bound for integer-weighted graphs with weights of O(n² log n) bits, and for simple graphs when each query returns the cut only mod 4. The question for simple graphs with integer answers stays open.

| # | Result | Status |
|---|---|---|
| 1 | Ω(√n) quantum cut queries for exact minimum degree, integer weights of O(n² log n) bits | proved below |
| 2 | Ω(√n) for the global minimum cut value at the same weight scale | proved in Section 6 |
| 3 | Sparsity lemma for near-solutions of the cut relations | proved below |
| 4 | Ω(√n) for a promise decision problem on degrees mod M, with weights in Z_M and the oracle returning the cut mod M, M = 2^k ≥ 4 | proved in Section 6 |
| 5 | n/7 − 2 classical randomized cut queries on the same kind of family, so a Θ(√n) against Θ(n) separation | lower bounds proved in Section 10, O(√n) upper bound cited |
| 6 | Ω(n/log n) classical randomized cut queries on simple graphs, by a reduction from set disjointness | proved in Section 10 |
| 7 | Θ(√n) quantum queries on simple graphs when each query returns the cut mod 4, with no restriction on the query sets | lower bound proved in Section 11, upper bound on paper there |

All lower bounds and lemmas below are machine-checked in Lean, assuming two classical theorems as explicit hypotheses: the approximate degree of AND_n and the randomized communication complexity of disjointness. The O(√n) upper bound from quantum minimum finding is cited and not machine-checked, and the words "tight" and "separation" rest on it. The same holds for Proposition 9, which also uses minimum finding. Section 9 gives the theorem names and the scope. The scripts in `sim/` test the identities on small instances, and their limits are listed in their docstrings. All sums in the proofs are finite.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Quantum query complexity | Exact minimum degree with quantum cut queries | O(√n) by quantum minimum finding [1]; no lower bound, Ω(√n) conjectured for simple graphs [1] | Ω(√n), so Θ(√n) | Integer weights of O(n² log n) bits. Simple graphs stay open | Lower bound: Lean, assuming the approximate degree of AND. O(√n): cited |
| Quantum query complexity | Global minimum cut value with quantum cut queries | No Ω(√n) lower bound known to us | Ω(√n) | Same weights | Lean, assuming the approximate degree of AND |
| Quantum query complexity | Promise decision problem on degrees mod M, modular model | No lower bound known to us | Ω(√n) | Weights in Z_M, oracle returns the cut mod M, M = 2^k ≥ 4. Nothing follows for integer oracles | Lean, assuming the approximate degree of AND |
| Quantum query complexity | Exact minimum degree on simple graphs, each query returning the cut mod 4 | No lower bound known to us; Ω(√n) conjectured for integer answers [1] | Θ(√n) | Simple graphs, any query sets. Integer answers stay open | Lower bound: Lean, assuming the approximate degree of AND. O(√n): on paper, using quantum minimum finding |
| Lattice lemma | Sparsity of near-solutions of the cut relations | Not available | At most 2R + 3 vertices with a visible degree shift, for R query terms | General tool for the bounds above | Lean |
| Classical query complexity | Exact minimum degree with randomized cut queries, large weights | O(n) by singleton queries; Ω(n/log n) from the simple-graph row below | At least n/7 − 2, so Θ(n) | Integer weights of O(n log n) bits and above | Lean |
| Classical query complexity | Exact minimum degree with randomized cut queries, simple graphs | O(n) by singleton queries; no lower bound stated in the sources known to us | Ω(n/log n) | Simple graphs | Lean, assuming the communication complexity of disjointness |
| Quantum-classical separation | Exact minimum degree with cut queries | O(√n) quantum and O(n) classical upper bounds, without matching lower bounds | Θ(√n) quantum against Θ(n) classical | Integer weights of O(n² log n) bits | Both lower bounds: Lean, as above. O(√n): cited |

## Model

The vertex set is V with |V| = n, E is the set of unordered pairs, and a graph is a vector A ∈ Z_{≥0}^E. For x ∈ {0,1}^n let δ_x ∈ {0,1}^E be the indicator of the pairs separated by x, so that cut_A(x) = ⟨A, δ_x⟩. The input class is the set of graphs with weights in [0, W], and N = n²W, which exceeds every cut value. A query is the unitary

    |x, z⟩ → exp(2πi z cut_A(x) / N) |x, z⟩,   z ∈ Z.

A Fourier transform on a second register turns this into |x, y⟩ → |x, y + cut_A(x) mod N⟩, so the two forms are equivalent. An algorithm with any other answer register is simulated with two queries of this form per query, by computing into a fresh register and uncomputing. This changes T by a factor of at most 2, and below T counts queries of the form above. Unitaries that do not depend on A act between queries, on a finite basis that may include any workspace.

‖θ‖ denotes the distance from θ to the nearest integer, and elements of R/Z are treated with this norm.

**Theorem 1.** A quantum algorithm that computes the minimum degree with error at most 1/3 on all n-vertex graphs with integer weights in [0, 2^{Cn²(⌊log₂ n⌋ + 1)}], for a suitable constant C, makes Ω(√n) queries.

Quantum minimum finding over singleton cuts gives the matching O(√n) upper bound, as noted in [1].

## 1. The hard family

**Lattice basis.** For a pair {u,v} with u, v ≠ 0 and {u,v} ≠ {1,2}, let

    b_uv = e_uv − e_0u − e_0v + e_01 + e_02 − e_12.

Write deg for the degree map, deg(A)_v = Σ_w A_vw. Then deg(b_uv) = 0, and the entries of b_uv lie in {0, ±1}. There are J = C(n,2) − n such vectors, so J = 0 at n = 3. Assume n ≥ 3 from here on, since the bounds are trivial for smaller n. The proofs below do not use that they form a basis of ker(deg) ∩ Z^E, only the identity (1).

**Decomposition.** Take F ∈ (R/Z)^E. Choose β_0 with 2β_0 = F_01 + F_02 − F_12 and set β_v = F_0v − β_0 for v ≠ 0. Then, in R/Z,

    F_uv = β_u + β_v + ε_uv,   with ε_uv = ⟨b_uv, F⟩ when b_uv is defined and ε_uv = 0 otherwise. (1)

**Degree shifts.** For each v fix two other vertices a, c and let B_v = e_va + e_vc − e_ac. Then deg(B_v) = 2e_v. By (1), ⟨B_v, F⟩ = 2β_v + ⟨B_v, ε⟩ in R/Z, so ‖⟨B_v, F⟩ − 2β_v‖ ≤ 3 max_e ‖ε_e‖.

**The input.** Let G = n!, which all of 1, …, n divide. For h ∈ {0,1}^n and a ∈ Z^J let

    A(h, a) = W₀·1 + G Σ_v h_v B_v + Σ_j a_j b_j.

Every vertex has degree (n−1)W₀ + 2G h_v, so the minimum degree is (n−1)W₀ unless h = 1^n.

**The distribution of a.** Fix integers m ≥ 1 and N ≥ 2m, and let ω = exp(2πi/N). For a ∈ Z_N let

    g(a) = |Σ_{j<m} ω^{ja}|² / (mN).

Then g ≥ 0. For an integer k let |k|_N be the distance from k to NZ. Expanding the square and using orthogonality gives Σ_a g(a) ω^{ak} = (1/m) #{(j, j') ∈ [m]² : j − j' + k ≡ 0 mod N}, and since 2m ≤ N this is

    Σ_a g(a) ω^{ak} = φ(k) := max(0, 1 − |k|_N / m).

So g is a probability distribution on Z_N, and φ(k) = 0 exactly when |k|_N ≥ m. Also Σ_{k∈Z_N} φ(k) = m. For a with representative r ∈ (−N/2, N/2], r ≠ 0, the geometric sum gives |Σ_{j<m} ω^{ja}| ≤ 2/|1 − ω^a| ≤ N/(2|r|), because |1 − ω^a| = 2 sin(π|r|/N) ≥ 4|r|/N. So g(a) ≤ N/(4mr²), and Pr[|r| > L] ≤ N/(2mL). Draw the a_j independently from g and use their representatives in A(h, a).

**Sizes.** Let W = 2^{Cn²(⌊log₂ n⌋ + 1)}, N = n²W, and let L = ⌊W/(24n²)⌋ and W₀ = JL + nG. On each edge, Σ_v |B_v(e)| ≤ n and Σ_j |b_j(e)| ≤ J, so if all |a_j| ≤ L the weights lie in [0, 2W₀] ⊆ [0, W]. Take m = 2400n⁶. Then Pr[∃j : |a_j| > L] ≤ JN/(2mL) ≤ 1/100, using J ≤ n². Note that m does not depend on W.

The oracle formula makes sense for every a, inside or outside the range. If a is out of range the algorithm has no correctness guarantee, but its acceptance probability is still in [0,1].

## 2. Expansion over labels

A path p fixes the query basis states (x^s, z^s), s = 1..T, and an output basis state. The final state of the algorithm on input A is Σ_p α_p exp(2πi⟨A, Z_p⟩/N) |end(p)⟩, with Z_p = Σ_s z^s δ_{x^s}. For two paths let D = Z_p − Z_{p'} and let its label be u(D) = (⟨b_j, D⟩ mod N)_j ∈ Z_N^J.

Let acc(A) be the probability of accepting on A. Summing over pairs of paths with the same accepting end,

    acc(A(h, c)) = Σ_{u ∈ Z_N^J} ω^{c·u} K_u(h),   K_u(h) = Σ_{pairs with label u} α_p ᾱ_{p'} exp(2πi⟨A(h,0), D⟩/N),

for every c ∈ Z_N^J. This is a Fourier expansion on Z_N^J, so

    K_u(h) = N^{−J} Σ_c ω^{−c·u} acc(A(h, c)),

and since acc ∈ [0,1], **each |K_u(h)| ≤ 1**. Averaging over a,

    P(h) := E_a acc(A(h, a)) = Σ_u φ(u) K_u(h),   φ(u) = Π_j φ(u_j) ∈ [0,1],   Σ_u φ(u) = m^J.

## 3. Sparsity lemma

**Lemma 2.** Let F = Σ_{s=1}^R t_s δ_{x^s} with t_s ∈ R/Z and x^s ∈ {0,1}^n. Suppose ‖⟨b_j, F⟩‖ ≤ η for all j. Let G be a multiple of all of 1, …, n and put τ = G(n² n! + 3)η. Then

    #{v : ‖G⟨B_v, F⟩‖ > τ} ≤ 2R + 3.

For η = 0 the set on the left is exactly {v : G⟨B_v, F⟩ ≠ 0}.

*Proof.* Let f_v = Σ_s t_s x^s_v and H_s = 2t_s, and let c_v = (x^s_v)_s ∈ {0,1}^R. Since (δ_x)_uv = x_u + x_v − 2x_u x_v, for u ≠ v we get Σ_s H_s c_v(s) c_u(s) = f_u + f_v − F_uv. Write ⟨c_u, c_v⟩_H for that form. Fix the base vertex 0. Let y_v = c_v − c_0 ∈ {0,±1}^R, and let ŷ_v = (y_v, 1) ∈ Z^{R+1}. Extend the form by Ĥ = (H, −2β_0) on the last coordinate. A direct expansion with (1) gives, for u, v ≠ 0,

    ⟨ŷ_u, ŷ_v⟩_Ĥ = −ε_uv + ε_u0 + ε_v0 (u ≠ v),   ⟨ŷ_v, ŷ_v⟩_Ĥ = 2β_v + 2ε_v0.

By (1), ε_v0 = 0 for all v. So off-diagonal entries are −ε_uv, of norm at most η, and the diagonal is exactly 2β_v.

Let Y be the set in the lemma without the vertex 0, and let r = |Y|. A dependency is an integer vector λ on Y with Σ_v λ_v ŷ_v = 0. For u ∈ Y let g_u ≥ 0 generate the subgroup of u-coordinates of dependencies.

*Blocks.* Choose a maximal independent set P of the vectors ŷ_v, of size ρ ≤ R + 1, and ρ rows on which these columns form an invertible integer matrix M, with Δ = det M > 0, swapping two rows if needed. These rows determine the dependencies, because each column is a rational combination of those in P. For q ∈ Y \ P let ν_q be the vector with coordinate Δ at q, coordinate 0 at the other vertices outside P, and Cramer's values on P. It is a dependency, and its entries are determinants of {0, ±1} matrices, so Δ and all entries are at most ρ!. Hence g_q divides Δ, so g_q ≠ 0.

*Small dependencies.* Suppose g_u ≠ 0. Then ŷ_u is a rational combination of the other vectors, so P can be chosen without u. Take a dependency λ with λ_u = g_u. Subtracting ⌊λ_q/Δ⌋ ν_q for each q ∉ P ∪ {u} leaves λ_u unchanged and puts the other λ_q into [0, Δ), and g_u ≤ Δ as well. The dependency Δλ − Σ_q λ_q ν_q is supported on P, which is independent, so it is 0. Thus Δ |λ_p| ≤ Σ_q |λ_q| |ν_q(p)| ≤ r Δ ρ!, and ‖λ‖₁ ≤ r² r! ≤ n² n!.

*Divisibility.* Pairing Σ_v λ_v ŷ_v = 0 with ŷ_u gives ‖g_u · 2β_u‖ ≤ ‖λ‖₁ η ≤ n² n! η. If 1 ≤ g_u ≤ n then g_u divides G, so ‖G · 2β_u‖ ≤ G n² n! η, and by the Degree shifts bound ‖G⟨B_u, F⟩‖ ≤ τ. That contradicts u ∈ Y. So every u ∈ Y has g_u = 0 or g_u ≥ n + 1.

*Counting.* Fix a block as above, let Q = Y \ P and κ = |Q|. Every q ∈ Q has g_q ≠ 0, so g_q ≥ n + 1. Let M' be the block of the columns in Q on the chosen rows. The map z ↦ M'z + M Z^ρ from Π_q [0, g_q) to Z^ρ / M Z^ρ is injective: if M'z − M'z' = Mp, then (−p, z − z') is a dependency, so g_q divides z_q − z'_q for each q, and z = z'. The quotient has Δ elements, so (n + 1)^κ ≤ Δ ≤ ρ! ≤ n^ρ, which gives κ ≤ ρ. So r ≤ 2ρ ≤ 2(R + 1), and adding back vertex 0 gives the bound. ∎

Dyadic t_s can approximate any rational, for example 1/3, and then F is close to an exact solution modulo 3. So near-solutions over Z_N behave like solutions over all of Q/Z, which is why the proof does not stop at the 2-rank of Z_{2^k}. The dependencies can be nonzero: at G = 1, an exact instance has n = 13, N = 12, R = 60, r = 12, ρ = 11, and its group of dependencies is spanned by (3,3,3,−3,−3,−3,2,2,2,−2,−2,−2). In this instance every 2β_v has denominator dividing 6, so at the G that Lemma 2 requires the set Y is empty. I do not know an instance with κ > 0 when G is a multiple of 1, …, n and T < n, so the factor 2 in 2R + 3 and the constant in n/7 may not be sharp.

**Exact 2-group case.** If all ⟨b_j, F⟩ = 0, G = 1 and all t_s have 2-power order, then for u ∈ Y the element 2β_u is nonzero of 2-power order, and λ_u · 2β_u = 0 makes λ_u even for every dependency λ. Half of a dependency is again a dependency, so the only dependency is 0, and r ≤ R + 1.

## 4. Low-degree polynomial

Fix T and a label u with φ(u) ≠ 0 that occurs. Fix one pair with that label and call its difference D_u, which has at most 2T terms. Any pair with label u has D with D − D_u of at most 4T terms and all labels of D − D_u zero modulo N. So

    K_u(h) = c_u exp(2πi Σ_v h_v φ_{u,v}) q_u(h),   φ_{u,v} = G⟨B_v, D_u⟩/N mod 1,

with |c_u| = 1, the factor exp(2πi W₀⟨1, D_u⟩/N). Here q_u collects the rest. By Lemma 2 with η = 0, each pair depends on at most 8T + 3 of the h_v, and for h_v ∈ {0,1} each factor equals 1 + h_v(exp(2πiG⟨B_v, D − D_u⟩/N) − 1). So q_u is a multilinear polynomial of degree at most 8T + 3, and |q_u(h)| = |K_u(h)| ≤ 1 on the cube.

Since φ(u) ≠ 0, every |u_j|_N < m, so ‖⟨b_j, D_u/N⟩‖ ≤ η with η = m/N. By Lemma 2 with R = 2T, the set Y_u = {v : ‖φ_{u,v}‖ > τ} has at most 4T + 3 elements. Define

    P̃(h) = Σ_u φ(u) c_u q_u(h) Π_{v∈Y_u} (1 + h_v(exp(2πi φ_{u,v}) − 1)).

Then deg P̃ ≤ 12T + 6. On the cube

    |P(h) − P̃(h)| ≤ Σ_u φ(u) |exp(2πi Σ_{v∉Y_u} h_v φ_{u,v}) − 1| ≤ m^J · 2πnτ,   τ = G(n² n! + 3) m / N.

Since m^J and G(n² n! + 3) are 2^{O(n²(log n + 1))} and N = n²W, a large enough C makes this at most 1/100. This is where the large weights come from. C = 24 satisfies this inequality and the size conditions of Section 1.

## 5. Proof of Theorem 1

Let the algorithm accept when it reports (n−1)W₀. With probability at least 0.99 over a, the input is in range. So P(h) ≥ 0.66 if h ≠ 1^n and P(1^n) ≤ 0.34. Q = Re P̃ is a real polynomial with Q ∈ [−0.01, 1.01] on the cube, Q ≥ 0.65 for h ≠ 1^n, and Q(1^n) ≤ 0.35. Let f = (1.01 − Q)/1.02, so f ∈ [0,1] on the cube, f(1^n) ≥ 11/17 and f(h) ≤ 6/17 otherwise. The map σ(x) = 3x² − 2x³ is increasing on [0,1] with σ(11/17) ≥ 2/3 and σ(6/17) ≤ 1/3, so σ∘f approximates AND_n within 1/3. It has degree at most 3(12T + 6). The approximate degree of AND_n is Θ(√n) [2, 3], so T = Ω(√n). ∎

## 6. Corollaries and the modular model

**Global minimum cut.** Take a graph A on V with weights at most W, and let V' = V ∪ K' with |K'| = n. Join all pairs inside K' and across (V, K') with weight W* = nW. This is the construction of [1, Lemma D.1] with heavy weights. A cut query on this graph takes one query on A plus known numbers. A set with a vertices of V and b of K' is crossed by f = b(n − b) + a(n − b) + (n − a)b pairs of weight W*. For 1 ≤ b ≤ n − 1, f is linear in a, with f = b(2n − b) at a = 0 and f = (n − b)(n + b) at a = n, so f ≥ 2n − 1. For b = 0, f = an, and b = n is its complement, so f ≥ 2n unless the set or its complement is a singleton of V. A singleton v ∈ V has value d_v + nW*. Since d_v ≤ (n−1)W < W*, the minimum cut value is δ(A) + nW*. So the global minimum cut value of weighted graphs on 2n vertices needs Ω(√n) quantum cut queries at this weight scale. A found minimum cut gives its value with one more query, so the same bound holds for finding one. The question in [1] whether o(n) quantum cut queries suffice to find a minimum cut stays open. In [4] it is asked whether polylog(n) quantum cut queries suffice for minimum cut, and at this weight scale they do not. At polynomial weights that question stays open. The cut function is symmetric and submodular, so minimizing such a function over nonempty proper subsets needs Ω(√n) quantum evaluation queries when values have Θ(n² log n) bits. This does not settle the question in [4] about plain submodular minimization, where the minimum is over all subsets, since a cut function has its minimum 0 at the empty set.

**Modular model.** Let the weights lie in Z_M and the oracle return the cut mod M, with M = 2^k ≥ 4. Fix c with nc even. This is a promise decision problem. Promise: every degree mod M lies in {c, c+2}. Task: decide whether some vertex has degree c mod M. Take G = 1, replace W₀·1 by a fixed graph A₀ with deg(A₀) = c·1, which exists because deg maps onto the vectors of even sum, and draw a uniformly from Z_M^J. Then φ is the indicator of 0, so only the label 0 survives and P is exactly a polynomial in h. A pair has R ≤ 2T terms, so the exact 2-group case gives deg P ≤ 2T + 2, and T = Ω(√n). Nothing follows for integer weights: a mod M oracle returns less than an integer oracle, so this bound says nothing about small integer weights with exact answers. The shift has to be even and nonzero mod M: an odd degree difference would show up in the parities, which one query reads by Bernstein-Vazirani, and for M = 2 a shift of 2 is invisible.

## 7. Limits

- **Simple graphs are covered only with answers mod 4.** The question in [1] is about simple graphs with integer answers, and Section 11 explains where its argument stops. Weights in Theorem 1 have Θ(n² log n) bits, and I know no reduction from these weights to simple graphs on poly(n) vertices. A blow-up has to answer queries that split blocks, and those are not cut queries on the original graph.
- **What breaks for small weights.** Keeping a in range needs JN/(2mL) ≤ 1/100, and N/L is about 24n⁴, so m = Ω(n⁶). The sum over labels in Section 4 has total mass m^J, and each term carries an error of about nτ, which is proportional to m/N. So N has to exceed m^J, which gives log W ≳ J log m = Θ(n² log n).
- **Weight scale.** I did not try to minimize the bits. Using fewer than J hidden directions would shorten them, but a sublattice weakens Lemma 2, and getting to poly(n) values would need a different argument for the error term.
- **Consistency with known upper bounds.** The polylog(n) approximation of the minimum degree discussed in [1, Section 2.4] is for simple graphs. The routine of [4, Lemma 15] counts nonzero row entries at a cost that grows with log M, which is about n² log n queries at this scale. So neither contradicts Theorem 1. Degree parity costs one query, and all degrees here have fixed parity.

## 8. Importance

Modest. It settles a weighted variant of a conjecture in [1] with a tight bound, using a short argument. The stated simple-graph version remains open, and the weights are far larger than anything an application would use. To my knowledge the integer-weighted lower bound is new. The classical results add little: Proposition 7 is elementary and may well be folklore, although I have not seen it stated, and Theorem 6 only removes its log factor, for huge weights. Theorem 8 is a tight bound on simple graphs with no restriction on query sets, also new to my knowledge, but its oracle is weaker than the one in [1], so it leaves the conjecture open.

## 9. Formal verification

The results are machine-checked end to end in `lean/`, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. The files contain no `sorry`, and the theorems listed in `lean/CutQuery/Axioms.lean` use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). To check them, run `lake exe cache get` and `lake build` in `lean/`, then `lake env lean CutQuery/Axioms.lean`, which prints the axioms of each theorem.

**Two classical theorems are hypotheses.** They are stated in `lean/CutQuery/Model.lean` and appear as explicit assumptions of the theorems that use them:

- `AndApproxDegree`: a real polynomial that approximates AND_k within 1/3 on the cube has degree at least c√k [2].
- `DisjLowerBound`: a distribution over deterministic protocols that decides disjointness of k-bit strings with error at most 1/3 on every input communicates at least ck bits [5, 6].

| Result | Lean theorem | Hypothesis |
|---|---|---|
| Theorem 1, with C = 24 in the statement | `quantum_bound`, `quantum_bound_24` | `AndApproxDegree` |
| Theorem 1 for any modulus | `quantum_bound_any_modulus` | `AndApproxDegree` |
| Theorem 1 for any answer interface: a query multiplies \|s⟩ by any unit-modulus function of s and the cut, simulated with two phase queries | `quantum_bound_general`, `GenAlg.errAt_sim` | `AndApproxDegree` |
| Global minimum cut, on 2n vertices | `quantum_mincut_bound`, `isMinCut_liftW` | `AndApproxDegree` |
| Modular model | `modular_bound` | `AndApproxDegree` |
| Theorem 8, simple graphs with answers mod 4 | `mod4_simple_bound`, `isSimple_tri`, `card_diag_le` | `AndApproxDegree` |
| Lemma 2 | `sparsity_cut` | none |
| Lemmas 3 and 5 | `exists_small_gamma` | none |
| Lemma 4 | `visible_card` | none |
| Exact 2-group case | `sparsity_two_group` | none |
| Theorem 6, with C = 23 in the statement | `classical_bound`, `classical_bound_23` | none |
| Theorem 6 at the weight scale of Theorem 1 | `classical_at_quantum_scale` | none |
| Proposition 7 | `simple_graph_bound` | `DisjLowerBound` |
| n singleton queries compute the minimum degree | `singleton_upper_bound` | none |
| n phase queries compute the minimum degree with error 0, so the premise of Theorem 1 can be met for every n and C | `readAll_errAt`, `quantum_premise_holds` | none |

**Not machine-checked:** the O(√n) upper bound from quantum minimum finding. It is cited, and it is what makes the quantum bound tight and gives the Θ(√n) side of every separation claim. The Lean files prove only that n phase queries suffice. Proposition 9 is proved on paper and uses minimum finding, so it is not machine-checked either.

**What the check does not cover.** Lean checks the proofs against the definitions in `Model.lean`, so the theorems mean what those definitions say. Their modelling choices are these. A classical algorithm is a distribution with finite support over deterministic adaptive algorithms making exactly T queries, and a shorter algorithm can pad its queries. A quantum algorithm acts on a finite basis, alternates unitaries with diagonal queries, and measures in the basis at the end. A graph is a function from pairs u < v to the integers. The Model section's simulation of other answer registers is checked in the direction a lower bound needs, from an answer-register algorithm to phase queries (`GenAlg.sim`). The converse is not formalized. Apart from the theorems that name C, the constants are existential.

## 10. Classical lower bound and the separation

**Theorem 6.** A randomized classical algorithm that computes the minimum degree with error at most 1/3 on all n-vertex graphs with integer weights of at most Cn(⌊log₂ n⌋ + 1) bits, for a suitable constant C, makes at least n/7 − 2 cut queries in the worst case.

Querying all singletons computes the minimum degree with n deterministic queries, so the classical complexity is Θ(n). The nearest earlier bounds are for connectivity: n/4 expected linear queries for zero-error algorithms [7], and Ω(n/log n) cut queries at bounded error from communication complexity. Together with Theorem 1 and quantum minimum finding, exact minimum degree on integer-weighted graphs has a quadratic separation at weights of O(n² log n) bits: Θ(√n) quantum queries against Θ(n) classical queries. Theorem 6 holds at this scale too, since a lower bound at smaller weights transfers to larger weights. Theorem 1 does not transfer the other way, so it says nothing at O(n log n) bits.

The family is the one of Section 1, with a drawn uniformly from a box. Fix a list X of T query sets, with T < n, and let

    w_j = (⟨b_j, δ_{x^s}⟩)_s,   w^v = (⟨B_v, δ_{x^s}⟩)_s,   Λ = the subgroup of Z^T generated by the w_j,
    Y(X) = {v : G w^v ∉ Λ}.

**Lemma 3 (invisible changes).** If v ∉ Y(X), there is γ ∈ Z^J such that D = G B_v − Σ_j γ_j b_j satisfies ⟨D, δ_{x^s}⟩ = 0 for all s. Then deg(D) = 2G e_v.

*Proof.* G w^v = Σ_j γ_j w_j says exactly this, and deg(b_j) = 0, deg(B_v) = 2e_v. ∎

**Lemma 4 (few visible vertices).** |Y(X)| ≤ 2T + 3.

*Proof.* Take u ∈ Y(X). The class of G w^u in the finitely generated group Z^T/Λ is nonzero, and characters into Q/Z separate points of such a group. So there is t ∈ (Q/Z)^T with ⟨t, w_j⟩ = 0 for all j and G⟨t, w^u⟩ ≠ 0. Put F^u = Σ_s t_s δ_{x^s}. Then ⟨b_j, F^u⟩ = ⟨t, w_j⟩ = 0, so all labels vanish and ε = 0 in (1), and ⟨B_u, F^u⟩ = ⟨t, w^u⟩ = 2β_u. Write β^u for the β of F^u, so that G · 2β^u_u ≠ 0.

The vectors ŷ_v of Lemma 2 depend only on X, so the dependencies, the g_u and the blocks do too. Pairing a dependency λ with ŷ_u under the form of F^u gives λ_u · 2β^u_u = 0. So g_u · 2β^u_u = 0. If 1 ≤ g_u ≤ n, then g_u divides G, which contradicts G · 2β^u_u ≠ 0. So g_u = 0 or g_u ≥ n + 1, and the Counting step of Lemma 2 gives |Y(X)| ≤ 2(T + 1) + 1. ∎

**Lemma 5 (small solutions).** The γ of Lemma 3 can be chosen with |γ_j| ≤ (G + J) T! 6^T for all j.

*Proof.* Pick an invertible ρ×ρ block M of the matrix (w_j), with ρ ≤ T, and let Δ = det M > 0, swapping two rows if needed. The entries of the w_j have absolute value at most 6 and those of w^v at most 3. Restriction to the ρ chosen rows is injective on the column space, and G w^v lies in the column space since v ∉ Y(X), so a solution on those rows solves the whole system, and the same holds for kernel vectors. For each non-pivot column q, Cramer's rule gives an integer kernel vector ν_q with coordinate Δ at q, zero at the other non-pivots, and entries at most ρ! 6^ρ on the pivots. Take any integer solution γ⁰, and subtract ⌊γ⁰_q/Δ⌋ ν_q for every non-pivot q, so that the non-pivot coordinates lie in [0, Δ). Call the result γ. On the pivots, Cramer's rule applied to Mγ_P = G w^v − Σ_q γ_q w_q on the chosen rows gives Δ γ_p = det(M with column p replaced by G w^v) − Σ_q γ_q det(M with column p replaced by w_q). So Δ |γ_p| ≤ G ρ! 6^ρ + J Δ ρ! 6^ρ, using |γ_q| ≤ Δ, and since Δ ≥ 1 this gives |γ_p| ≤ (G + J) ρ! 6^ρ. ∎

*Proof of Theorem 6.* We may assume T < n. Let Γ = (G + J) n! 6^n, which bounds Lemma 5 since T < n, so log Γ = O(n log n), because G = n!. Let L = 1000JΓ and W₀ = JL + nG. For a in the box [−L, L]^J the weights of A(h, a) are in [0, 2W₀] and have O(n log n) bits.

Let μ be the distribution with a uniform on the box, and with h = 1^n with probability 1/2, and otherwise h = 1^n − e_v for a uniform v. The minimum degree is c + 2G when h = 1^n and c otherwise, with c = (n−1)W₀. By averaging over the coins, some deterministic adaptive algorithm with T queries has error at most 1/3 under μ.

Let S be the set of a in the box for which it outputs something other than c on A(1^n, a), and let α be the fraction of the box in S. The error on h = 1^n is at least 1 − α. For a ∈ S let X be the queries it makes on A(1^n, a). Fix v, and let S_v = {a ∈ S : v ∉ Y(X)}. For each transcript with v ∉ Y(X) fix γ as in Lemmas 3 and 5, and define Φ_v(a) = a + γ on S_v. The input A(1^n − e_v, a + γ) equals A(1^n, a) minus the vector D of Lemma 3, so all answers agree, the output is the same and it is not c, which is wrong because vertex v has degree c.

Φ_v is injective on S_v: running the algorithm on A(1^n − e_v, a') determines the transcript, hence γ, hence a. If a + γ leaves the box, then some coordinate of a is within Γ of the boundary, and this holds for a fraction at most ξ := 2JΓ/(2L + 1) ≤ 1/1000 of the box. So

    Pr[error | h = 1^n − e_v] ≥ |S_v|/|box| − ξ.

By Lemma 4 each transcript has at most 2T + 3 visible vertices, so the average over v of |S_v|/|box| is at least α(1 − (2T + 3)/n). Hence the error under μ is at least

    (1/2)(1 − α) + (1/2)(α(1 − (2T + 3)/n) − ξ) ≥ 1/2 − (2T + 3)/(2n) − ξ/2.

The weights fit with C = 23. Comparing with 1/3 gives (2T + 3)/n ≥ 1/3 − ξ ≥ 0.332, so T ≥ 0.166n − 1.5 ≥ n/7 − 2. ∎

**Proposition 7.** A randomized classical algorithm that computes the minimum degree of n-vertex simple graphs with error at most 1/3 makes Ω(n/log n) cut queries.

*Proof.* Alice holds x ∈ {0,1}^k and Bob holds y ∈ {0,1}^k, with k = n − 4 and shared coins. The graph has vertices v_1, …, v_k and four hubs A₁, A₂, B₁, B₂ that form a clique. Each v_i is adjacent to A₁ and B₁, to A₂ if x_i = 1, and to B₂ if y_i = 1. Then deg(v_i) = 2 + x_i + y_i and every hub has degree at least 3, so the minimum degree is 2 exactly when some i has x_i = y_i = 0. Both players know each query set, since it depends only on the coins and the earlier answers. Alice sends the number of edges at A₂ that cross it, Bob does the same for B₂, and the remaining edges are public, so a query costs O(log n) bits. Deciding disjointness of the complements of x and y needs Ω(k) bits [5, 6]. ∎

Quantum minimum finding over singleton queries takes O(√n) queries, so simple graphs already show a separation of O(√n) against Ω(n/log n). The reduction gives no useful quantum bound, because a query set in superposition would have to travel between the players, at a cost of n qubits per query.

**Scope.** `sim/check_classical.py` tests Lemmas 3 to 5 and the coupling on adaptive trees at small sizes, with the limits listed in its docstring. Theorem 6 needs huge weights, and on simple graphs the classical bound is Proposition 7. A plain information count gives only O(1) at any answer length, since the output is about one bit.

## 11. Simple graphs with answers mod 4

Here a query is |x, z⟩ → i^{z cut_A(x)} |x, z⟩ with z ∈ Z₄, and A is a simple graph. This is the model of Section 1 with N = 4, so N no longer exceeds the cut values and the integer cut cannot be recovered. Query sets are unrestricted, and algorithms may be adaptive and use workspace.

**Theorem 8.** A quantum algorithm that computes the minimum degree of every n-vertex simple graph with error at most 1/3, where each query returns the cut mod 4, makes Ω(√n) queries.

**The graph.** Assume n ≥ 6 and let L = ⌊n/3⌋. Name 3L vertices v_ℓ, a_ℓ, c_ℓ for ℓ = 1, …, L. The base graph A₀ is a clique on the v_ℓ together with a clique on all other vertices. Write e(u, w) for the unit vector of a pair, with e(u, u) = 0. For ℓ ≤ m let

    G(ℓ, m) = e(v_ℓ, c_m) + e(a_ℓ, v_m) − e(v_ℓ, v_m) − e(a_ℓ, c_m).

For an upper triangular bit matrix U let A(U) = A₀ + Σ_{ℓ≤m} U_ℓm G(ℓ, m).

Each pair lies in the support of at most one gadget. The pairs v_ℓc_m and a_ℓv_m with ℓ ≤ m have base value 0 and coefficient +1. The pairs v_ℓv_m with ℓ < m and a_ℓc_m with ℓ ≤ m have base value 1 and coefficient −1. So A(U) is a simple graph.

A gadget with ℓ < m preserves all degrees, and G(ℓ, ℓ) raises the degree of v_ℓ by 2 and leaves the others unchanged. Hence deg v_ℓ = L − 1 + 2U_ℓℓ, and every other vertex has degree n − L − 1 ≥ L + 1. The minimum degree is L + 1 if every diagonal bit is 1, and L − 1 otherwise.

**The queries.** Let Y_ℓ = x(v_ℓ) − x(a_ℓ) and Q_m = x(v_m) − x(c_m). Checking the 16 cases of four bits gives ⟨G(ℓ, m), δ_x⟩ = 2 Y_ℓ Q_m, so

    cut_{A(U)}(x) = cut_{A₀}(x) + 2 Yᵀ U Q.

Mod 4 this term is 2 yᵀ U q, where y and q reduce Y and Q mod 2. A query therefore evaluates a bilinear form of a hidden triangular matrix over F₂, with the bits to be tested on its diagonal.

*Proof of Theorem 8.* Write U as h on the diagonal and uniform independent bits a above it. Expand the acceptance probability over pairs of paths as in Section 2. A pair has coefficients w_s ∈ Z₄ on at most 2T query sets, and it contributes a phase independent of U times (−1)^{Σ_{ℓ≤m} U_ℓm M_ℓm}, where M = Σ_s w_s y^s (q^s)ᵀ over F₂. So rank M ≤ 2T.

Averaging over a multiplies the term by 0 unless M_ℓm = 0 for all ℓ < m. In that case M is lower triangular. Let I = {ℓ : M_ℓℓ = 1}. The submatrix of M on I is lower triangular with unit diagonal, so |I| ≤ rank M ≤ 2T, and the term is a constant times (−1)^{Σ_{ℓ∈I} h_ℓ}.

Thus P(h) = E_a acc(A(U)) is a real polynomial in h of degree at most 2T, with values in [0, 1]. Let the algorithm accept when it reports L − 1. Then P(h) ≥ 2/3 if some h_ℓ = 0 and P(1^L) ≤ 1/3, so 1 − P approximates AND_L within 1/3. The approximate degree of AND_L gives 2T = Ω(√L). ∎

The exact zeros come from evenness: ⟨G(ℓ, m), δ_x⟩ is always even, so at phases of order 4 a hidden bit contributes 1 or −1, and these cancel or add up.

**Proposition 9.** With answers mod 4, O(√n) queries suffice on every simple graph.

*Proof.* Singleton queries do not suffice, since they give degrees only mod 4. For a vertex u and a set S not containing u, cut(S ∪ {u}) − cut(S) = deg u − 2 e(u, S), where e(u, S) counts the edges from u to S. Two queries on a uniform superposition of S thus prepare i^{deg u} Σ_S (−1)^{e(u,S)} |S⟩. A Hadamard transform reads the neighbours of u exactly, which gives deg u, and two more queries uncompute. So 4 queries compute deg u coherently and without error, and quantum minimum finding over u finishes. ∎

**Relation to matrix queries.** In [8] it is shown that trace, determinant and rank need Ω(n) quantum queries with matrix-vector or bilinear access to a general matrix over a finite field. On the family above, fixing x(v) = 0 makes y and q free, and one query with q in superposition reads yᵀU. The determinant bound of [8] does not transfer, because det U = AND(h) here for triangular U, and Grover search over the diagonal takes O(√L) queries. What Theorem 8 adds is a simple graph that puts the degrees on the diagonal of such a matrix, together with the triangular rank bound.

**Where it stops.** The integer oracle of [1] also allows z with z/N outside (1/4)Z. For a pair of paths let M_ℓm = Σ_s (w_s / N) Y^s_ℓ Q^s_m with w_s ∈ Z. A hidden bit then contributes the factor (1 + e(2 M_ℓm))/2, of modulus |cos(2π M_ℓm)|, which is zero only when 2 M_ℓm ≡ 1/2 mod 1. Other pairs are damped but do not vanish, so P need not have degree at most 2T. `sim/check_mod4.py` shows this at phase 1/8, where weight above 2T is nonzero. With about n² hidden bits this damping can be large, but an absolute sum over paths loses a factor exponential in Tn, and I have no bound on the coherent sum.

`sim/check_mod4.py` tests the graph, the identity, the polynomial degree on random unitaries and the routine of Proposition 9, on small instances listed in its docstring.

## References

[1] S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022. arXiv:2201.05674.

[2] N. Nisan, M. Szegedy. On the degree of Boolean functions as real polynomials. Computational Complexity, 1994.

[3] R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. J. ACM, 2001.

[4] T. Lee, M. Santha, S. Zhang. Quantum algorithms for graph problems with cut queries. SODA 2021. arXiv:2007.08285.

[5] B. Kalyanasundaram, G. Schnitger. The probabilistic communication complexity of set intersection. SIAM J. Discrete Math., 1992.

[6] A. Razborov. On the distributional complexity of disjointness. Theoretical Computer Science, 1992.

[7] A. Auza, T. Lee. On the query complexity of connectivity with global queries. arXiv:2109.02115, 2021.

[8] A. M. Childs, S.-H. Hung, T. Li. Quantum query complexity with matrix-vector products. arXiv:2102.11349, 2021.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
