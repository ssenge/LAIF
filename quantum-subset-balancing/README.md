# Subset Balancing with small coefficients, with a quantum algorithm

Written 5 Nov 2026.

**Paper:** [`paper/main.pdf`](paper/main.pdf), with its source in [`paper/`](paper/).

Given integers x₁, …, x_n and a constant d ≥ 1, find a nonzero D ∈ {−d, …, d}ⁿ with ⟨D, x⟩ = 0. Write [−d:d] for the coefficient set. For d = 1 this is Equal Subset Sum.

**Theorem 1.** Subset Balancing on [−2:2] has a quantum algorithm running in worst-case time O*(2^{0.6125n}), and Subset Balancing on [−3:3] one running in time O*(2^{0.7215n}), with quantum random access to quantum memory. Both never output a non-solution, and output a solution with probability at least 2/3 if one exists.

**Theorem 2.** For every constant d, the same method with no representations gives O*((2d+1)^{2n/7}) directly, with a table, a search over residues and claw finding.

Status: Claim. The combinatorial lemmas, the concavity behind the certificate and the composition of the costs are in Lean, with the quantum primitives as named hypotheses. The bound on the exponent is an interval arithmetic computation.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Exact exponential algorithms, quantum | Subset Balancing on [−2:2], worst case | 5^{2n/7} ≤ 2^{0.6634n}, implied by Chukhin et al. [1] | 2^{0.6125n} | Time with quantum random access to quantum memory; bounded error | Claim; lemmas and cost composition in Lean; exponent by interval arithmetic |
| Exact exponential algorithms, quantum | Subset Balancing on [−3:3], worst case | 7^{2n/7} ≤ 2^{0.8021n}, implied by Chukhin et al. [1] | 2^{0.7215n} | As above | As above |

The bound of [1] follows from seven blocks of size n/7, lists of (2d+1)^{n/7} entries and worst-case 7-SUM in time Õ(M²) (their Theorem 1.2), with one coordinate forced to be nonzero as in the proof of their Theorem 4.2.

Classically, meet in the middle gives (2d+1)^{n/2}, and O*(|C|^{(0.5−ε)n}) for a constant ε depending on d is due to Randolph and Węgrzycki [2], with 2^{1.108n} at d = 2. Gao, Feng, Hu and Pan [3] give a randomized 2^{2.443n} for every d, through lattices, and polynomial time for sufficiently large d. So the comparison here concerns small constant d, and no statement is made for large d. To our knowledge there is no earlier quantum bound stated for this problem. No lower bound beyond the trivial is known, so this is a best known upper bound and not a tight one.

**Prior work.** The problem was studied on average-case instances by Chen et al. [9]. Writing a solution as a difference of two vectors and filtering by a prime goes back to Mucha et al. [4], and the extension of representations to Subset Balancing to [2]. The table of bin sizes with unranking is from Allcock et al. [5]. Labels that make every matched pair valid are from Ye [6], for d = 1. Fixing a prime and searching over residues with claw finding on bins is from [1], for k-SUM. To our knowledge, what is new here is the family of interval labels over [−d:d], the pinned coordinate, the capped bins on arbitrary instances for d ≥ 2, the exponent, and the concavity certificate over all solution profiles.

## 1. Setup

**Short entries.** If the entries have more than (2d+1)ⁿ bits, trying all vectors is polynomial in the input length. Otherwise draw a uniform prime q from [Q, 2Q] with Q = Θ(n(2d+1)^{2n}), replace the entries by x_i mod q, and append aux entries q(2d+1)^i for i < m, with (2d+1)^m ≥ 2dn + 1. A solution of the new instance restricted to the first n coordinates is nonzero, since balanced digits in base 2d+1 are unique, and it satisfies ⟨D, x⟩ ≡ 0 mod q. Conversely ⟨D, x mod q⟩ = kq with |k| ≤ dn is absorbed by the aux digits, so every old solution extends. A nonzero value has O((2d+1)ⁿ) prime divisors above Q, and [Q, 2Q] has at least Q/O(n) primes, so by a union bound over the (2d+1)ⁿ vectors every solution mod q is a real one with high probability. The output is checked against the original. Entries have O(n) bits, and n grows by O(log n), which changes the time by a polynomial factor.

**Minimum support.** Fix a nonzero solution D⋆ of minimum support and try all profiles of counts of values, polynomially many. For uniform ε ∈ {±1}ⁿ put y_i = ε_i x_i and D_i = ε_i D⋆_i. Then ⟨D, y⟩ = 0, minimality is preserved, and with probability 1/poly(n) the counts of c and −c differ by at most one for each c. So the profile π on [−d:d] is symmetric up to O(1/n).

**Pin.** Guess a coordinate i⋆ with c⋆ = D_{i⋆} ≠ 0. Every X below has X_{i⋆} = c⋆, every Y has Y_{i⋆} = 0, and i⋆ gets no label.

## 2. The lists

A **label** is a pair of nonempty integer intervals L = (S_L, T_L) with S_L − T_L inside [−d:d]. So the widths s = |S_L| − 1 and t = |T_L| − 1 have s + t ≤ 2d, hence min(s, t) ≤ d. We use the 2d + 1 wide labels S = [0:s], T = [s − d : d], for s = 0, …, 2d, so s + t = 2d.

A **layout** is a law q on triples (L, x, y) with x ∈ S_L and y ∈ T_L, whose marginal on c = x − y is π. An **integer layout** is a family of nonnegative integers ν_L(x, y) within O(1) of n q(L, x, y), zero where q is zero, with Σ_{L, x−y=c} ν_L(x, y) equal to the number of coordinates other than i⋆ with D_i = c. One exists by rounding each row c. There are O(1) of them per law, and all are tried.

A **partition** Π assigns labels to the coordinates with |L| = Σ_{x,y} ν_L(x, y). It is **good** if for all L and c, D has exactly ν_L(c) = Σ_{x−y=c} ν_L(x, y) coordinates of value c on L. A uniform Π is good with probability 2^{−an}/poly(n), with a = I(C; L) under q.

X belongs to the list 𝒳 if on each L it has, for each symbol s, exactly Σ_y ν_L(s, y) coordinates of value s, and X_{i⋆} = c⋆. Y belongs to 𝒴 if on each L it has, for each s, exactly Σ_x ν_L(x, s) coordinates of value s, and Y_{i⋆} = 0. The sizes are 2^{u_x n}/poly(n) and 2^{u_y n}/poly(n), with u_x = H(x | L) and u_y = H(y | L). Let U be the larger size and u = max(u_x, u_y).

**Lemma 1 (validity).** For X ∈ 𝒳, Y ∈ 𝒴: X − Y ∈ [−d:d]ⁿ and X ≠ Y. So any X, Y with ⟨X, y⟩ = ⟨Y, y⟩ give a solution.

*Proof.* On L, x − y ∈ S_L − T_L. At i⋆ the difference is c⋆, nonzero, and in [−d:d]. ∎

**Representations.** R is the set of (X, Y) with X − Y = D such that for each L and each (x, y), exactly ν_L(x, y) coordinates of L have (X_i, Y_i) = (x, y), and (X_{i⋆}, Y_{i⋆}) = (c⋆, 0). Then R ⊂ 𝒳 × 𝒴, and |R| = K is a product of multinomials over the pairs (L, c), so K = 2^{a₀n}/poly(n) with a₀ = H(x, y | C, L). Let F be the set of coordinates in classes (L, c) with at least two positive ν_L(x, y) over x − y = c.

**Lemma 2.** If Π is good and |F| < |supp D|, the K values ⟨X, y⟩ over R are pairwise distinct, and ⟨X, y⟩ = ⟨Y, y⟩ on R.

*Proof.* ⟨X, y⟩ − ⟨Y, y⟩ = ⟨D, y⟩ = 0. Suppose (X, Y) ≠ (X′, Y′) in R have equal values. Then E = X − X′ = Y − Y′ is nonzero. On a coordinate of L, |E_i| ≤ min(s_L, t_L) ≤ d, since E_i is a difference within S_L and within T_L. Outside F the pair is forced, so E_i = 0, and i⋆ lies outside F. So E is a nonzero solution in [−d:d]ⁿ with support in F, against minimality. ∎

**Table.** For a prime P, a dynamic program over the coordinates with state (position, number of each symbol used on each label, residue) has P poly(n) entries, and gives the size and the I-th element of 𝒳_ρ = {X ∈ 𝒳 : ⟨X, y⟩ ≡ ρ mod P} in poly(n) time. The same holds for 𝒴. This extends [5, Theorem 3.5]. The number of counters is constant since d is.

## 3. The filter and the cap

Let s = 2^{σn} with σ ≥ 0, P₀ = Ks = 2^{Ω(n)}, P a uniform prime of [P₀, 2P₀], and T = ⌈c n U/P₀⌉.

**Lemma 3 (filter).** Fix Π good with |F| < |supp D|. With probability at least 3/4 over P there is a set R′ of at least K/O(n) residues such that each ρ ∈ R′ has a representation of value v ≡ ρ for which at most T/2 elements of 𝒳_ρ and at most T/2 elements of 𝒴_ρ have an exact sum other than v.

*Proof.* Values have O(n) bits, so a nonzero difference has O(1) prime divisors above P₀, and there are at least P₀/O(n) primes. For a representation j of value v_j, let e_j count elements of 𝒳 and 𝒴 with sum ≠ v_j and ≡ v_j mod P: E[e_j] ≤ 2U · O(n)/P₀. Let Z count pairs of representations colliding mod P: E[Z] ≤ K² O(n)/P₀ ≤ K · O(n), using s ≥ 1 and Lemma 2. With probability at least 3/4 the mean of e_j is at most 16U O(n)/P₀ and Z ≤ 8K O(n). So at least K′ ≥ K/2 representations have e_j ≤ T/2, and if they occupy M residues then K′²/M ≤ K′ + 2Z, so M ≥ K/O(n). ∎

**Lemma 4 (cap).** Fix ρ ∈ R′ and T ≥ 1. The first T elements W_X of 𝒳_ρ, or all of them if there are fewer, contain an element of sum v, and likewise W_Y.

*Proof.* Let C be the elements of sum v, nonempty. At most T/2 elements lie outside C. ∎

By Lemma 1 every pair with equal sums is a solution, so a large class of equal sums does no harm.

## 4. The algorithm

The **base procedure** on a coin (Π, P, j):

1. Build the table, in P poly(n) time.
2. Run j iterations of quantum search over ρ ∈ Z_P, with j uniform below J = √(O(n)s). A residue is marked if claw finding [7] finds a pair in W_X × W_Y with equal exact sums, in Õ(T^{2/3}) time. Windows are padded to length T with tagged values that cannot collide. Claw finding is repeated O(n) times, with a constant large enough that the error of one check is below 2^{−2en}, for e the total exponent.
3. Verify the pair, undo ε, restrict to the original coordinates, and raise the flag if it is a solution.

If Π is good then, with probability at least 3/4 over P, the marked fraction is at least 1/(O(n)s). So a uniform coin raises the flag with probability at least 2^{−an}/poly(n). Amplitude amplification over the coin gives

    L = a/2 + max(a₀ + σ, σ/2 + (2/3) max(0, u − a₀ − σ)).

Balancing gives σ = (4u − 10a₀)/7, when this is nonnegative, and L = a/2 + (4u − 3a₀)/7.

**Empty scheme.** Take q on the labels ([0:2d], {d}) and ({d}, [0:2d]), with weight 1/2 each, independent of c. Then a = 0, K = 1, F is empty and u = H(π)/2, so L = (2/7)H(π) ≤ (2/7) log₂(2d + 1) at σ = 4u/7. This proves Theorem 2.

**Typed search.** Quantum search over typed vectors D has exponent H(π)/2.

## 5. The exponent

**Proposition 2 (concavity).** Fix a kernel W(L, x, y | c). As functions of π, a = H(L) − Σ_c π_c H(L | c) is concave, a₀ = Σ_c π_c H(x, y | L, c) is linear, and u_x, u_y are concave, since conditional entropy is concave in the joint law and the joint is linear in π. So with σ fixed each of

- a/2 + a₀ + σ,
- a/2 + σ/2 + (2/3)(u_x − a₀ − σ), the same with u_y,
- a/2 + σ/2

is concave in π, and L equals their maximum. A tangent at the centre of a box bounds each term from above on the box, and a linear function is largest at a corner. |F|/n and a₀ + σ are linear in π, so the side conditions reduce to corners.

**Certificate.** `sim/certify.py` covers the simplex of (w₁, …, w_d), with w_c = π_c + π_{−c}, by adaptive boxes, each with typed search, the empty scheme, or a kernel solved at its centre over the wide labels. `sim/verify.py` re-evaluates each box in interval arithmetic: the boxes cover the simplex, every entry is nonnegative, every value has a row of the kernel, σ ≥ 0, all tangent bounds hold at all corners, a₀ + σ > 0, and |F| < |supp D|. It shares only the label set with `certify.py`.

| d | Previous best bound | Certified | Boxes | Worst profile found (w₀, w₁, …) | a | a₀ | u | σ | L there |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 0.6634 | 0.6125 | 2596 | (0.1377, 0.2962, 0.5661) | 0.0528 | 0.3850 | 1.3133 | 0.2005 | 0.6119 |
| 3 | 0.8021 | 0.7215 | 25049 | (0.0942, 0.1897, 0.2343, 0.4818) | 0.0487 | 0.5655 | 1.6389 | 0.1287 | 0.7185 |

The profile is symmetric only up to O(1/n), and the types round within O(1). This changes every exponent by o(1), which the margin in each box absorbs. For d = 1 the same run gives 0.4386, in 70 boxes, close to the bound 0.4384 of [8] from a three-label family.

`sim/curves.py` gives the worst exponent for a fixed weight w₀ of the value 0, on a grid, in `sim/curves_2.dat` and `sim/curves_3.dat`, with the empty scheme alongside. The table has about 2^{(a₀+σ)n} entries, so 2^{0.586n} at the worst d = 2 profile and 2^{0.694n} at the worst d = 3 profile.

## 6. Measurements

`sim/check.py` replaces the quantum searches by exhaustive classical ones, on planted instances with a pinned coordinate at d = 2, 3 and n ≤ 12. Every pair with equal sums has X ≠ Y and a difference in [−d:d]ⁿ. The representations in R of a minimum-support solution have distinct sums. On instances with pairs (g, (d + 1)g), which give many equal sums inside the lists, bins are capped, and Lemma 4 is asserted wherever its condition holds. A further test plants a dependency equal to the difference E of two representations, and confirms that E lies in [−d:d]ⁿ with support in F and is a real solution. These sizes test the structure of the lists, and K is small there. They say nothing about the asymptotic exponent.

`sim/qiskit_check.py` runs the three nested searches as Qiskit circuits in Aer, noiseless, at up to 20 qubits: amplitude amplification over a list of 4 partitions, quantum search over residues, and a quantum walk for the claw in windows of T = 4.

| Instance | n | Marked (coin, residue) | Blind draw | + walk | + residues | + coin | Mean runs to a solution |
|---|---|---|---|---|---|---|---|
| d = 2, uniform profile | 9 | 1/128 | 0.002 | 0.007 | 0.136 | 0.822 | 4.2 |
| d = 2, worst profile | 9 | 1/128 | 0.002 | 0.007 | 0.136 | 0.822 | 4.0 |
| d = 3, uniform profile | 8 | 1/128 | 0.002 | 0.007 | 0.136 | 0.822 | 3.6 |
| d = 2, many zeros | 9 | 1/64 | 0.004 | 0.014 | 0.206 | 0.975 | 3.0 |

The columns give the exact probability of a real solution in one run, with the best j ≤ 2 and k ≤ 1 for the last two. Equal fractions of marked pairs give equal probabilities, which is why three rows agree. The mean runs draw j and k at random for each run, over 50 repetitions, and every output is a real solution. The amplification agrees with sin²(3θ) to within 10⁻¹³. An instance with no solution is never flagged.

This tests the construction on tiny instances, not the exponent. The table and the windows are read through a diagonal gate computed classically, so there is no quantum memory and no data register. Subset states are prepared by a dense gate, and j and k are drawn classically and not held in the coin. P and T are set to fit the qubits, not to the balance of the proof. Claw finding is not repeated, and in the nested runs its step counts are fixed for one claw: on one claw they lift 0.250 to 0.906, and on two claws they give 0.283 against 0.472 with no walk. This is the usual effect of a fixed iteration count on an unknown number of solutions. The cited claw finding handles any number of claws, and the same walk with a uniform number of rounds below 8 keeps a mean success of at least 0.42 on the patterns tested (one pair, two disjoint pairs, a star, a 2×2 block).

To reproduce the certificate, run `python certify.py d target`, then `python verify.py d`, in `sim/`. `sim/verify.log` holds the result for d = 1, 2, 3. The targets are 0.4386, 0.6125 and 0.7215.

## 7. Limits

- Time with quantum random access to quantum memory, which [1] and [5] also use. The table is exponential. No claim is made for a model without such memory, and there is no gate count.
- Theorem 1 is stated for d = 2 and d = 3, where the computation was carried out. The method applies to each fixed d, and each needs its own computation.
- The exponent is computed in interval arithmetic, which is not a formal proof.
- Claw finding, amplitude amplification, the table, the reduction to short entries and the integer layout are cited or argued here, not formalized.
- This is an asymptotic bound with polynomial factors unoptimized. It says nothing about instances that fit on current devices.
- The coefficient sets [±d], with no zero, are not covered. There a difference of two representations can have zeros, so it need not be a solution.

## 8. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry`, `axiom` or `native_decide` in the sources. `lake env lean SubsetBalancing/Axioms.lean` prints the axioms of 100 theorems: only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

| Part | Theorems | Hypotheses |
|---|---|---|
| Lemma 1, pin, sign flip | `sub_inBox`, `ne_of_pin`, `validity`, `MinimalSolution.flip` | |
| Widths of labels | `Label.width_add_le`, `Label.min_width_le`, `Label.abs_exchange_le`, `Label.wide_inside` | |
| Lemma 2 | `no_two_representations`, `forced_off_free`, `value_injOn`, `value_eq` | |
| Count of K | `fst_bijOn`, `card_reps`, `card_free`, `card_typed` | |
| Lemma 3 | `averaging`, `markov`, `cauchy_classes`, `classes_lower_bound`, `card_prime_divisors_le`, `filter_lemma`, `filter_lists` | `PrimeCount` |
| Lemma 4 | `cap_lemma`, `card_firstWindow`, `pairFound_of_good` | |
| Marked fraction, iterations | `marked_fraction`, `grover_average`, `grover_uniform` | |
| Coin | `coin_success`, `coin_mean`, `coin_mean_minimal`, `coin_mean_empty` | `GroverSuccess` |
| Exponent | `totalExp_eq_terms`, `balance`, `balance_optimal`, `schedule_exponents`, `total_exponent`, `total_exponent_balanced` | `TableBuild`, `Unranking`, `ClawWindows`, `GroverResidues`, `AmplitudeAmplification` |
| Empty scheme | `free_empty_scheme`, `K_eq_one`, `empty_scheme_exponent`, `total_exponent_empty` | as above |
| Probability with cost | `coin_cost` | as above |
| Proposition 2 | `tangent_le`, `linear_le_corner`, `a₀Exp_linear`, `entL_concave`, `aExp_concave`, `listEnt_concave`, `term_table_concave`, `term_search_concave`, `term_half_concave`, `exponent_box_bound` | Derivatives at the centre |

**Assuming.** The hypotheses are named in `lean/SubsetBalancing/Model.lean`. They bound cost functions in a record `Primitives`, with no circuit model, and `hypotheses_satisfiable` shows that those on `Primitives` are consistent. So `coin_cost` links the two bounds numerically, and it does not state that the procedure amplified there is the search of `coin_mean`. A residue is marked in Lean if a pair exists in the windows. The probability of a good partition and the entropy forms of K and of the list sizes enter as arguments.

**Not formalized.** The assembly into Theorem 1, the quantum primitives themselves (including the success of claw finding, the correctness of unranking and coherent coin preparation), the link from the search to the flag, the dynamic program of the table, the probability of balanced signs, the outer loop, the integer layout, the reduction to short entries, the derivatives of the entropy terms at the centre of a box, and the certificate with its numerical bounds.

## References

1. N. Chukhin, A. S. Kulikov, M. Levitskii, I. Mihajlin. Improved quantum algorithms for Subset Sum and k-SUM. arXiv:2608.07309.
2. T. Randolph, K. Węgrzycki. Beating meet-in-the-middle for subset balancing problems. STOC 2026, arXiv:2511.10823.
3. Y. Gao, Y. Feng, H. Hu, Y. Pan. Subset Balancing and Generalized Subset Sum via Lattices. arXiv:2604.04656.
4. M. Mucha, J. Nederlof, J. Pawlewicz, K. Węgrzycki. Equal-Subset-Sum faster than the meet-in-the-middle. ESA 2019, arXiv:1905.02424.
5. J. Allcock, Y. Hamoudi, A. Joux, F. Klingelhöfer, M. Santha. Classical and quantum algorithms for variants of Subset-Sum via dynamic programming. ESA 2022, arXiv:2111.07059.
6. L. Ye. An O((5/3)ⁿ poly(n)) one-sided Monte Carlo algorithm for Equal Subset Sum. arXiv:2608.08260.
7. S. Tani. Claw finding algorithms using quantum walk. Theoretical Computer Science 410, 2009.
8. S. Senge. A faster quantum algorithm for Equal Subset Sum. In this repository, [quantum-equal-subset-sum](../quantum-equal-subset-sum/).
9. X. Chen, Y. Jin, T. Randolph, R. A. Servedio. Average-case subset balancing problems. SODA 2022.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
