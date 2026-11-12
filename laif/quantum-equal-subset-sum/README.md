# Equal Subset Sum with a quantum algorithm

Written 5 Nov 2026.

**Paper:** [`paper/main.pdf`](paper/main.pdf), with its source in [`paper/`](paper/).

Given integers x₁, …, x_n, find a nonzero D ∈ {−1,0,1}ⁿ with ⟨D, x⟩ = 0. For positive entries this is two disjoint nonempty subsets with equal sums.

**Theorem 1.** Equal Subset Sum has a quantum algorithm running in worst-case time O*(2^{0.4384n}), with quantum random access to quantum memory. It never outputs a non-solution, and it outputs a solution with probability at least 2/3 if one exists.

Status: Claim. The combinatorial lemmas and the composition of the costs are in Lean, with the quantum primitives as named hypotheses. The bound on the exponent is an interval arithmetic computation.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Exact exponential algorithms, quantum | Equal Subset Sum, worst case | 3^{2n/7} ≤ 2^{0.4529n}, implied by the proof of Theorem 4.2 of Chukhin et al. [1]; 2^{0.5044n} by Allcock et al. [2] | 2^{0.4384n} | Time with quantum random access to quantum memory; bounded error | Claim; lemmas and cost composition in Lean; exponent by interval arithmetic |

Classically, the best known bounds are 1.6994ⁿ ≤ 2^{0.7651n} [3] and (5/3)ⁿ ≤ 2^{0.7370n} [4], both Monte Carlo. No lower bound beyond the trivial is known, so this is a best known upper bound and not a tight one.

**Prior work.** Writing a solution as a difference of two vectors and filtering by a prime is from Mucha et al. [5]. The table of bin sizes with unranking is from Allcock et al. [2], who also cap a bin under the pigeonhole promise (their Theorem 6.3). Lists over {0,1,2} are from Randolph and Węgrzycki [6], and the labels A, B, C that make every matched pair valid are from Ye [4]. Fixing a prime and searching over residues with claw finding on bins is from Chukhin et al. [1], for k-SUM. To our knowledge, what is new here is the quantum exponent of the label scheme, the capped bins on arbitrary instances, and the combination with one table per partition.

## 1. Setup

If the entries have more than 2ⁿ bits, trying all 3ⁿ vectors is polynomial in the input length. Otherwise, by the reduction of [5], in the form of [4, Lemma 1.1], assume n + O(log n) entries of O(n) bits. The output is checked against the original instance.

Fix a nonzero solution D⋆ of minimum support, with z = pn zeros, and try all z. For uniform ε ∈ {±1}ⁿ put y_i = ε_i x_i and D_i = ε_i D⋆_i. Then ⟨D, y⟩ = 0, minimality is preserved, and with probability Ω(1/√n) the counts of +1 and −1 differ by at most 1.

## 2. The lists

Take a layout array on {−1,0,+1} × {A,B,C}:

| d | A | B | C |
|---|---|---|---|
| ±1 | a₁ | b₁ | b₁ |
| 0 | a₀ | b₀ | b₀ |

with 2a₁ + 4b₁ = 1 − p, a₀ + 2b₀ = p and b₁ > 0, and with either a₁, a₀ > 0 and p < 1/2, or a₁ = a₀ = 0. Put c_A = 2a₁ + a₀ and c_B = 2b₁ + b₀.

An integer layout ν_L(d) has the right sum over L for each d and stays within 2 of nΘ(d, L), with ν_A ≡ 0 if a₁ = a₀ = 0. One exists by rounding each row separately, since the column sums are free, and all O(1) of them are tried. A partition Π labels the coordinates with |L| = Σ_d ν_L(d). It is **good** if D has exactly ν_L(d) coordinates of value d on L. A uniform Π is good with probability 2^{−an}/poly(n), where a is the mutual information of value and label:

    a = H(c_A, c_B, c_B) − Σ_d Θ_d H(Θ(d,·)/Θ_d).

Let f = ⌊ν_A(0)/2⌋ and f′ = ν_A(0) − f.

- 𝒳: on A values in {0,1}, with ν_A(−1) + f zeros and ν_A(+1) + f′ ones; on B type (ν_B(−1), ν_B(0), ν_B(+1)) over (0,1,2); on C constant 1.
- 𝒴: on A values in {0,1}, with ν_A(+1) + f zeros and ν_A(−1) + f′ ones; on B constant 1; on C type (ν_C(+1), ν_C(0), ν_C(−1)) over (0,1,2).

Let U = max(|𝒳|, |𝒴|). Both sizes are 2^{un}/poly(n), with u = c_A + c_B H(b₁/c_B, b₀/c_B, b₁/c_B).

**Lemma 1 (validity).** For X ∈ 𝒳, Y ∈ 𝒴: X − Y ∈ {−1,0,1}ⁿ and X ≠ Y. So any X, Y with ⟨X,y⟩ = ⟨Y,y⟩ give a solution.

*Proof.* On A both lie in {0,1}. On B, Y = 1 and X ∈ {0,1,2}, and on C the reverse. Also ν_B(−1) ≥ b₁n − 2 > 0 for large n, so X has a zero on B, where Y = 1. ∎

**Lemma 2 (representations).** If Π is good, the pairs (X,Y) ∈ 𝒳 × 𝒴 with X − Y = D are in bijection with the subsets of size f of the zeros of D on A. So there are K = binom(ν_A(0), f) = 2^{a₀n}/poly(n) of them, with ⟨X,y⟩ = ⟨Y,y⟩, and the K values are pairwise distinct.

*Proof.* On B, Y = 1 forces X = D + 1, of the required type. On C, X = 1 forces Y = 1 − D, also of the required type. On A, D = −1 forces (0,1), D = +1 forces (1,0), and D = 0 leaves (0,0) or (1,1), with exactly f taking (0,0). If A is empty then K = 1. Otherwise two representations with equal value differ only on the zeros F of D on A, which gives a nonzero solution with support in F. But |F| = ν_A(0) ≤ z < n − z = |supp D| since p < 1/2, against minimality. ∎

**Table.** For a prime P, a dynamic program over the coordinates with state (position, number of each symbol used on each label, residue) has P poly(n) entries, and gives the size and the I-th element of 𝒳_ρ = {X ∈ 𝒳 : ⟨X,y⟩ ≡ ρ mod P} in poly(n) time. The same holds for 𝒴. This extends [2, Theorem 3.5].

## 3. The filter and the cap

Let s = 2^{σn} with σ ≥ 0, P₀ = Ks = 2^{Ω(n)}, P a uniform prime of [P₀, 2P₀], and T = ⌈c n U/P₀⌉ for a suitable constant c.

**Lemma 3 (filter).** Fix Π good. With probability at least 3/4 over P there is a set R of at least K/O(n) residues such that each ρ ∈ R has a representation of value v ≡ ρ for which at most T/2 elements of 𝒳_ρ and at most T/2 elements of 𝒴_ρ have an exact sum other than v.

*Proof.* A nonzero difference of values has O(1) prime divisors above P₀, and [P₀, 2P₀] has at least P₀/O(n) primes, so it vanishes mod P with probability at most O(n)/P₀. For a representation j of value v_j, let e_j count the elements of 𝒳 and 𝒴 with sum ≠ v_j and ≡ v_j. Then E_P[e_j] ≤ 2U · O(n)/P₀. The number Z of pairs of representations colliding mod P has E_P[Z] ≤ K² O(n)/P₀ ≤ K · O(n). So with probability at least 3/4 the mean of e_j is at most 16U O(n)/P₀ and Z ≤ 8K O(n). Then at least K′ ≥ K/2 representations have e_j ≤ T/2, and if they occupy M residues then K′²/M ≤ K′ + 2Z by convexity, so M ≥ K/O(n). ∎

**Lemma 4 (cap).** Fix ρ ∈ R, with T ≥ 1. Let W_X be the first T elements of 𝒳_ρ, or all of them if there are fewer, and define W_Y likewise. Then W_X and W_Y both contain an element of sum v.

*Proof.* Let C be the elements of 𝒳_ρ with sum v. It is nonempty, and at most T/2 elements lie outside it. If |𝒳_ρ| ≤ T then W_X ⊇ C. Otherwise W_X has T elements, at most T/2 of them outside C. The same holds for 𝒴_ρ. ∎

So a large class of equal sums does no harm.

## 4. The algorithm

The **base procedure** on a coin (Π, P, j):

1. Build the table, in P poly(n) time.
2. Run j iterations of Grover search over ρ ∈ Z_P, with j uniform below J = √(O(n)s). A residue is marked if claw finding [7] finds a pair in W_X × W_Y with equal exact sums, in Õ(T^{2/3}) time. Windows are padded to length T with tagged values that cannot collide. Claw finding is repeated O(n) times, so its error probability is much smaller than 1/J².
3. Verify the pair, undo ε, restrict to the original coordinates, and raise the flag if it is a solution.

This is a unitary of fixed running time. If Π is good then, with probability at least 3/4 over P, the fraction of marked residues is at least 1/(O(n)s), and a uniform j gives constant success. So a uniform coin raises the flag with probability at least 2^{−an}/poly(n). **Amplitude amplification** over the coin runs it forward and backward, which also uncomputes the table. Repeating over the O(√n) draws of ε and over the polynomially many z and ν gives success at least 2/3. The total exponent is

    L = a/2 + max(a₀ + σ, σ/2 + (2/3)(u − a₀ − σ)).

Balancing gives σ = (4u − 10a₀)/7, when this is nonnegative, and L = a/2 + (4u − 3a₀)/7.

**Empty label.** For a₁ = a₀ = 0, split the coordinates evenly between B and C. Then a = 0, a partition is good with probability 1/poly(n), K = 1 and u = (h(p) + 1 − p)/2, so

    L = S(p) = (2/7)(h(p) + 1 − p),

with maximum (2/7) log₂ 3 at p = 1/3. This proves 3^{2n/7} with a table, a search over residues and claw finding. The same steps for Subset Sum, with X and Y over the subsets of two halves and 𝒴_ρ = {Y : t − ⟨Y,x⟩ ≡ ρ}, give an alternative proof of the time 2^{2n/7} of [1], with neither 7-SUM nor a dictionary on four blocks.

## 5. The exponent

S increases on [0, 1/3] and decreases on [1/3, 1], with S(0.2) < 0.4349 and S(0.47) < 0.4365.

- p ≥ 0.99: Grover search over the typed vectors D, exponent below 0.05.
- p ≤ 0.2 or 0.47 ≤ p < 0.99: the empty label, exponent S(p).
- 0.2 < p < 0.47: the array below, interpolated in p.

| p | a₁ | a₀ | b₁ | b₀ | a | u | σ | L |
|---|---|---|---|---|---|---|---|---|
| 0.20 | 0.0551 | 0.0665 | 0.1724 | 0.0668 | 0.0266 | 0.7848 | 0.3535 | 0.4333 |
| 0.25 | 0.1280 | 0.1544 | 0.1235 | 0.0478 | 0.0422 | 0.8459 | 0.2628 | 0.4383 |
| 0.30 | 0.2009 | 0.2423 | 0.0746 | 0.0289 | 0.0384 | 0.9070 | 0.1722 | 0.4336 |
| 0.36 | 0.2883 | 0.3400 | 0.0159 | 0.0100 | 0.0044 | 0.9814 | 0.0751 | 0.4173 |
| 0.42 | 0.2642 | 0.3935 | 0.0129 | 0.0132 | 0.0017 | 0.9838 | 0.0000 | 0.3944 |
| 0.47 | 0.2111 | 0.3821 | 0.0270 | 0.0439 | 0.0003 | 0.9553 | 0.0000 | 0.3823 |

`sim/certify.py` covers [0.2, 0.47] with interval arithmetic and adaptive bisection, and gets L ≤ 0.4384, with all array entries positive. The worst point is near p = 0.2498, with L ≈ 0.43831 and a table of about 2^{0.4172n} entries. As a check on the formulas, the classical cost a + u − a₀, minimized over the same family of arrays, has value log₂(5/3) at p = 1/5, the exponent of [4].

Without labels, that is X, Y ∈ {0,1}ⁿ and K = 2^{pn}, with element distinctness on one window, the same steps give (4 − 3p)/7 for p ≤ 2/5. For a maximum solution ratio ℓ = 1 − p ≥ 3/5 this is (1 + 3ℓ)/7, against ℓ/2 + 1/10 in [2, Theorem 5.5], and with the empty label it gives 0.4504.

## 6. Measurements

`sim/check.py` and `sim/check_empty.py` replace the quantum searches by exhaustive classical ones and run on planted instances at n ≤ 24, including odd support and instances built with large classes of equal sums. Every equal-sum pair verified at n ≤ 20 is a real solution, the K representations have distinct sums, and the fraction of working residues is above 1/(ns). These sizes test the structure of the lists only, and K is small there. They say nothing about the asymptotic exponent. `sim/opt.py`, `sim/opt2.py` and `sim/exact.py` compute and optimize the exponents.

`sim/qiskit_check.py` runs the three nested searches as Qiskit circuits in Aer, noiseless, at up to 21 qubits: amplitude amplification over a list of 4 partitions, quantum search over residues, and a quantum walk for the claw in windows of T = 4. The walk alone also runs at T = 8, with 23 qubits.

| Instance | n | Marked (coin, residue) | Blind draw | + walk | + residues | + coin | Mean runs to a solution |
|---|---|---|---|---|---|---|---|
| Labels | 10 | 4/64 | 0.016 | 0.057 | 0.244 | 1.000 | 2.6 |
| Labels, large classes of equal sums | 10 | 3/64 | 0.015 | 0.033 | 0.214 | 0.984 | 2.3 |
| Empty label | 12 | 1/256 | 0.001 | 0.004 | 0.078 | 0.563 | 6.5 |

The columns give the exact probability of a real solution in one run, with the best j ≤ 2 and k ≤ 1 for the last two. The mean runs draw j and k at random for each run, over 50 repetitions, and every output is a real solution. The amplification agrees with sin²(3θ) to within 10⁻¹³, and the cap bites on every instance. Instances with no solution never pass the final check.

This tests the construction on tiny instances, not the exponent. The table and the windows are read through a diagonal gate computed classically, so there is no quantum memory and no data register. Subset states are prepared by a dense gate, and j and k are drawn classically and not held in the coin. P and T are set to fit the qubits, not to the balance of the proof. Claw finding is not repeated, and in the nested runs its step counts are fixed for one claw: on one claw they lift 0.250 to 0.906 at T = 4, and on two claws they give 0.283 against 0.472 with no walk. This is the usual effect of a fixed iteration count on an unknown number of solutions. The cited claw finding handles any number of claws, and the same walk with a uniform number of rounds below 8 keeps a mean success of at least 0.43 on the patterns tested (one pair, two disjoint pairs, a star, a 2×2 block).

## 7. Limits

- Time with quantum random access to quantum memory, which [1] and [2] also use. The table has about 2^{0.4172n} entries. No claim is made for a model without such memory, and there is no gate count.
- The exponent is computed in floating-point interval arithmetic, which is not a formal proof.
- Claw finding, amplitude amplification, the table, the reduction to short entries and the integer layout are cited.
- This is an asymptotic bound with polynomial factors unoptimized. It says nothing about instances that fit on current devices.

## 8. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry`, `axiom` or `native_decide` in the sources. `lake env lean EqualSubsetSum/Axioms.lean` prints the axioms of 61 theorems: only `propext`, `Classical.choice` and `Quot.sound`, and subsets of those.

| Part | Theorems | Hypotheses |
|---|---|---|
| Lemma 1, sign flip | `sub_trinary`, `validity`, `MinimalSolution.flip` | |
| Lemma 2 | `repX_isX`, `repY_isY`, `repOf_bijOn`, `card_reps`, `card_free_lt_supp`, `value_injOn` | |
| Lemma 3 | `averaging`, `markov`, `cauchy_classes`, `classes_lower_bound`, `card_prime_divisors_le`, `filter_lemma`, `filter_lists` | `PrimeCount` |
| Lemma 4 | `cap_lemma`, `card_firstWindow`, `pairFound_of_good` | |
| Marked fraction, iterations | `marked_fraction`, `grover_average`, `grover_uniform` | |
| Coin | `coin_success`, `coin_mean`, `coin_mean_minimal`, `coin_mean_empty` | `GroverSuccess` |
| Exponent | `balance`, `balance_optimal`, `total_exponent`, `total_exponent_balanced` | `TableBuild`, `Unranking`, `ClawWindows`, `GroverResidues`, `AmplitudeAmplification` |
| Empty label | `listExp_empty`, `empty_label_exponent`, `emptyExp_one_third`, `total_exponent_empty` | as above |
| Probability with cost | `coin_cost` | as above |

**Assuming.** The hypotheses are named in `lean/EqualSubsetSum/Model.lean`. They bound cost functions in a record `Primitives`, with no circuit model, and `hypotheses_satisfiable` shows that those on `Primitives` are consistent. So `coin_cost` links the two bounds numerically, and it does not state that the procedure amplified there is the search of `coin_mean`. A residue is marked in Lean if a pair exists in the windows. The probability of a good partition and the exponent of the lists enter as arguments.

**Not formalized.** The assembly into Theorem 1, the quantum primitives themselves (including the success of claw finding, the correctness of unranking and coherent coin preparation), the link from the search to the flag, the probability of balanced signs, the outer loop over ε, z and ν, the existence of the integer layout, the reduction to short entries, the case p ≥ 0.99, the monotonicity of S, and the numerical bound 0.4384.

## References

1. N. Chukhin, A. S. Kulikov, M. Levitskii, I. Mihajlin. Improved quantum algorithms for Subset Sum and k-SUM. arXiv:2608.07309.
2. J. Allcock, Y. Hamoudi, A. Joux, F. Klingelhöfer, M. Santha. Classical and quantum algorithms for variants of Subset-Sum via dynamic programming. ESA 2022, arXiv:2111.07059.
3. R. Yamano, T. Shibuya. Faster exact algorithms for Equal-Subset-Sum. arXiv:2607.09289.
4. L. Ye. An O((5/3)ⁿ poly(n)) one-sided Monte Carlo algorithm for Equal Subset Sum. arXiv:2608.08260.
5. M. Mucha, J. Nederlof, J. Pawlewicz, K. Węgrzycki. Equal-Subset-Sum faster than the meet-in-the-middle. ESA 2019, arXiv:1905.02424.
6. T. Randolph, K. Węgrzycki. Beating meet-in-the-middle for subset balancing problems. STOC 2026, arXiv:2511.10823.
7. S. Tani. Claw finding algorithms using quantum walk. Theoretical Computer Science 410, 2009.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
