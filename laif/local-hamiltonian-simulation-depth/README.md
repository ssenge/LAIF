# Depth of geometrically local Hamiltonian simulation with long blocks

Written 26 Nov 2026.

A geometrically local Hamiltonian H acts on n qubits placed on the sites of a D-dimensional cubic lattice. Every term has a support of bounded diameter, and the local strength is at most one (the terms containing any one site have total norm at most one). The task is a circuit of nearest-neighbour gates that approximates e^{−iHT} to operator-norm error ε. Write m = log(nT/ε).

The best known circuits have depth O(T log(nT/ε)) and O(nT log(nT/ε)) gates [1], improving the depth O(T log^D(nT/ε)) of [2]. The depth lower bound of [1] adds the two scales: Ω(min{ℓ_sys, T + m′/log(e + m′/T)}) with m′ = log(n/ε) and lattice side ℓ_sys, under the conditions of [1, eq. (147)]. The joint dependence on T and ε is stated in [1] as a remaining question.

The circuits of [1] first cut the evolution into steps of time at most 1 by the Lieb-Robinson decomposition of [2]. They then simulate each block of side Θ(m) with a fixed-order product formula whose residual is removed by a linear combination of unitaries, at depth O(m) per block. Here the blocks keep side Θ(m log m), but each step is long: its time τ is the largest one for which the many product-formula steps of a block still fit the control distribution of [1]. The coefficient sum of the correction stays bounded, and the per-block cost of the correction is spread over the time τ instead of a unit time.

**Theorem 1.** Fix D ≥ 1 and an even integer p > D, and let δ = (D+1)/(p+1). If the lattice side is at least a constant times m log m, there is a nearest-neighbour circuit with operator-norm error at most ε, O(n) ancillas, and

- depth O_p(T · m^δ (log m)^{1+D/(p+1)} + m log m), and
- O_p(n (T · m^δ (log m)^{1+D/(p+1)} + m log m)) gates.

**Corollary 2.** For every fixed δ′ > 0 there is a constant C_{δ′} such that, under the lattice condition of Theorem 1, depth at most C_{δ′}(T · m^{δ′} + m log m) and n times as many gates suffice. This takes p > (D+1)/δ′ − 1 and absorbs the logarithmic factor.

Status: Claim. The parameter arithmetic (size condition, coefficient condition, exponent, depth sum, with a concrete instance) is checked in Lean, and the parameter conditions for concrete values by a script with asserts.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Depth for e^{−iHT}, geometrically local H in D dimensions, error ε | O(T m) [1] | O_{δ′}(T m^{δ′} + m log m) for every δ′ > 0 |
| Gates, same setting | O(n T m) [1] | O_{δ′}(n (T m^{δ′} + m log m)) for every δ′ > 0 |

## 1. Long steps

For a time t with |t| ≤ τ, the evolution of the whole lattice is approximated by a constant number of layers of forward and inverse block evolutions, as in [2] and [1, Lemma 4], with error C n |t| e^{v′|t| − μ ℓ_buf}. Here ℓ_buf is the buffer width, the blocks have sides between ℓ_buf and C ℓ_buf, and C, μ and v′ depend only on the local model. The proof of [1, Lemma 4] in [1, Appendix D] uses |t| ≤ 1 at two points only. The first is the Lieb-Robinson tail Σ_{k ≥ d/R} (2ν|t|)^k/k! ≤ e^{−μd} exp(2ν e^{μR} |t|), which holds for every t and gives v′ = 2ν e^{μR}. The second is the factor |t| in the Duhamel bound. The strip widths, the slab identities and the number of layers do not depend on t. A buffer ℓ_buf ≥ C(τ + m) therefore keeps the error of all ⌈T/τ⌉ steps below ε/4, and the choice of τ below has τ ≤ ℓ.

## 2. One long block

Let a block have side ℓ and volume v = ℓ^D, and let it evolve for a time τ. With r steps of length h = τ/r, e^{−iH_blk τ} = (C(h) E(h))^r exactly, where C is the order-p product formula and E(s) = C(s)^† e^{−iH_blk s} is its residual. The construction of [1, Sections 3 to 5] is used with these changes.

- The residual table [1, Lemma 7] is an identity for every s. Its entries do not depend on r or τ.
- The label states of [1, Section 3.3] are defined for every r. They use N = r + K₀ slots with K₀ = ⌊Q/(p+1)⌋, and the normalization 2 comes from (1 − a)^r = 1/2 for every r.
- In the error and coefficient bounds [1, Lemma 10], take ξ = e and Q = m + O(1). The condition r A(ξ) ≤ 1/8 reads v τ^{p+1}/r^p ≤ c_p, so r = Θ_p(τ (vτ)^{1/p}) steps suffice. Then h ≤ 1/Θ_p(1), so t_ω ξ ≤ 1/2 holds as well, and the truncation error is at most 4e^{−Q}.
- The control distribution of [1, Lemma 12] for D ≥ 2, and of [1, Lemma 26] for D = 1, needs N w + w log ℓ = O(ℓ), with records of width w = Θ(log ℓ) that hold the address, offset, phase and count fields of [1, eq. (96)], and (L+1) N w = O(ℓ) for D = 1, where L is the number of stages of the product formula. These lemmas then give depth O(ℓ + N w) = O(ℓ), O(ℓ^{D+1}) gates and O(ℓ^D) ancillas.
- The source computations of [1, Sections 4.3 and 4.4] have depth O(N w + Q w) = O(ℓ) and O(N Q w) = O(ℓ m) gates. One round of oblivious amplitude amplification [1, Section 5.1] uses a constant number of calls.

**Parameters.** The degree threshold forces ℓ ≥ Q w, so take ℓ = Θ_p(m log m). With a = Θ_p(w), the size condition is a·τ^{(p+1)/p} ℓ^{D/p} ≤ ℓ, and the largest step time is τ = ℓ^{(p−D)/(p+1)} a^{−p/(p+1)}. At this τ the size condition holds with equality, the coefficient ratio v τ^{p+1}/r^p is constant, and

ℓ/τ = ℓ^{(D+1)/(p+1)} a^{p/(p+1)} = Θ_p(m^δ (log m)^{1+D/(p+1)}).

So one block evolution has error e^{−Θ(m)}, depth O_p(ℓ), O_p(vℓ) gates and O(v) ancillas.

## 3. Totals

Each of the ⌈T/τ⌉ steps has a constant number of block layers, so the depth is O_p(⌈T/τ⌉ ℓ) ≤ O_p(T ℓ/τ + ℓ). For T < τ a single step of time T has the same block. The gate count is n times the depth up to constants, and the ancillas are O(n). The block errors add up to at most ε/4 for Q = m + O(1).

## 4. Lean

`lean/LongBlock.lean` (Lean 4, Mathlib) proves the parameter arithmetic with unit constants, for real p and D with 0 ≤ D < p:

- `size_identity`: with r = τ^{(p+1)/p} ℓ^{D/p} and τ = ℓ^{(p−D)/(p+1)} a^{−p/(p+1)}, a·r = ℓ;
- `coeff_identity`: r^p = τ^{p+1} ℓ^D, so the coefficient ratio is one;
- `depth_per_time`: ℓ/τ = ℓ^δ a^{p/(p+1)} with δ = (D+1)/(p+1);
- `delta_pos`, `delta_lt_one`: 0 < δ < 1;
- `depth_sum`: ⌈T/τ⌉ steps of depth ℓ cost at most T ℓ/τ + ℓ;
- `example_instance`: p = 4, D = 1, a = 1, ℓ = 32 give τ = 8 and r = 32, so the hypotheses can hold together and the steps have length 1/4.

`lean/axioms.txt` lists only `propext`, `Classical.choice` and `Quot.sound`.

## 5. Script

`sim/params.py` sets the model constants to one except the stage count L + 1 = 2·5^{p/2−1} + 1 and the record width w = (D+3)⌈log₂(Q w)⌉. For D = 1, 2, 3, several p and m from 10⁶ to 10¹⁵ it checks the size condition (L+1) N w ≤ ℓ, the buffer ℓ ≥ τ + m, h ≤ 1 and v τ^{p+1}/r^p ≤ 1. It also checks that the slope of log(ℓ/τ) against log m, after removing the factor w^{1+D/(p+1)}, is (D+1)/(p+1).

## 6. Limits

- The bound is asymptotic. With the constants of the script, the depth per unit time ℓ/τ drops below m only for m of order 10⁷ when D = 1 and later for D ≥ 2. The constants depending on p grow with the 2c·5^{p/2−1} stages of the product formula.
- The lattice side must be at least a constant times m log m, against a constant times m in [1].
- A version with p growing with m is not claimed.
- The model is that of [1]: time-independent interactions, exact single-qubit gates and nearest-neighbour CNOTs. Finite gate sets add the synthesis cost of [1, Appendix C].
- The circuit construction rests on [1, Lemmas 4, 7, 9, 10, 12, 15 and 26], used for long steps and many product-formula steps as described above.
- Not formalized: the circuit construction and its error analysis. Lean covers the parameter arithmetic only.

## References

1. Z. Shen, Y. Wu, P. Yao, X. Yuan, Y. Zhang. Toward an optimal quantum algorithm for geometrically local Hamiltonian simulation. arXiv:2610.01839 (2026).
2. J. Haah, M. B. Hastings, R. Kothari, G. H. Low. Quantum algorithm for simulating real time evolution of lattice Hamiltonians. SIAM J. Comput. (2023), arXiv:1801.03922.

## Use of AI

The construction, the analysis, the Lean proofs, the script and this text were produced with the help of Claude Opus 5.5.
