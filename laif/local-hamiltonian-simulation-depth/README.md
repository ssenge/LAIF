# Depth of geometrically local Hamiltonian simulation with long blocks

Written 26 Nov 2026.

A geometrically local Hamiltonian H acts on n qubits placed on the sites of a D-dimensional cubic lattice. Every term has a support of bounded diameter, and the local strength is at most one (the terms containing any one site have total norm at most one). The task is a circuit of nearest-neighbour gates that approximates e^{−iHT} to operator-norm error ε. Write m = log(nT/ε).

The best known circuits have depth O(T log(nT/ε)) and O(nT log(nT/ε)) gates [1], improving the depth O(T log^D(nT/ε)) of [2]. The depth lower bound of [1] adds the two scales, Ω(T + m′/log(e + m′/T)) with m′ = log(n/ε), and the joint dependence on T and ε is stated in [1] as a remaining question.

The circuits of [1] first cut the evolution into steps of time at most 1 by the Lieb-Robinson decomposition of [2]. They then simulate each block of side Θ(m) with a fixed-order product formula whose residual is removed by a linear combination of unitaries, at depth O(m) per block. Here the steps are long, of time τ = Θ(m log m). The product formula uses many more steps per block, so that the coefficient sum of the correction stays bounded. The blocks are made large enough for the control distribution of [1] to apply unchanged. The per-block cost of the correction is then spread over a time τ instead of a unit time.

**Theorem 1.** Fix D ≥ 1 and an even integer p > D, and let δ = (D+1)/(p−D). If the lattice side is at least a constant times (m log m)^{(p+1)/(p−D)} (log m)^{p/(p−D)}, there is a nearest-neighbour circuit with operator-norm error at most ε, O(n) ancillas, and

- depth O_p((T + m log m) · (m log m)^δ · (log m)^{p/(p−D)}), and
- O_p(n (T + m log m) · (m log m)^δ · (log m)^{p/(p−D)}) gates.

**Corollary 2.** For every fixed δ′ > 0 and T ≥ m, depth T · m^{δ′} and n T · m^{δ′} gates suffice. This takes p > D + (D+1)/δ′ and absorbs the logarithmic factors.

Status: Claim. The parameter conditions and the exponent δ are checked by a script with asserts (`sim/params.py`).

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Depth for e^{−iHT}, geometrically local H in D dimensions, error ε, T ≥ m | O(T m) [1] | T m^{δ′} for every δ′ > 0 |
| Gates, same setting | O(n T m) [1] | n T m^{δ′} for every δ′ > 0 |

## 1. Long steps

For a time t with |t| ≤ τ, the evolution of the whole lattice is approximated by a constant number of layers of forward and inverse block evolutions, as in [2] and [1, Lemma 4], with error C n |t| e^{v′|t| − μ ℓ_buf}. Here ℓ_buf is the buffer width, the blocks have sides between ℓ_buf and C ℓ_buf, and C, μ and v′ depend only on the local model. The proof of [1, Lemma 4] in [1, Appendix D] uses |t| ≤ 1 at two points only. The first is the Lieb-Robinson tail Σ_{k ≥ d/R} (2ν|t|)^k/k! ≤ e^{−μd} exp(2ν e^{μR} |t|), which holds for every t and gives v′ = 2ν e^{μR}. The second is the factor |t| in the Duhamel bound. A buffer ℓ_buf ≥ C(τ + m) therefore keeps the error of all ⌈T/τ⌉ steps below ε/4.

## 2. One long block

Let a block have side ℓ and volume v = ℓ^D, and let it evolve for a time τ. With r steps of length h = τ/r, e^{−iH_blk τ} = (C(h) E(h))^r exactly, where C is the order-p product formula and E(s) = C(s)^† e^{−iH_blk s} is its residual. The construction of [1, Sections 3 to 5] is used with these changes.

- The residual table [1, Lemma 7] needs only |s| ≤ h ≤ 1. It does not depend on r or τ.
- The label states of [1, Section 3.3] are defined for every r. They use N = r + K₀ slots with K₀ = ⌊Q/(p+1)⌋, and the normalization 2 comes from (1 − a)^r = 1/2 for every r.
- In the error and coefficient bounds [1, Lemma 10], take ξ = e and Q = m + O(1). The condition r A(ξ) ≤ 1/8 reads v τ^{p+1}/r^p ≤ c_p, so r = Θ_p(τ (vτ)^{1/p}) steps suffice. Then h → 0, and t_ω ξ ≤ 1/2 holds as well. The truncation error is at most 4e^{−Q}.
- The control distribution of [1, Lemma 12] for D ≥ 2, and of [1, Lemma 26] for D = 1, needs N w + w log ℓ = O(ℓ) with record width w = Θ(log ℓ). This is the size condition ℓ ≥ C N w. Since r grows only like ℓ^{D/p}, it holds for ℓ = Θ_p(τ^{(p+1)/(p−D)} w^{p/(p−D)}). These lemmas then give depth O(ℓ + N w) = O(ℓ), O(ℓ^{D+1}) gates and O(ℓ^D) ancillas.
- The source computations of [1, Sections 4.3 and 4.4] have depth O(N w + Q w) = O(ℓ) and O(N Q w) = O(ℓ m) gates. One round of oblivious amplitude amplification [1, Section 5.1] uses a constant number of calls.

So one block evolution has error e^{−Θ(m)}, depth O_p(ℓ), O_p(vℓ) gates and O(v) ancillas.

## 3. Totals

Each of the ⌈T/τ⌉ steps has a constant number of block layers, so the depth is O_p(⌈T/τ⌉ ℓ). For T ≥ τ = m log m this is O_p(T ℓ/τ) = O_p(T τ^δ w^{p/(p−D)}). For T < τ a single step of time T gives O_p(ℓ). The gate count is n times the depth up to constants, and the ancillas are O(n). The block errors add up to at most ε/4 for Q = m + O(1).

## 4. Script

`sim/params.py` takes all model constants equal to one. For D = 1, 2, 3, several p and m from 10³ to 10⁹ it checks the size conditions, h ≤ 1 and v τ^{p+1}/r^p ≤ 1. It also checks that the slope of log(ℓ/τ) against log τ, after removing the factor w^{p/(p−D)}, is (D+1)/(p−D).

## 5. Limits

- The bound is asymptotic. With unit constants the depth per unit time ℓ/τ is below m at m = 10³ only for p ≥ 8 when D = 1, and the factor (log m)^{p/(p−D)} and the constants depending on p dominate at moderate m.
- The lattice side must exceed the block side ℓ, which is polynomial in m.
- The hidden constants depend on p through the product formula (its 2 · 5^{p/2−1} stages) and the residual table. A version with p growing with m is not claimed.
- The model is that of [1]: time-independent interactions, exact single-qubit gates and nearest-neighbour CNOTs. Finite gate sets add the synthesis cost of [1, Appendix C].
- Not formalized: the whole construction. The script checks only the parameter conditions.

## References

1. Z. Shen, Y. Wu, P. Yao, X. Yuan, Y. Zhang. Toward an optimal quantum algorithm for geometrically local Hamiltonian simulation. arXiv:2610.01839 (2026).
2. J. Haah, M. B. Hastings, R. Kothari, G. H. Low. Quantum algorithm for simulating real time evolution of lattice Hamiltonians. SIAM J. Comput. (2023), arXiv:1801.03922.

## Use of AI

The construction, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
