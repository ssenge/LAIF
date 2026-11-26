# The optimal constant of zero-error quantum search

2026-11-26

A zero-error search algorithm must halt with probability 1 and output a marked item with certainty. Its cost is the expected number of oracle rounds. A weakly measured search loop [2] finds one marked item among N in (1/2 + 1/π)·(π/4)√N expected queries as N → ∞. With m parallel queries per round and k marked items, circuits in [1] reach the same constant 1/2 + 1/π, in units of (π/4)√(N/(mk)), for every m and k. A lower bound of order √(N/(mk)) is known [1, Appendix E.2], with constant 1/2 for m = k = 1 (implied by [3]). This folder proves that no zero-error algorithm does better: the optimal constant is exactly 1/2 + 1/π, for every m and k.

## Setting

The setting is that of [1, Appendix E.1]. There are N items, and S is an unknown set of k marked items, with k known. The oracle O_S maps |b⟩|x⟩ to |b ⊕ [x ∈ S]⟩|x⟩. A round applies O_S to at most m disjoint registers at once. Between rounds the algorithm may apply any unitary that does not depend on S, measure, and branch on the outcomes. It must halt with probability 1 and output an element of S with certainty. The cost is the expected number of rounds on the worst-case S. A random relabelling of the items, at no query cost, makes this equal to the average over all S, so the bounds below hold for both.

Write sin θ = 1/√N and sin θ_m = √(m/N), with θ, θ_m ∈ (0, π/2].

## Results

| Quantity | Previous best bound | This folder |
|---|---|---|
| Zero-error search, k marked items known, at most m parallel queries per round: expected rounds divided by (π/4)√(N/(mk)), as N → ∞ | at most 1/2 + 1/π ≈ 0.8183 [2; 1, Appendix E]; at least 1/2 for m = k = 1, implied by [3] | **exactly 1/2 + 1/π**, for every m and k |
| The same for one marked item and every N ≥ 2, m ≤ N | | **at least (π/4 + 1/2 − θ)/(2θ_m)** rounds |
| Exact optimum for m = k = 1, numerical | | 0.7811, 0.8097, 0.8161, 0.8178, 0.8182 at N = 16, 64, 256, 1024, 4096 |

**Theorem 1.** For one marked item, every N ≥ 2 and every 1 ≤ m ≤ N, every zero-error algorithm uses at least

  E[rounds] ≥ (π/4 + 1/2 − θ) / (2θ_m)

expected rounds. As N → ∞ with m fixed, the bound equals (1/2 + 1/π)·(π/4)√(N/m) − 1/(2√m) + o(1).

**Corollary 2.** For k marked items, let M = ⌊N/k⌋ ≥ m. Every zero-error algorithm uses at least (π/4 + 1/2 − arcsin(1/√M)) / (2 arcsin √(m/M)) expected rounds. So for fixed m and k the ratio to (π/4)√(N/(mk)) is at least 1/2 + 1/π − o(1). With the algorithms of [2] and [1], the optimal constant of zero-error search for one of k marked items with m parallel queries is exactly 1/2 + 1/π.

For m = k = 1 the bound of Theorem 1 lies about half a round below the exact optimum:

| N | 16 | 64 | 256 | 1024 | 4096 |
|---|---|---|---|---|---|
| Theorem 1 | 2.0435 | 4.6281 | 9.7765 | 20.0630 | 40.6311 |
| Optimum, at most T rounds | 2.4539 | 5.0875 | 10.2560 | 20.5523 | 41.1252 |
| Optimum divided by (π/4)√N | 0.7811 | 0.8097 | 0.8161 | 0.8178 | 0.8182 |

The optimum is that of a semidefinite program over the Gram matrices of all algorithms with at most T rounds (T = 24, 36, 60, 120, 220), described below.

## Proof of Theorem 1

**Normal form.** Replace the algorithm by its random relabelling and keep the relabelling, and every measurement except the decision to halt, coherent. At the start of round t, on marked item y, the part of the state that has not halted is a vector ψ_y. Its squared norm a_t is the probability of not having halted, the same for every y, and the expected number of rounds is the sum of a_t over t ≥ 0. A permutation of the items maps ψ_y to ψ_σ(y) by a unitary, so ⟨ψ_x, ψ_y⟩ = b for all x ≠ y. Let ψ̄ be the mean of the ψ_y. Then ‖ψ̄‖² = (a + (N − 1)b)/N and ⟨ψ̄, ψ_y − ψ̄⟩ = 0. Define ω ∈ [0, π/2] by cos ω = ‖ψ̄‖/√a. At the start all ψ_y coincide, so a_0 = 1 and ω_0 = 0.

**Halting.** The halted part of the state on input y lies in the subspace where the output register holds y, so the halted parts for different y are orthogonal and have the same squared norm d. Halting therefore lowers a by d and leaves b unchanged. In terms of u = b/a, cos²ω = 1/N + (1 − 1/N)u.

**Lemma 3 (one round).** One round changes ω by at most 2θ_m.

*Proof.* In the basis |+⟩, |−⟩ of the target qubits, O_S acts on a register as the phase (−1)^{[x ∈ S]} when the target is |−⟩ and as the identity when it is |+⟩. For S = {y}, m registers in a basis state therefore pick up the phase (−1)^{[y ∈ A]}, where A is the set of items held an odd number of times by registers with target |−⟩, and |A| ≤ m. So the round maps ψ_y to (I − 2Π_y)ψ_y with Π_y = Σ_{A ∋ y} P_A, for orthogonal projectors P_A that sum to the identity. Hence Π_y is a projector and Σ_y Π_y = Σ_A |A| P_A ≤ m I.

Let β = ‖ψ̄‖, δ_y = ψ_y − ψ̄ and p = mean_y ‖Π_y ψ̄‖² / β², so p ≤ m/N. The new mean ψ̄′ satisfies

  ‖ψ̄′‖ ≥ Re⟨ψ̄, ψ̄′⟩/β = β − (2/β) mean_y (‖Π_y ψ̄‖² + Re⟨Π_y ψ̄, δ_y⟩).

The δ_y have mean zero, so mean_y ⟨Π_y ψ̄, δ_y⟩ = mean_y ⟨(Π_y − p)ψ̄, δ_y⟩. By the Cauchy-Schwarz inequality this is at most (mean_y ‖(Π_y − p)ψ̄‖²)^{1/2} (mean_y ‖δ_y‖²)^{1/2} = (p(1 − p))^{1/2} β · √a sin ω. With sin²θ_p = p this gives

  ‖ψ̄′‖ ≥ √a (cos ω (1 − 2p) − 2 sin ω (p(1 − p))^{1/2}) = √a cos(ω + 2θ_p) ≥ √a cos(ω + 2θ_m)

when ω + 2θ_m ≤ π, so the new angle is at most ω + 2θ_m (if ω + 2θ_m > π this holds trivially, since every angle is at most π/2). The round is its own inverse, so the same bound from the new state back to the old one gives the other direction. ∎

The bound is tight: for m = 1 a Grover iteration attains it, and the one-round program of `sim/parallel.py` attains it for m ≤ 8. Unitaries between rounds change neither a nor b.

**Potential.** Let K = 1/(2θ_m), c = π/4 + 1/2 − θ and ω* = π/2 − θ/2. Define h(ω) = K(c − ω) for ω ≤ ω* and h(ω) = K(c − 2ω* + ω) for ω ≥ ω*, and Φ = a·h(ω).

**Lemma 4.** (a) A round lowers Φ by at most a. (b) Halting never lowers Φ.

*Proof.* (a) h is Lipschitz with constant K, and Lemma 3 moves ω by at most 2θ_m = 1/K at fixed a. (b) At fixed b, the derivative of a·h(ω) in a is h(ω) + h′(ω)(cos²ω − 1/N)/sin 2ω. Halting lowers a, so it suffices that h(ω) sin 2ω + h′(ω)(cos²ω − 1/N) ≤ 0 on (0, π/2).

On (0, ω*] this reads (c − ω) sin 2ω ≤ cos²ω − 1/N. The function g(ω) = cot(ω)/2 + ω − π/4 − 1/2 is convex with minimum 0 at ω = π/4. Where sin 2ω ≥ 1/√N, the inequality is equivalent to g(ω) + θ ≥ 1/(N sin 2ω), and the right side is at most 1/√N = sin θ ≤ θ. For ω < θ/2 the left side of cos²ω − (c − ω) sin 2ω ≥ 1/N is at least F(x) = (1 + √(1 − x²))/2 − (π/4 + 1/2 − arcsin x)x − x² with x = 1/√N. F decreases on (0, 1/√2], since F′(x) ≤ 1/2 − π/4 − 1/2 + π/4 − 2x < 0, and F(1/√2) = 0.

On [ω*, π/2), c − 2ω* + ω ≤ 1/2 − π/4 < 0, and cos²ω ≤ sin²(θ/2) = (1 − √(1 − 1/N))/2 ≤ 1/N, so both terms are at most 0. ∎

**Proof of Theorem 1.** By Lemma 4, Φ_{t+1} ≥ Φ_t − a_t, so a_0 + ... + a_{T−1} ≥ Φ_0 − Φ_T. The algorithm halts with probability 1 and h is bounded, so Φ_T → 0. Hence E[rounds] ≥ Φ_0 = K c = (π/4 + 1/2 − θ)/(2θ_m). ∎

**Proof of Corollary 2.** Given one marked item among M, form N items from k copies of the M items plus N − kM unmarked dummies. The copies of the marked item are k marked items, one query to the large oracle costs one query to the small one, and any marked item found names the original. An algorithm for k marked items thus yields one for a single marked item among M with the same expected number of rounds. ∎

## Scope

- The lower bound covers every algorithm in the setting above, with intermediate measurements, classical control and any workspace, and every N, m and k. Theorem 1 is exact at finite N; the constant 1/2 + 1/π in Corollary 2 is asymptotic in N for fixed m and k.
- Matching upper bounds are those of [2] for m = k = 1 and of [1, Appendix E] for every m and k.
- The results concern finding one marked item (Find-Any). Finding all k marked items is not covered.
- The exact optima in the table come from a semidefinite program in double precision. The bounds of Theorem 1 have written proofs. Lemma 3, Lemma 4 and the potential steps are checked numerically on random instances, through the exact one-round program, on fine grids for N up to 10⁶, and along the optimal trajectories.

## Files

- `sim/bss.py`: the semidefinite program over Gram matrices for m = k = 1. It covers all algorithms with at most T rounds, with halting, and prints the optimal expected number of queries.
- `sim/parallel.py`: the exact one-round program for at most m parallel queries (set phases with |A| ≤ m), and the largest change of ω.
- `sim/check_lb.py`: asserts for Lemma 3 (random families of vectors and the one-round program), for the halting condition of Lemma 4 (N from 2 to 10⁶), for Theorem 1 against the optimum, and for the potential along the optimal trajectories.

## References

1. S. Shirobokov et al., Discovering formally verified quantum programs with AI, arXiv:2611.09822 (2026).
2. P. Andrés-Martínez, C. Heunen, Weakly measured while loops: peeking at quantum states, arXiv:2009.08832.
3. C. Zalka, Grover's quantum searching algorithm is optimal, Phys. Rev. A 60, 2746 (1999), arXiv:quant-ph/9711070.

## Use of AI

The results, proofs and scripts were developed with the help of an AI system (Claude Opus 5.5), which also checked them.
