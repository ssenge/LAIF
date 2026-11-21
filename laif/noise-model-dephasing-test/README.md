# Testing dephasing in an unknown basis against its depolarizing model

2026-11-21

## Problem

A device applies the same channel E on ℂ^d at every use. Either E is the depolarizing model

M_p = (1 − p) id + p Λ,  Λ(ρ) = (ρ + Tr(ρ) I)/(d + 1),

or E is dephasing in an unknown fixed basis,

E_{p,U} = (1 − p) id + p Δ_U,  Δ_U(ρ) = Σ_k P_k ρ P_k,  P_k = U|k⟩⟨k|U†,

for some unitary U. The two have the same entanglement fidelity and average gate fidelity, and Λ is the average of Δ_U over uniformly random U [1]. An ordinary strategy is an adaptive circuit that calls the device one call at a time on a d-dimensional query system, with unlimited quantum memory and known operations between calls [1, Definition 4]. In [1, Theorem 3], for d = 2^n, every ordinary strategy that decides between the two cases with success probability at least 2/3 needs Ω(d^{1/16}/p) calls, while O(d²/p) calls suffice through an approximate simulation of the quantum switch [1, Section 5.1]. Sharpening these bounds is named as open in [1, Section 6].

| | calls |
|---|---|
| Previous best bound | O(d²/p) [1, Section 5.1] |
| Lower bound (d = 2^n) | Ω(d^{1/16}/p) [1, Theorem 3] |
| Theorem 1 | O(d/p) |

## Result

**Theorem 1.** For every d ≥ 2 and 0 < p ≤ 1 there is an ordinary strategy that makes O(d/p) calls, outputs "model" with probability at least 2/3 if E = M_p, and outputs "dephasing" with probability at least 2/3 if E = E_{p,U}, for every unitary U.

The theorem follows from the state certification test of [2, Theorem 1.4] once the device is called in blocks; the proof below gives the details and the constants.

## Proof

*Blocks.* Δ_U is idempotent, and complete depolarization Ω(ρ) = Tr(ρ) I/d satisfies Ω ∘ Ω = Ω. Writing M_p = a id + (1 − a) Ω with a = 1 − pd/(d + 1), m consecutive calls give

E_{p,U}^m = (1 − p)^m id + (1 − (1 − p)^m) Δ_U,  M_p^m = a^m id + (1 − a^m) Ω.

Since a ≤ 1 − 2p/3, the choice m = ⌈3 ln(2)/(2p)⌉ = O(1/p) gives a^m ≤ 1/2.

*Input.* Pick a pure state ψ from an exact state 4-design (or uniformly at random) and send it through a block of m calls. With q = (1 − p)^m and q′ = a^m the outputs are

σ_E = (1 − q) Δ_U(ψ) + q ψ,  σ_M = (1 − q′) I/d + q′ ψ,

and σ_M is known to the strategy, since p and ψ are. With A = Δ_U(ψ) − I/d and B = ψ − I/d we have σ_E − σ_M = (1 − q) A + (q − q′) B, ‖B‖₂² = 1 − 1/d and ⟨A, B⟩ = ‖A‖₂² = X, where X = Σ_k w_k² − 1/d and w_k = |⟨u_k|ψ⟩|². Hence

‖σ_E − σ_M‖₂² = (1 − q′)² X + (q − q′)² (1 − 1/d − X) ≥ (1 − q′)² X ≥ X/4,

because X ≤ 1 − 1/d. For every fixed U and uniformly random ψ the weights w_k are uniform on the simplex. X² is a polynomial of degree 4 in ψ and its conjugate, so a state 4-design gives the same values of

E X = (d − 1)/(d(d + 1)),  E X² = (d − 1)(d² + 7d − 6)/(d²(d + 1)(d + 2)(d + 3)),

and E X² ≤ 2 (E X)² for all d ≥ 2. By the second-moment inequality P(X ≥ E X/2) ≥ (E X)²/(4 E X²), X ≥ E X/2 ≥ 1/(6d) with probability at least 1/8 over ψ, and then ‖σ_E − σ_M‖₂ ≥ 1/(2√(6d)).

*Test.* The certification algorithm of [2, Theorem 1.4] for the distance ‖ρ − σ‖₂ decides between ρ = σ_M and ‖ρ − σ_M‖₂ > ε with O(1/ε²) copies of ρ, independent of the dimension, with error probability at most δ after O(log(1/δ)) repetitions. With ε = 1/(3√(6d)) and δ = 1/27 one round needs O(d) blocks, which the strategy runs one after another, keeping the outputs in its memory; under the model ρ = σ_M exactly. A round outputs "far" with probability at most 1/27 under the model and at least (26/27)/8 under every E_{p,U}. Nine rounds, each with a fresh ψ, answering "dephasing" if any round says "far", err with probability at most 9/27 = 1/3 under the model and at most (1 − 26/216)^9 < 1/3 under dephasing. The total is O(d) blocks of O(1/p) calls. ∎

## Check

`sim/check.py` checks the block formulas against direct composition, the identity for ‖σ_E − σ_M‖₂², the exact moments E X and E X² against Monte Carlo sampling, the constant (E X)²/(4 E X²) for 2 ≤ d ≤ 2000 in exact rational arithmetic, and the gap ‖σ_E − σ_M‖₂ ≥ √X/2 on random instances with q in [0, 1] and q′ ≤ 1/2. `sim/pz_all_d.py` proves E X² ≤ 2 (E X)² for all d ≥ 2: in t = d − 2 the numerator and the denominator of 2 (E X)² − E X² have nonnegative coefficients.

## Scope

- The strategy measures jointly across the O(d) stored outputs, as [2] does; it uses one query system and sequential calls only.
- The bound is an upper bound; for d = 2^n the lower bound Ω(d^{1/16}/p) of [1] is unchanged, so the query complexity lies between d^{1/16}/p and d/p.
- Not formalized in Lean. [2, Theorem 1.4] is used as stated there.

## References

[1] D. Li. Infinite or indefinite: the query cost of simulating the quantum switch. arXiv:2611.16229.

[2] C. Bădescu, R. O'Donnell, J. Wright. Quantum state certification. STOC 2019. arXiv:1708.06002.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
