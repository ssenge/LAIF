# Testing dephasing in an unknown basis against its depolarizing model

2026-11-21

## Problem

A device applies the same channel E on ℂ^d at every use. Either E is the depolarizing model

M_p = (1 − p) id + p Λ,  Λ(ρ) = (ρ + Tr(ρ) I)/(d + 1),

or E is dephasing in an unknown fixed basis,

E_{p,U} = (1 − p) id + p Δ_U,  Δ_U(ρ) = Σ_k P_k ρ P_k,  P_k = U|k⟩⟨k|U†,

for some unitary U. The two have the same entanglement fidelity and average gate fidelity, and Λ is the average of Δ_U over uniformly random U [1]. An ordinary strategy is an adaptive circuit that calls the device one call at a time on a d-dimensional query system, with unlimited quantum memory and known operations between calls [1, Definition 4]. In [1, Theorem 3], every ordinary strategy that decides between the two cases with success probability at least 2/3 needs Ω(d^{1/16}/p) calls, while O(d²/p) calls suffice through an approximate simulation of the quantum switch [1, Section 5.1]. Sharpening these bounds is named as open in [1, Section 6].

| | calls |
|---|---|
| Previous best bound | O(d²/p) [1] |
| Lower bound | Ω(d^{1/16}/p) [1, Theorem 3] |
| Theorem 1 | O(d log d / p) |

## Result

**Theorem 1.** For every d ≥ 2 and 0 < p ≤ 1 there is an ordinary strategy that makes O(d log(d)/p) calls, outputs "model" with probability at least 2/3 if E = M_p, and outputs "dephasing" with probability at least 2/3 if E = E_{p,U}, for every unitary U.

## Proof

*Blocks.* Δ_U is idempotent, and complete depolarization Ω(ρ) = Tr(ρ) I/d satisfies Ω ∘ Ω = Ω. Writing M_p = a id + (1 − a) Ω with a = 1 − pd/(d + 1), m consecutive calls give

E_{p,U}^m = (1 − p)^m id + (1 − (1 − p)^m) Δ_U,  M_p^m = a^m id + (1 − a^m) Ω.

Both 1 − p and a are at most 1 − 2p/3, so with η = 1/(4√(6d)) and m = ⌈3 ln(1/η)/(2p)⌉ = O(log(d)/p) both weights (1 − p)^m and a^m are at most η.

*Input.* Pick a uniformly random unit vector ψ once and send |ψ⟩⟨ψ| through a block of m calls. The outputs are

σ_E = (1 − q) Δ_U(ψ) + q ψ,  σ_M = (1 − q′) I/d + q′ ψ,  with q, q′ ≤ η,

and σ_M is known to the strategy, since p and ψ are. The weights w_k = |⟨u_k|ψ⟩|² of Δ_U(ψ) = Σ_k w_k P_k are uniform on the simplex for every fixed U. For X = ‖Δ_U(ψ) − I/d‖₂² = Σ_k w_k² − 1/d,

E X = (d − 1)/(d(d + 1)),  E X² = (d − 1)(d² + 7d − 6)/(d²(d + 1)(d + 2)(d + 3)),

and E X² ≤ 2 (E X)² for all d ≥ 2. By the second-moment inequality P(X ≥ E X/2) ≥ (E X)²/(4 E X²), X ≥ E X/2 ≥ 1/(6d) with probability at least 1/8 over ψ. On this event

‖σ_E − σ_M‖₂ ≥ ‖Δ_U(ψ) − I/d‖₂ − q ‖ψ − Δ_U(ψ)‖₂ − q′ ‖ψ − I/d‖₂ ≥ 1/√(6d) − 2η = 1/(2√(6d)).

*Test.* The certification algorithm of [2, Theorem 1.4] for the distance ‖ρ − σ‖₂ distinguishes ρ = σ_M from ‖ρ − σ_M‖₂ > ε with O(1/ε²) copies of ρ, independent of the dimension. With ε = 1/(3√(6d)) it needs O(d) blocks, which the strategy runs one after another, keeping the outputs in its memory. Under the model ρ = σ_M exactly. One round with a fresh ψ therefore outputs "far" with probability at most a small constant under the model and with probability at least c > 0 under every E_{p,U}. Running a constant number of rounds, each with the error of [2] reduced by repetition, and answering "dephasing" if any round says "far", gives success probability 2/3 in both cases with O(d) blocks in total, that is, O(d log(d)/p) calls. ∎

## Check

`sim/check.py` checks the block formulas against direct composition, the exact moments E X and E X² against Monte Carlo sampling, the constant (E X)²/(4 E X²) for 2 ≤ d ≤ 2000 in exact rational arithmetic, and the gap ‖σ_E − σ_M‖₂ on random instances with every contamination weight up to η. `sim/pz_all_d.py` proves E X² ≤ 2 (E X)² for all d ≥ 2: in t = d − 2 the numerator and the denominator of 2 (E X)² − E X² have nonnegative coefficients.

## Scope

- The strategy measures jointly across the O(d) stored outputs, as [2] does; it uses one query system and sequential calls only.
- The bound is an upper bound; the lower bound Ω(d^{1/16}/p) of [1] is unchanged, so the query complexity lies between d^{1/16}/p and d log(d)/p.
- Not formalized in Lean. [2, Theorem 1.4] is used as stated there.

## References

[1] D. Li. Infinite or indefinite: the query cost of simulating the quantum switch. arXiv:2611.16229.

[2] C. Bădescu, R. O'Donnell, J. Wright. Quantum state certification. STOC 2019. arXiv:1708.06002.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
