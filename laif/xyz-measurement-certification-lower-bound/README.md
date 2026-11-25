# Certifying a cat state with single-qubit X, Y and Z measurements needs Ω((3/2)^{n/2}) copies, even adaptively

2026-11-25

## Problem

A known pure target state |ψ⟩ on n qubits is to be certified, or its fidelity with an unknown lab state σ estimated, from copies of σ. With arbitrary measurements, Θ(1/ε) copies certify and Θ(1/ε²) copies estimate the fidelity to ±ε. Many experiments measure each qubit only along the axes X, Y or Z. In that model, the classical-shadow estimator with uniformly random axes estimates the fidelity with O(d^{0.7716}/ε²) copies, d = 2^n, for every target ([5]; earlier o(d^{0.9675})/ε² [1]). For almost all targets, X, Y, Z measurements certify with O(1/ε²) copies [6] and estimate the fidelity efficiently [7]. Without the axis restriction, adaptive single-qubit measurements certify every pure state from O(n/ε) copies [2], while algorithms with little adaptivity need 2^{Ω(n)} copies for some target [2, Theorem 2]. Concrete targets that cannot be certified with polynomially many single-qubit measurements are asked for in [3]; for general axes none exist [2]. With X, Y, Z axes only, the target ψ_n below is one. For measurements of single X, Y, Z strings, fidelity estimation is studied in [4], and the cost of such estimators grows with the distance from stabilizer states [8].

Fidelity estimation to ±ε for a worst-case target, X, Y, Z measurements on every qubit:

| | copies |
|---|---|
| Upper bound, non-adaptive | O(d^{0.7716}/ε²) [5] |
| Previous best lower bound | Ω(1/ε²), the bound for arbitrary measurements; 2^{Ω(n)} for algorithms with little adaptivity [2, Theorem 2] |
| Theorem 1, adaptive within and across copies | (2/225)(3/2)^{n/2}/ε² = Ω(d^{0.2924}/ε²) for ε ≤ 1/10 |

## Setting

Let |a⟩ be the single-qubit state whose expectation values of X, Y and Z are all 1/√3, and |ā⟩ a state orthogonal to it, with any phase. Define the cat state and its dephased version

|ψ_n⟩ = (|a⟩^{⊗n} + |ā⟩^{⊗n})/√2,  ρ_n = (|a⟩⟨a|^{⊗n} + |ā⟩⟨ā|^{⊗n})/2,

so ⟨ψ_n|ρ_n|ψ_n⟩ = 1/2. The state ψ_n is the cat state (|0⟩^{⊗n} + |1⟩^{⊗n})/√2 with one fixed single-qubit unitary applied to every qubit.

**Model.** The copies arrive one after another. On each copy, the strategy measures the qubits one at a time, each in the eigenbasis of X, Y or Z. Which qubit is measured next, along which axis, and whether to stop may depend on all earlier outcomes on this copy and on earlier copies, and on classical randomness. Measuring a qubit again, along any axis, gives an outcome whose law is fixed by its earlier outcome and is the same under every hypothesis, so it adds only classical randomness; hence each qubit is measured at most once. The number of copies may be random; the bounds below are for its largest value, and with the same proof for its expectation under ψ_n (in (a), (b)) or under the state ρ_{5ε} defined below (in (c)). At the end the strategy outputs a decision or an estimate.

## Result

**Theorem 1.** In this model, for every n ≥ 1:

(a) a strategy that tells ψ_n from ρ_n with success probability at least 2/3 under each hypothesis uses at least (2/9)(3/2)^{n/2} copies;

(b) for 0 < ε ≤ 1/2, let σ_ε = (1 − 2ε)|ψ_n⟩⟨ψ_n| + 2ερ_n, whose fidelity with ψ_n is 1 − ε. A strategy that accepts ψ_n and rejects σ_ε, each with probability at least 2/3, uses at least (3/2)^{n/2}/(9ε) copies;

(c) for 0 < ε ≤ 1/10, a strategy that estimates ⟨ψ_n|σ|ψ_n⟩ to ±ε with probability at least 2/3 for every state σ uses at least (2/225)(3/2)^{n/2}/ε² copies.

Since (3/2)^{n/2} = d^{log₂(3/2)/2} and log₂(3/2)/2 = 0.29248…, the bounds grow as d^{0.2924}. So in this model the worst-case exponent of fidelity estimation lies between 0.2924 and 0.7716 [5], and certification of the explicit target ψ_n costs exponentially many copies even with adaptivity within and across copies. The bound in (a) exceeds 1 for n ≥ 8.

## Proof

*One copy.* Fix the strategy's behaviour on one copy, given everything before it and given its random coins (the coins are part of the past and have the same law under both hypotheses). It is a decision tree: each node measures one not yet measured qubit along X, Y or Z. Measuring the remaining qubits at a leaf only refines the outcome, and refining cannot decrease the chi-square divergence or the relative entropy (data processing), so assume every leaf ℓ has measured all n qubits, with outcome states |e_1⟩, …, |e_n⟩ (each an eigenvector of the chosen axis). The event of reaching ℓ is the product projector onto |e_ℓ⟩ = ⊗_i |e_i⟩. With u_ℓ = ⟨e_ℓ|a^{⊗n}⟩ = Π_i ⟨e_i|a⟩ and v_ℓ = ⟨e_ℓ|ā^{⊗n}⟩, the leaf probabilities are

P_ψ(ℓ) = m_ℓ + c_ℓ,  P_ρ(ℓ) = m_ℓ,  m_ℓ = (|u_ℓ|² + |v_ℓ|²)/2,  c_ℓ = Re(u_ℓ v̄_ℓ).

*The key sum.* Along X, Y or Z the two outcome probabilities of |a⟩ are (1 ± 1/√3)/2 and those of |ā⟩ are (1 ∓ 1/√3)/2, so for every axis

Σ_{e} |⟨e|a⟩| |⟨e|ā⟩| = 2 · √((1 + 1/√3)(1 − 1/√3))/2 = √(2/3).

Summing over the tree from the leaves up, each node contributes this factor whatever axis it chooses, so Σ_ℓ |u_ℓ| |v_ℓ| = (2/3)^{n/2}.

*Chi-square bound.* Since c_ℓ² ≤ |u_ℓ|²|v_ℓ|² and 2xy/(x + y) ≤ √(xy) for x, y ≥ 0,

χ²(P_ψ ‖ P_ρ) = Σ_ℓ c_ℓ²/m_ℓ ≤ Σ_ℓ 2|u_ℓ|²|v_ℓ|²/(|u_ℓ|² + |v_ℓ|²) ≤ Σ_ℓ |u_ℓ||v_ℓ| = (2/3)^{n/2}.

For the state ρ_s = (1 − s)ρ_n + s|ψ_n⟩⟨ψ_n| the leaf probabilities are m_ℓ + s c_ℓ. Hence χ²(P_{ρ_s} ‖ P_ρ) = s² Σ c²/m ≤ s²(2/3)^{n/2}. Since |c_ℓ| ≤ m_ℓ, also m_ℓ + (1 − 2ε)c_ℓ ≥ 2ε m_ℓ, and so χ²(P_ψ ‖ P_{σ_ε}) = Σ (2εc_ℓ)²/(m_ℓ + (1 − 2ε)c_ℓ) ≤ 2ε Σ c²/m ≤ 2ε(2/3)^{n/2}.

The argument follows the cross-term approach of [2, Section 3], which compares a superposition of product states with their mixture. With X, Y, Z axes and the state |a⟩, the per-qubit factor √(2/3) is the same for every allowed axis, and this is what makes the bound hold for every adaptive tree.

*All copies.* The copies are independent and the tree for copy t depends only on earlier outcomes. By the chain rule, the relative entropy D between the two full outcome distributions is the sum over t of the expected relative entropy of copy t given the past, and D ≤ χ² holds for each copy. So D ≤ T · κ, with κ the per-copy bound above. Success probability 2/3 under both hypotheses forces total variation at least 1/3, and total variation is at most √(D/2), so D ≥ 2/9 and T ≥ 2/(9κ). This gives (a) with κ = (2/3)^{n/2} and (b) with κ = 2ε(2/3)^{n/2}. For (c), the states ρ_n and ρ_{5ε} have fidelities 1/2 and 1/2 + 5ε/2 with ψ_n, so an estimate to ±ε tells them apart; κ = 25ε²(2/3)^{n/2} gives T ≥ (2/225)(3/2)^{n/2}/ε².

## Check

`sim/check.py` (output `sim/out_check.txt`) builds ψ_n and ρ_n and asserts, for n ≤ 6 and all 3^n settings of the axes, the leaf formulas, the identity Σ|u||v| = (2/3)^{n/2}, the bound χ²(P_ψ ‖ P_ρ) ≤ (2/3)^{n/2}, the bound for (b) at ε = 0.01, 0.1, 0.2, the identity χ²(P_{ρ_s} ‖ P_ρ) = s² Σ c²/m used in (c), with P_{ρ_s} computed from the density matrix of ρ_s, for s up to 1, and the fidelity 1/2. The numbers below use the phase of |ā⟩ fixed in the scripts. For n ≤ 5 it asserts the identity and the bound on 200 random adaptive trees each, with the qubit order and the axes chosen at random from the outcomes so far. Over the non-adaptive settings, the largest χ²(P_ψ ‖ P_ρ) is 0.82, 0.75, 0.68, 0.64, 0.60, 0.57 times (2/3)^{n/2} for n = 1, …, 6, all attained by measuring every qubit along Z. For that setting `sim/allz.py` (output `sim/out_allz.txt`) computes χ² exactly up to n = 320: χ²/(2/3)^{n/2} times √n increases to 1.89 at n = 320, so the per-copy bound is attained up to a factor Θ(n^{−1/2}) (numerical). Since the squared distance between √P_ψ and √P_ρ is at least χ²/6 here (because |c_ℓ| ≤ m_ℓ), a likelihood-ratio test on all-Z data tells ψ_n from ρ_n with O(√n (3/2)^{n/2}) copies, so (a) is tight up to the factor √n for this pair, given the numerical asymptotics. `sim/blocks.py` is a local numerical search over non-adaptive settings: it minimizes the largest coefficient Σ|⟨e|A⟩||⟨e|A′⟩| over orthogonal pairs of k-qubit states A, A′ for k = 1, 2, 3; per qubit it finds √(2/3) each time, the value of the pair a, ā.

## Scope

- The model measures single qubits along X, Y and Z only. Measurements along other axes, joint measurements of several qubits, and measurements on several copies at once are not covered; with other single-qubit axes, polynomially many copies suffice [2].
- Copies are measured one after another. Strategies that interleave measurements of qubits from several stored copies are not covered.
- The lower bound concerns the worst case over targets: it is proved for the target ψ_n. The upper bound O(d^{0.7716}/ε²) [5] holds for every target.
- The hardness comes from the axis restriction alone: after the single-qubit rotation that maps ψ_n to (|0⟩^{⊗n} + |1⟩^{⊗n})/√2, measurements along the rotated axes of random elements of its stabilizer group accept with probability (1 + F)/2 at fidelity F, which certifies it with O(1/ε) copies.
- **Not formalized:** the theorem has no Lean proof.

## References

1. J. Acharya, A. Dharmavarapu, Y. Liu, N. Yu. Sublinear copies suffice for fidelity estimation with Pauli measurements. arXiv:2609.35547.
2. M. Gupta, W. He, R. O'Donnell. Few single-qubit measurements suffice to certify any quantum state. STOC 2026, arXiv:2506.11355.
3. H.-Y. Huang, J. Preskill, M. Soleimanifar. Certifying almost all quantum states with few single-qubit measurements. arXiv:2404.07281.
4. O. Fawzi, A. Oufkir, R. Salzmann. Optimal fidelity estimation from binary measurements for discrete and continuous variable systems. arXiv:2409.04189.
5. Shadow norm under random Pauli measurements: the exact worst case over observables, [laif/pauli-shadow-norm](../pauli-shadow-norm/).
6. A. Coladangelo, J. Li, J. Slote. Robust quantum state certification and uncertainty principles for total influence. arXiv:2607.27184.
7. M. Sun, G. Waite, M. Bremner, C. Ferrie. Efficient fidelity estimation with few local Pauli measurements. arXiv:2510.08155.
8. L. Leone, S. F. E. Oliviero, A. Hamma. Nonstabilizerness determining the hardness of direct fidelity estimation. arXiv:2204.02995.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
