# Shadow norm under random Pauli measurements: the exact worst case over observables

2026-11-11

## Problem

Classical shadows with random Pauli measurements [2] measure every copy of an unknown N-qubit state σ in a uniformly random basis B ∈ {X, Y, Z}^N and record the outcome x ∈ {±1}^N. The estimator

ρ̂_{B,x} = ⊗_i (3 |b_i x_i⟩⟨b_i x_i| − I)

is unbiased for σ, and Tr(O ρ̂) estimates Tr(O σ). Its variance is governed by the shadow norm

‖O‖²_shadow = max_σ E_{B, x∼σ} |Tr(O ρ̂_{B,x})|².

For an observable on k qubits the known bounds grow like 4^k ‖O‖²_∞ [2]. For global observables, such as the fidelity with a target state, the first bound sublinear in d = 2^N was proved in [1]: ‖ρ‖²_shadow = o(d^{0.9675}) ‖ρ‖₂² for positive semidefinite ρ, which gives fidelity estimation with o(d^{0.9675}) log(1/δ)/ε² copies.

## Result

**Theorem 1.** For every operator O on N qubits and every state σ,

E_{B, x∼σ} |Tr(O ρ̂_{B,x})|² ≤ (1 + 1/√2)^N Tr(O†O).

So ‖O‖²_shadow ≤ d^{0.7716} ‖O‖₂², since log₂(1 + 1/√2) = 0.77155. The constant is exact for every N: a product operator O = O₁^{⊗N} with O₁ ∝ I + (1 + √2) Z and σ = |0⟩⟨0|^{⊗N} attains equality.

**Corollary 1** (fidelity estimation). For every target state ρ, pure or mixed, the classical-shadow protocol of [1] with random Pauli basis measurements estimates Tr(ρσ) to ±ε with probability 1 − δ using

O(d^{0.7716} log(1/δ) / ε²)

copies, with measurements chosen independently of ρ. Previous best bound: o(d^{0.9675}) log(1/δ)/ε² [1].

**Corollary 2** (shadow tomography). Expectation values of M observables O_1, …, O_M, of any sign, can be estimated to ±ε with O(d^{0.7716} max_i ‖O_i‖₂² log(M/δ)/ε²) Pauli basis measurements. Previous best bound: o(d^{0.9675}) max_i ‖O_i‖₂² log M/ε² for positive semidefinite O_i [1].

**States.** Over positive semidefinite O the worst case is smaller. Product pure states give exactly 1.5^N = d^{0.585}. An explicit 4-qubit mixed state gives the ratio 5.3988, and tensor powers of it give ‖ρ‖²_shadow ≥ 5.3988^{N/4} ‖ρ‖₂² = d^{0.608} ‖ρ‖₂² (`sim/state_lb.py`, state in `sim/rho_N4.txt`). So for states the exponent of this protocol lies between 0.608 and 0.7716.

## Proof

*Superoperator form.* Use the trace inner product ⟨⟨A|B⟩⟩ = Tr(A†B) on operators. Since ρ̂ is self-adjoint, |Tr(O ρ̂)|² = ⟨⟨O| (|ρ̂⟩⟩⟨⟨ρ̂|) |O⟩⟩, and so

E_{B, x∼σ} |Tr(O ρ̂_{B,x})|² = ⟨⟨O| L(σ) |O⟩⟩,  L(σ) = Σ_{B,x} 3^{−N} Tr(σ Π_{B,x}) |ρ̂_{B,x}⟩⟩⟨⟨ρ̂_{B,x}|,

with Π_{B,x} = ⊗_i |b_i x_i⟩⟨b_i x_i|. The map L has the measure-and-prepare form X ↦ Σ_k Tr(X E_k) R_k with E_k ≥ 0 and R_k ≥ 0. Bases, outcomes, projectors and estimators all factor over the qubits, so L = L₁^{⊗N}. With ν(Φ) = sup over states σ of λ_max(Φ(σ)), this gives the bound ν(L) Tr(O†O).

*Product step.* Let L₁(X) = Σ_k Tr(X E_k) R_k with E_k, R_k ≥ 0, and let L₂ be a positive map. Then ν(L₁ ⊗ L₂) ≤ ν(L₁) ν(L₂). Take a pure state σ on both factors and a unit vector φ. Then (L₁ ⊗ L₂)(σ) = Σ_k R_k ⊗ L₂(X_k) with X_k = Tr₁[(E_k ⊗ I) σ] ≥ 0, and with Y_k = Tr₁[(R_k ⊗ I) |φ⟩⟨φ|] ≥ 0,

⟨φ| (L₁ ⊗ L₂)(σ) |φ⟩ = Σ_k Tr(Y_k L₂(X_k)) ≤ ν(L₂) Σ_k Tr X_k Tr Y_k = ν(L₂) Tr(φ₁ L₁(σ₁)) ≤ ν(L₁) ν(L₂),

where σ₁ and φ₁ are the reduced states on the first factor. This is the case p = ∞ of the multiplicativity of maximal output norms of entanglement-breaking channels [3]. By induction ν(L₁^{⊗N}) ≤ ν(L₁)^N, and products of single-qubit optimizers give equality.

*One qubit.* In the basis {I, X, Y, Z}/√2 the estimator ρ̂_{b,s} = (I + 3s P_b)/2 has coordinates (1, 3s e_b)/√2, and a state with Bloch vector r gives outcome s in basis b with probability (1 + s r_b)/2. So

L₁(σ) = (1/3) Σ_b Σ_s (1 + s r_b)/2 · (1/2) (1, 3s e_b)(1, 3s e_b)ᵀ = [[1/2, rᵀ/2], [r/2, (3/2) I₃]].

Its largest eigenvalue is 1 + √(1 + |r|²)/2, at most 1 + 1/√2, with equality for pure states. The eigenvector for r = e_z is (1, 0, 0, 1 + √2) up to scale, which is O₁.

*Corollaries.* The single-copy variance of the estimator Tr(ρ ρ̂) is at most ‖ρ‖²_shadow ≤ (1 + 1/√2)^N Tr(ρ²) ≤ d^{0.7716}. The median of means then gives Corollary 1, and a union bound over the M observables gives Corollary 2.

## Check

`sim/check_bound.py` checks the closed form of L₁ and its largest eigenvalue, and tests random complex and self-adjoint O against random entangled σ for N ≤ 4; no pair exceeds the bound. It also checks that the product optimizer attains equality for N ≤ 4, and that an alternating search over self-adjoint O and states σ for N = 2, 3 ends at exactly (1 + 1/√2)^N. `sim/shadow.py` computes the second-moment operator Σ_{B,x} 3^{−N} Tr(O ρ̂_{B,x})² Π_{B,x}, whose largest eigenvalue is the shadow norm of O, and checks unbiasedness. `sim/search.py` searches over states. `sim/state_lb.py` evaluates the saved 4-qubit state (ratio at least 5.39) and checks that the ratio is multiplicative under tensor products.

## Scope

- **Not formalized:** the theorem has no Lean proof.
- Theorem 1 is tight over all observables. Over states it is not: the exponent of the classical-shadow protocol for fidelity estimation lies between 0.608 and 0.7716, and the lower end is numerical.
- The corollaries concern this protocol, with Pauli basis measurements chosen independently of the target. Protocols that adapt the bases to the target are not covered.

## References

[1] J. Acharya, A. Dharmavarapu, Y. Liu, N. Yu. Sublinear Copies Suffice for Fidelity Estimation with Pauli Measurements. arXiv:2609.35547.
[2] H.-Y. Huang, R. Kueng, J. Preskill. Predicting many properties of a quantum system from very few measurements. Nature Physics 16 (2020) 1050-1057, arXiv:2002.08953.
[3] C. King. Maximal p-norms of entanglement breaking channels. arXiv:quant-ph/0212057.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
