# Sharper error bounds for agnostic process tomography

2026-11-12

## Problem

In agnostic process tomography [1], an algorithm has query access to an unknown channel E on n qubits (d = 2ⁿ) and a known class C of unitaries, and outputs a hypothesis with error at most α·opt(E, C) + ε, where opt is the smallest error of a member of C. Two distances are used [1, Definitions 10 and 12]:

- the average distance d_avg(E_1, E_2) = (E_ψ d_tr(E_1(ψ), E_2(ψ))²)^{1/2}, with ψ uniformly random and d_tr the trace distance;
- the normalized 2-norm distance d_F(Φ, Ψ) = ‖v(Φ) − v(Ψ)‖_2/√2 of the channel states v(Φ) = (1 ⊗ Φ)(|Ω⟩⟨Ω|), |Ω⟩ = d^{−1/2} Σ_i |i⟩|i⟩, where ‖·‖_2 is the entrywise 2-norm.

Previous best bounds [1, Proposition 3, Corollaries 7 and 8]: for a finite class C, selecting the member with the smallest estimated average infidelity gives d_avg ≤ opt^{1/4} + ε with O(log(|C|/δ)/ε⁴) queries, and the same up to a term η^{1/4} for classes with covering nets at scale η, such as circuits of G two-qubit gates. [1, Proposition 4 and Corollaries 9 to 12]: applying a (1, ε², δ)-agnostic state tomography algorithm in fidelity on v(E) gives d_F ≤ 2^{1/4} opt^{1/2} + ε, for stabilizer circuits, stabilizer circuits with few T gates and products of one-qubit unitaries. Improving both to 1-agnostic is stated as an open problem in [1, Section 1.5].

## Results

**Theorem 1.** The algorithm of [1, Proposition 4] is 1-agnostic: with the same queries and time, its output Φ′ satisfies

d_F(E, Φ′) ≤ (opt(E, C)² + ε²)^{1/2} ≤ opt(E, C) + ε.

The same holds for [1, Corollaries 9 to 12].

**Theorem 2.** The algorithm of [1, Proposition 3] outputs U ∈ C with

d_avg(U, E) ≤ (2 opt(E, C)² + ε²)^{1/2} ≤ √2 · opt(E, C) + ε

with O(log(|C|/δ)/ε⁴) queries. Together with the bound of [1], d_avg ≤ min{√2 · opt, opt^{1/4}} + ε; the new bound is the smaller one for opt < 2^{−2/3} ≈ 0.63. For one qubit (n = 1) the algorithm is 1-agnostic: d_avg(U, E) ≤ (opt² + ε²/2)^{1/2} ≤ opt + ε. For a class with covering number N(C, d_avg, η) the algorithm of [1, Corollary 7] gives d_avg ≤ √2(opt + η) + ε with O(log(N(C, d_avg, η)/δ)/ε⁴) queries; for circuits of G two-qubit gates this is d_avg ≤ √2 opt + ε with Õ(G log(n/δ)/ε⁴) queries.

Both bounds use the following fact. For a pure state φ and any state σ, the operator φ − σ has at most one positive eigenvalue, equal to d_tr(φ, σ), and its negative eigenvalues sum to −d_tr(φ, σ). Hence

d_tr(φ, σ)² ≤ ‖φ − σ‖_2² ≤ 2 d_tr(φ, σ)²,   ‖φ − σ‖_2² = 1 − 2⟨φ|σ|φ⟩ + tr σ².   (∗)

So the squared 2-norm distance to a pure state is an affine function of the fidelity, with a constant tr σ² that does not depend on φ.

## Proofs

*Fact (∗).* Since σ ⪰ 0, φ − σ ⪯ φ, and φ has rank one, so φ − σ has at most one positive eigenvalue λ_+. Its trace is 0, so the negative eigenvalues μ_i satisfy Σ|μ_i| = λ_+, and d_tr = (λ_+ + Σ|μ_i|)/2 = λ_+. Then ‖φ − σ‖_2² = λ_+² + Σ μ_i² with 0 ≤ Σ μ_i² ≤ (Σ|μ_i|)² = λ_+². The identity is the expansion of tr((φ − σ)²) with tr φ² = 1. ∎

*Theorem 1.* The proper state tomography step outputs a pure state ψ ∈ D with ⟨ψ|v|ψ⟩ ≥ max_{φ∈D} ⟨φ|v|φ⟩ − ε², where v = v(E) and D is a class of pure states that contains v(U) for every U ∈ C. By (∗),

2 d_F(E, ψ)² = ‖v − ψ‖_2² = tr v² + 1 − 2⟨ψ|v|ψ⟩ ≤ min_{φ∈D} (tr v² + 1 − 2⟨φ|v|φ⟩) + 2ε² = min_{φ∈D} 2 d_F(E, φ)² + 2ε².

Here d_F(E, φ) = ‖v − φ‖_2/√2. Since D contains the channel states of C, min_{φ∈D} d_F(E, φ) ≤ opt(E, C), so the output Φ′, the map with v(Φ′) = ψ (in general not a channel, so the learner is improper as in [1]), satisfies d_F(E, Φ′)² ≤ opt² + ε². Purity of ψ is used in (∗). ∎

*Theorem 2.* For U ∈ C let I(U) = E_ψ(1 − ⟨ψ|U†E(ψ)U|ψ⟩) be the average infidelity and H(U) = E_ψ ‖Uψ U† − E(ψ)‖_2². By (∗),

H(U) = 2I(U) − 1 + E_ψ tr E(ψ)²,

where the last term does not depend on U. Both I and H are averages of quantities of degree two in ψψ†, so they are the same for uniformly random inputs and for random stabilizer states, which form a 2-design; this is the ensemble of [1]. The estimates of [1, Equation (5.7)] give |Î(U) − I(U)| ≤ ε′ for all U ∈ C with O(log(|C|/δ)/ε′²) queries, and the selected Û minimizes Î. Then H(Û) ≤ min_U H(U) + 4ε′, and by (∗) applied for each ψ,

d_avg(Û, E)² ≤ H(Û) ≤ min_U H(U) + 4ε′ ≤ 2 min_U d_avg(U, E)² + 4ε′ = 2 opt² + 4ε′.

With ε′ = ε²/4, d_avg(Û, E)² ≤ 2 opt² + ε². The analysis of [1] gives d_avg(Û, E)² ≤ opt^{1/2} + 2ε′ for the same algorithm, hence the minimum. For n = 1, φ − σ is a traceless 2 × 2 matrix, so ‖φ − σ‖_2² = 2 d_tr² exactly, H = 2 d_avg², and d_avg(Û, E)² ≤ (min_U H(U) + 4ε′)/2 = opt² + ε²/2. For a covering net M of C at scale η, the same argument on M gives d_avg² ≤ 2 min_{V∈M} d_avg(V, E)² + 4ε′, and min_{V∈M} d_avg(V, E) ≤ opt + η by the triangle inequality for d_avg [1, Lemma 7]. The covering numbers of circuits of G gates [1, Lemma 9] give the last statement with η = ε/(2√2). ∎

## Check

`sim/check.py` asserts (∗) on 3000 random pairs of a pure state and a mixed state in dimensions 2 to 8 (the ratio ‖φ − σ‖_2²/d_tr² lies between 1.22 and 2.00), that the fidelity maximizer and the d_F minimizer coincide among the channel states of 6 random unitaries for 200 noisy channels in dimension 3, and, for 300 random finite classes and channels on an empirical distribution of 400 inputs, that H = 2I − 1 + E tr E(ψ)², that the minimizers of I and H coincide and that d_avg of the selected unitary is at most √2 times the optimum. For one qubit it asserts ‖φ − σ‖_2² = 2 d_tr² and that the selection attains the optimum on 200 instances. Output in `sim/out.txt`.

## Scope

- Written proofs with numerical checks. The estimation step, the agnostic state tomography algorithms and the covering numbers are used as stated in [1] and the works cited there.
- The factor √2 in Theorem 2 comes from (∗); for n ≥ 2 the exact factor of the infidelity selection lies between 1 and √2 and is not determined here.
- The quadratic relation between the error of the state tomography step (ε²) and the final error ε is unchanged.

## References

[1] C. Wadhwa, L. Lewis, E. Kashefi, M. Doosti. Agnostic process tomography. arXiv:2410.11957.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
