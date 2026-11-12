# Fractional colourings of large-expectation Pauli sets for product states

2026-11-12

## Problem

For an n-qubit state ρ and ε ∈ (0, 1), let B_ε(ρ) be the set of Pauli strings P with |tr(ρP)| ≥ ε, and let G(B_ε) be its anticommutation graph: two strings are adjacent if they anticommute. Independent sets of G are commuting sets, and a fractional colouring of size χ is a weighting w ≥ 0 of commuting sets with total weight χ such that every vertex is covered with weight at least 1. The smallest such χ is the fractional chromatic number χ_f.

It was conjectured in [1, Conjecture 13] that χ_f(G(B_ε)) = O(ε⁻²) for every state. A bound of this form, with a colouring that can be sampled efficiently, gives a two-copy Clifford shadow tomography protocol for any set of Pauli observables [1, Lemma 20]. The conjecture is refuted in [2]: every graph with α(G) < β(G) yields states for which χ_f(G(B_ε)) ε² is unbounded [2, Theorem B], where α is the independence number and β(G) = max_σ Σ_{A} tr(σA)² over the strings of a realization of G. It is asked in [2, Question 8] whether χ_f(G(B_ε)) = O(ε^{−κ}) holds for some κ > 0.

## Results

**Proposition 1.** Let ρ = ρ_1 ⊗ ⋯ ⊗ ρ_n be a product of single-qubit states, pure or mixed, or the image CρC† of such a product under a Clifford unitary C. Then χ_f(G(B_ε(ρ))) ≤ ε⁻² for every ε ∈ (0, 1). The constant 1 is attained.

So [2, Question 8] has a positive answer with κ = 2 for these states, with the constant of [1, Conjecture 13] equal to 1. The colouring is explicit and is sampled in time O(n) from the single-qubit expectation vectors. In the protocol of [1, Lemma 20], the set S_ε of the second stage satisfies |tr(ρP)| ≥ ε/2 for all P ∈ S_ε with high probability [1, eq. (10)], so G(S_ε) is an induced subgraph of G(B_{ε/2}) and has a fractional colouring of size at most 4ε⁻². For these states the protocol then uses O((log |S|)/ε⁴) two-copy Clifford measurements for any set S of Pauli observables.

**Proposition 2.** For every state ρ and every ε ∈ (0, 1),

χ_f(G(B_ε)) ≤ ε⁻² β_f(G(B_ε)),   β_f(G) = max { Σ_P y_P tr(σP)² : σ a state, y ≥ 0, Σ_{P∈I} y_P ≤ 1 for every commuting set I }.

Here β_f ≥ β/α, by the choice y = 1/α. So the quantity β/α, whose growth under graph products drives the counterexamples of [2, Theorem B], is a lower bound for the quantity β_f, which controls χ_f ε² from above. Proposition 2 is the linear programming duality route suggested in [1, Section 1], with the state σ free.

## Proofs

*Proposition 1.* Write the single-qubit states as ρ_i = (I + v_i · (X, Y, Z))/2 with expectation vectors v_i = (⟨X⟩_i, ⟨Y⟩_i, ⟨Z⟩_i), |v_i| ≤ 1, and P = P_1 ⊗ ⋯ ⊗ P_n. Then tr(ρP) = Π_{i : P_i ≠ I} ⟨P_i⟩_i.

For a basis choice s ∈ {X, Y, Z}ⁿ, the strings P with P_i ∈ {I, s_i} for all i commute, so I_s = {P ∈ B_ε : P_i ∈ {I, s_i} for all i} is a commuting set. Choose s at random with independent coordinates, Pr[s_i = σ] = q_i(σ) = ⟨σ⟩_i²/|v_i|² for v_i ≠ 0 and q_i(σ) = 1/3 for v_i = 0, and give I_s the weight ε⁻² Pr[s]. The total weight is ε⁻².

Let P ∈ B_ε. If P_i ≠ I, then ⟨P_i⟩_i ≠ 0, so v_i ≠ 0 and q_i(P_i) = ⟨P_i⟩_i²/|v_i|² ≥ ⟨P_i⟩_i². Hence P is covered with weight

ε⁻² Π_{i : P_i ≠ I} q_i(P_i) ≥ ε⁻² Π_{i : P_i ≠ I} ⟨P_i⟩_i² = ε⁻² tr(ρP)² ≥ 1.

For a Clifford unitary C, the map P ↦ CPC† permutes the Pauli strings up to sign, preserves commutation, and satisfies tr(CρC† · CPC†) = tr(ρP). So it maps B_ε(ρ) onto B_ε(CρC†) up to signs, and the two graphs are isomorphic.

For the constant, take n = 1 with v = (1/√2, 0, 1/√2) and ε = 1/√2. Then B_ε = {I, X, Z}, X and Z anticommute, and χ_f = 2 = ε⁻². ∎

*Proposition 2.* By linear programming duality, χ_f(G) equals the fractional clique number max { Σ_P y_P : y ≥ 0, Σ_{P∈I} y_P ≤ 1 for every independent set I }. Every P ∈ B_ε has tr(ρP)² ≥ ε², so Σ_P y_P ≤ ε⁻² Σ_P y_P tr(ρP)² ≤ ε⁻² β_f(G(B_ε)), with σ = ρ. For the lower bound on β_f, every commuting set of G has at most α(G) elements, so y = 1/α is feasible and gives Σ_P tr(σP)²/α, whose maximum over σ is β/α. ∎

## Check

`sim/fraccolour.py` computes χ_f exactly by linear programming over all maximal commuting sets, and checks with asserts:

- Proposition 1 for random product states, pure and mixed, on n ≤ 3 qubits and ε ∈ {0.2, 0.35, 0.5, 0.7}, together with the coverage of the colouring in the proof;
- the inequality of Proposition 2 with an optimal dual solution y, and the feasibility of y, for these states and for random pure states on 2 and 3 qubits;
- the case n = 1, v = (1/√2, 0, 1/√2), ε = 1/√2, where χ_f ε² = 1.

Output in `sim/fraccolour_out.txt`.

## Scope

- Written proofs, with the numerical checks for n ≤ 3.
- Proposition 1 covers products of single-qubit states and their Clifford images. For these states the large-expectation strings factor qubit by qubit; for general states [2, Question 8] stays open.
- Sampling the colouring of Proposition 1 needs the single-qubit expectation vectors. The sample count O((log |S|)/ε⁴) is for the protocol of [1, Lemma 20] with an optimal fractional colouring of G(S_ε), whose runtime is not bounded here.
- **Not formalized:** the results have no Lean proof.

## References

[1] R. King, D. Gosset, R. Kothari, R. Babbush. Triply efficient shadow tomography. PRX Quantum 6, 010336 (2025). arXiv:2404.19211.

[2] J. Stempin, S. Llorens, F. Huber. Counterexamples to the fractional coloring conjecture for triply efficient shadow tomography. arXiv:2608.20113.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
