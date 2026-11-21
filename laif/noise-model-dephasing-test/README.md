# Testing dephasing in an unknown basis against its depolarizing model

2026-11-21

## Problem

A device applies the same channel E on ℂ^d at every use. Either E is the depolarizing model

M_p = (1 − p) id + p Λ,  Λ(ρ) = (ρ + Tr(ρ) I)/(d + 1),

or E is dephasing in an unknown fixed basis,

E_{p,U} = (1 − p) id + p Δ_U,  Δ_U(ρ) = Σ_k P_k ρ P_k,  P_k = U|k⟩⟨k|U†,

for some unitary U. The two have the same entanglement fidelity and average gate fidelity, and Λ is the average of Δ_U over uniformly random U [1]. An ordinary strategy is an adaptive circuit that calls the device one call at a time on a d-dimensional query system, with unlimited quantum memory and known operations between calls [1, Definition 4]. In [1, Theorem 3], for d = 2^n, every ordinary strategy that decides between the two cases with success probability at least 2/3 needs Ω(d^{1/16}/p) calls, while O(d²/p) calls suffice through an approximate simulation of the quantum switch [1, Section 5.1]. Sharpening these bounds is named as open in [1, Section 6]. After one call the two channels are at diamond distance of order p, so general identity tests against a fixed channel with unentangled measurements [3], or against a completely depolarizing reference [4], apply with cost growing as 1/p².

| | calls |
|---|---|
| Previous best bound | O(d²/p) [1, Section 5.1] |
| Lower bound (d = 2^n) | Ω(d^{1/16}/p) [1, Theorem 3] |
| Theorem 1 | O(d/p) |
| Theorem 2 (parallel strategies) | Ω(√d/p) |

## Result

**Theorem 1.** For every d ≥ 2 and 0 < p ≤ 1 there is an ordinary strategy that makes O(d/p) calls, outputs "model" with probability at least 2/3 if E = M_p, and outputs "dephasing" with probability at least 2/3 if E = E_{p,U}, for every unitary U.

The theorem follows from the state certification test of [2, Theorem 1.4] once the device is called in blocks; the proof below gives the details and the constants.

**Theorem 2.** A parallel strategy prepares one state ρ on n query systems and an ancilla, applies the device to the n query systems at once, and measures. Every parallel strategy that outputs the correct answer with probability at least 2/3 for M_p and for every E_{p,U} makes at least √d/(11p) calls.

## Proof of Theorem 1

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

## Proof of Theorem 2

*Reduction to p = 1.* E_{p,U}^{⊗n} = Σ_S p^{|S|}(1 − p)^{n−|S|} Δ_U^{⊗S} ⊗ id and M_p^{⊗n} = Σ_S p^{|S|}(1 − p)^{n−|S|} Λ^{⊗S} ⊗ id, summed over the subsets S of the calls. A strategy that is correct with probability 2/3 for every U is also correct with probability 2/3 on average over a uniformly random U, so its two output states, averaged over U and with M_p, are at trace distance at least 1/3. By convexity this distance is at most E_S β(|S|), where β(s) is the largest trace distance between (E_U Δ_U^{⊗s} ⊗ id)(ρ) and (Λ^{⊗s} ⊗ id)(ρ) over all states ρ. It remains to show β(s) ≤ 3.42 s/√d, since then 1/3 ≤ 3.42 pn/√d.

*Measure and prepare.* With K_w = |w⟩⟨w| on (ℂ^d)^{⊗s}, Δ_U^{⊗s}(X) = d^s E_k K_w X K_w† with w = u_{k_1} ⊗ ⋯ ⊗ u_{k_s} for independent uniform indices k_i, and Λ^{⊗s}(X) = d^s E_v K_w X K_w† with w = v_1 ⊗ ⋯ ⊗ v_s for independent uniformly random unit vectors v_i. Draw independent standard normal vectors g_1, …, g_s in ℂ^d and independent uniform indices k_i. Put w₂ = ⊗ g_i/‖g_i‖ (exactly the fresh law), let e_1, …, e_s be the orthonormalization of g_1, …, g_s in this order and w_H = ⊗ e_i, and let w₁ use, for the r distinct indices in order of first appearance, the orthonormalization of the corresponding g's, repeated wherever an index repeats (exactly the law of one uniformly random basis). For each of the three choices set V(ω) = d^{s/2} (K_{w(ω)} ⊗ I) ρ^{1/2}. The two output states are σ_j = E V_j V_j†, with E ‖V_j‖₂² = 1 for j = 1, 2. From XX† − YY† = X(X − Y)† + (X − Y)Y†,

‖σ₁ − σ₂‖₁ ≤ 2 (E ‖V₁ − V₂‖₂²)^{1/2} ≤ 2 (√λ_max(Z_{1H}) + √λ_max(Z_{H2})),  Z_{ab} = d^s E[(K_{w_a} − K_{w_b})†(K_{w_a} − K_{w_b})].

*The orthonormalization term.* (K_a − K_b)†(K_a − K_b) = |a⟩⟨a| + |b⟩⟨b| − ⟨a|b⟩|a⟩⟨b| − ⟨b|a⟩|b⟩⟨a|. Write P_i for the projector onto the span of e_1, …, e_{i−1} and v_i = g_i/‖g_i‖ = c_i e_i + P_i v_i with c_i = ‖(1 − P_i) v_i‖. Then ⟨w_H|w₂⟩ |w_H⟩⟨w₂| = ⊗_i (c_i² |e_i⟩⟨e_i| + c_i |e_i⟩⟨P_i v_i|). The direction of P_i g_i is uniform on the unit sphere of the span of e_1, …, e_{i−1} and enters nothing else, so every term containing a factor |e_i⟩⟨P_i v_i| has mean zero. The c_i are independent of the e_i with E c_i² = (d − i + 1)/d. With Q = (d)_s E|w_H⟩⟨w_H|, where (d)_s = d(d − 1)⋯(d − s + 1), and γ = d^s/(d)_s, this gives the exact identity

Z_{H2} = γQ + I − 2Q = (γ − 1) I + (2 − γ) R,  R = I − Q.

For every unitary the sum of |u_{a_1} ⋯ u_{a_s}⟩⟨u_{a_1} ⋯ u_{a_s}| over all index tuples is I, and Q is the average of the sum over the tuples of distinct indices. So R is the average of the sum over tuples with a repeated index, and R ≤ Σ_{i<j} 2Π^{ij}_sym/(d + 1), where Π^{ij}_sym is the projector onto the symmetric subspace of the systems i and j, since d E|uu⟩⟨uu| = 2Π_sym/(d + 1) for a uniformly random unit vector u. Hence λ_max(Z_{H2}) ≤ (γ − 1) + (2 − γ) s(s − 1)/(d + 1) when γ ≤ 2.

*The repetition term.* w₁ = w_H unless two indices coincide (event C), and (K₁ − K_H)†(K₁ − K_H) ≤ 2|w₁⟩⟨w₁| + 2|w_H⟩⟨w_H|. On one side d^s E[1{k_i = k_j} |w₁⟩⟨w₁|] = 2Π^{ij}_sym/(d + 1) ⊗ I; on the other w_H is independent of the indices, P(C) ≤ s(s − 1)/(2d), and d^s E|w_H⟩⟨w_H| = γQ ≤ γI. So λ_max(Z_{1H}) ≤ 2s(s − 1)/(d + 1) + γ s(s − 1)/d.

*Constants.* If s² ≤ d then (d)_s/d^s ≥ 1 − s(s − 1)/(2d) ≥ 1/2, so γ ≤ 2 and γ − 1 ≤ s²/d. Then λ_max(Z_{1H}) ≤ 4s²/d and λ_max(Z_{H2}) ≤ 2s²/d, and the trace distance (1/2)‖σ₁ − σ₂‖₁ is at most (2 + √2) s/√d ≤ 3.42 s/√d. For s² > d this bound exceeds 1 and holds trivially. ∎

## Check

`sim/check.py` checks the block formulas against direct composition, the identity for ‖σ_E − σ_M‖₂², the exact moments E X and E X² against Monte Carlo sampling, the constant (E X)²/(4 E X²) for 2 ≤ d ≤ 2000 in exact rational arithmetic, and the gap ‖σ_E − σ_M‖₂ ≥ √X/2 on random instances with q in [0, 1] and q′ ≤ 1/2. `sim/parallel.py` samples the three couplings and compares Z_{H2} with its exact form for s = 2 and s = 3, where R follows by inclusion and exclusion; the error shrinks as the sample size grows. It then checks the bound on λ_max(Z_{H2}) against the exact spectrum for d ≤ 10, which is attained for s = 2, and the sampled λ_max(Z_{1H}) against its exact value 3/(d + 1) for s = 2. `sim/pz_all_d.py` proves E X² ≤ 2 (E X)² for all d ≥ 2: in t = d − 2 the numerator and the denominator of 2 (E X)² − E X² have nonnegative coefficients.

## Scope

- The strategy measures jointly across the O(d) stored outputs, as [2] does; it uses one query system and sequential calls only.
- For adaptive strategies and d = 2^n the query complexity lies between d^{1/16}/p [1] and d/p. Theorem 2 covers parallel strategies only; the tester of Theorem 1 is sequential.
- Not formalized in Lean. [2, Theorem 1.4] is used as stated there.

## References

[1] D. Li. Infinite or indefinite: the query cost of simulating the quantum switch. arXiv:2611.16229.

[2] C. Bădescu, R. O'Donnell, J. Wright. Quantum state certification. STOC 2019. arXiv:1708.06002.

[3] G. Rosenthal, H. Aaronson, S. Subramanian, A. Datta, T. Gur. Quantum channel testing in average-case distance. arXiv:2409.12566.

[4] O. Fawzi, N. Flammarion, A. Garivier, A. Oufkir. Quantum channel certification with incoherent strategies. COLT 2023, PMLR 195. arXiv:2303.01188.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
