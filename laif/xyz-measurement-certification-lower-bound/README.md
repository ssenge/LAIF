# Certifying a cat state with single-qubit X, Y and Z measurements needs Ω((3/2)^{n/2}) copies, even adaptively

2026-11-25

## Problem

A known pure target state |ψ⟩ on n qubits is to be certified, or its fidelity with an unknown lab state σ estimated, from copies of σ. With arbitrary measurements, Θ(1/ε) copies certify and Θ(1/ε²) copies estimate the fidelity to ±ε. Many experiments measure each qubit only along the axes X, Y or Z. In that model, the classical-shadow estimator with uniformly random axes estimates the fidelity with O(d^{0.7716}/ε²) copies, d = 2^n, for every target ([5]; earlier o(d^{0.9675})/ε² [1]). For almost all targets, X, Y, Z measurements certify with O(1/ε²) copies [6] and estimate the fidelity efficiently [7]. Without the axis restriction, adaptive single-qubit measurements certify every pure state from O(n/ε) copies [2], while algorithms with little adaptivity need 2^{Ω(n)} copies for some target [2, Theorem 2]. Concrete targets that cannot be certified with polynomially many single-qubit measurements are asked for in [3]; for general axes none exist [2]. With X, Y, Z axes only, the target ψ_n below is one. For measurements of single X, Y, Z strings, fidelity estimation is studied in [4], and the cost of such estimators grows with the distance from stabilizer states [8].

Lower bounds for a worst-case target, X, Y, Z measurements on every qubit, q = (2/3)^{n/2}:

| | certification (1 against 1 − ε) | fidelity estimation to ±ε |
|---|---|---|
| Upper bound, non-adaptive | | O(d^{0.7716}/ε²) [5] |
| Previous best lower bound | Ω(1/ε), the bound for arbitrary measurements; 2^{Ω(n)} for algorithms with little adaptivity [2, Theorem 2] | Ω(1/ε²), the bound for arbitrary measurements; 2^{Ω(n)} for algorithms with little adaptivity, implied by [2, Theorem 2] |
| Theorem 1, stored copies, any order, fully adaptive | ln(5/3)(3/2)^{n/2}/(2ε) | ln(5/3)(3/2)^{n/2}/(5ε) |
| Theorem 2, copies measured one after another, adaptive | | (2/225)(3/2)^{n/2}/ε² = Ω(d^{0.2924}/ε²) |

## Setting

Let |a⟩ be the single-qubit state whose expectation values of X, Y and Z are all 1/√3, and |ā⟩ a state orthogonal to it, with any phase. Define the cat state and its dephased version

|ψ_n⟩ = (|a⟩^{⊗n} + |ā⟩^{⊗n})/√2,  ρ_n = (|a⟩⟨a|^{⊗n} + |ā⟩⟨ā|^{⊗n})/2,

so ⟨ψ_n|ρ_n|ψ_n⟩ = 1/2. The state ψ_n is the cat state (|0⟩^{⊗n} + |1⟩^{⊗n})/√2 with one fixed single-qubit unitary applied to every qubit. For 0 ≤ s ≤ 1 let ρ_s = (1 − s)ρ_n + s|ψ_n⟩⟨ψ_n|, with fidelity (1 + s)/2, and for 0 < ε ≤ 1/2 let σ_ε = (1 − 2ε)|ψ_n⟩⟨ψ_n| + 2ερ_n, with fidelity 1 − ε.

**Model.** A strategy receives T copies of the lab state. It measures single qubits one at a time, each in the eigenbasis of X, Y or Z. Which qubit is measured next, along which axis, and whether to stop may depend on all earlier outcomes and on classical randomness. After an outcome e a qubit is left in the state |e⟩, uncorrelated with all other qubits, so measuring it again, along any axis, gives an outcome whose law is fixed by its earlier outcome and is the same under every hypothesis, so it adds only classical randomness; hence each qubit is measured at most once. At the end the strategy outputs a decision or an estimate.

- *Stored copies:* all T copies are held at once, and the next qubit may belong to any copy.
- *Copies one after another:* each copy is measured completely before the next one is used. Here the number of copies may be random; the bound of Theorem 2 is for its largest value, and with the same proof for its expectation under ρ_{5ε}.

## Result

**Theorem 1** (stored copies). For every n ≥ 1, with q = (2/3)^{n/2}:

(a) a strategy that tells ψ_n from ρ_n with success probability at least 2/3 under each hypothesis uses T ≥ ln(5/3)/ln(1 + q) ≥ ln(5/3)(3/2)^{n/2} copies;

(b) a strategy that accepts ψ_n and rejects σ_ε, each with probability at least 2/3, uses T ≥ ln(5/3)/ln(1 + 2εq) ≥ ln(5/3)(3/2)^{n/2}/(2ε) copies;

(c) for 0 < ε ≤ 1/10, a strategy that estimates ⟨ψ_n|σ|ψ_n⟩ to ±ε with probability at least 2/3 for every state σ uses T ≥ ln(5/3)(3/2)^{n/2}/(5ε) copies.

**Theorem 2** (copies one after another). For 0 < ε ≤ 1/10, a strategy that estimates ⟨ψ_n|σ|ψ_n⟩ to ±ε with probability at least 2/3 for every state σ uses at least (2/225)(3/2)^{n/2}/ε² copies.

Here ln(5/3) = 0.5108…, and (3/2)^{n/2} = d^{log₂(3/2)/2} with log₂(3/2)/2 = 0.29248…, so all bounds grow as d^{0.2924}. So with X, Y, Z measurements the worst-case exponent of fidelity estimation lies between 0.2924 and 0.7716 [5], and certification of the explicit target ψ_n costs exponentially many copies for every adaptive strategy.

## Proof

*Trees.* Given its random coins, a strategy is a decision tree: each node measures one not yet measured qubit along X, Y or Z. A random strategy is a mixture of such trees, and the bounds below hold for each tree, so they hold for the mixture. Measuring the remaining qubits at a leaf only refines the outcome, and refining cannot decrease the total variation distance, the chi-square divergence or the relative entropy (data processing). So assume every leaf ℓ has measured every qubit, with outcome states |e_j⟩, each an eigenvector of the chosen axis. The event of reaching ℓ is the product projector onto |e_ℓ⟩ = ⊗_j |e_j⟩.

*The per-qubit factor.* Along X, Y or Z the two outcome probabilities of |a⟩ are (1 ± 1/√3)/2 and those of |ā⟩ are (1 ∓ 1/√3)/2, so for every axis

Σ_e |⟨e|a⟩| |⟨e|ā⟩| = 2 · √((1 + 1/√3)(1 − 1/√3))/2 = √(2/3).

**Lemma 1.** Let Φ = φ ⊗ χ and Φ′ = φ′ ⊗ χ be unit vectors, where φ = ⊗_{j∈Q} φ_j and φ′ = ⊗_{j∈Q} φ′_j are product states on a set Q of qubits and χ is any state of the other qubits, the same in both. Then for every tree, Σ_ℓ |⟨e_ℓ|Φ⟩| |⟨e_ℓ|Φ′⟩| ≤ Π_{j∈Q} κ_j, with κ_j the largest value over the three axes of Σ_e |⟨e|φ_j⟩||⟨e|φ′_j⟩|.

*Proof.* Induction on the tree. If the root measures a qubit j ∈ Q with outcome e, both amplitudes split off the factor ⟨e|φ_j⟩ or ⟨e|φ′_j⟩, and the rest is a tree on vectors of the same form with Q replaced by Q \ {j}; summing over e gives the factor κ_j times the largest subtree bound. If it measures a qubit outside Q, both vectors leave the same unnormalized state ⟨e|χ⟩ of squared norm p_e on the other qubits, with Σ_e p_e = 1; both amplitudes scale by √p_e, so the sum is Σ_e p_e times the subtree sums, at most the largest of them. κ_j = 1 when φ_j = φ′_j. ∎

*Theorem 1.* Write a pattern s ∈ {0, 1}^T for the product state p_s of T copies in which copy t is |a⟩^{⊗n} if s_t = 0 and |ā⟩^{⊗n} if s_t = 1. Then ψ_n^{⊗T} = 2^{−T/2} Σ_s |p_s⟩. For a set A of copies, let τ_A be ψ_n^{⊗T} with the copies in A replaced by ρ_n. With Φ_r = p_r ⊗ ψ_n^{⊗(T∖A)} for patterns r on A, the leaf probabilities are

P_ψ(ℓ) = 2^{−|A|} |Σ_r ⟨e_ℓ|Φ_r⟩|²,  P_{τ_A}(ℓ) = 2^{−|A|} Σ_r |⟨e_ℓ|Φ_r⟩|²,

so P_ψ − P_{τ_A} = 2^{−|A|} Σ_{r≠r′} ⟨e_ℓ|Φ_r⟩⟨Φ_{r′}|e_ℓ⟩. By Lemma 1 with the per-qubit factor √(2/3) on the n qubits of each copy where r and r′ differ, Σ_ℓ |⟨e_ℓ|Φ_r⟩||⟨e_ℓ|Φ_{r′}⟩| ≤ q^{d(r,r′)}, with d the number of differing entries. Hence

Σ_ℓ |P_ψ(ℓ) − P_{τ_A}(ℓ)| ≤ 2^{−|A|} Σ_{r≠r′} q^{d(r,r′)} = (1 + q)^{|A|} − 1.

Success probability 2/3 under both hypotheses forces this sum to be at least 2/3.
(a) Take A = all copies: (1 + q)^T ≥ 5/3.
(b) σ_ε^{⊗T} is the mixture of the τ_A with A containing each copy independently with probability 2ε, so the sum is at most E[(1 + q)^{|A|}] − 1 = (1 + 2εq)^T − 1, and (1 + 2εq)^T ≥ 5/3.
(c) ρ_s^{⊗T} is the mixture over sets B, containing each copy independently with probability s, of ψ_n on B and ρ_n on the rest. Here ρ_n on the rest is a mixture of product patterns, and for each of them the same computation with B in place of A compares the term with ρ_n^{⊗T}, so Σ_ℓ |P_{ρ_s} − P_ρ| ≤ (1 + sq)^T − 1. The states ρ_0 = ρ_n and ρ_{5ε} have fidelities 1/2 and 1/2 + 5ε/2, so an estimate to ±ε tells them apart, and (1 + 5εq)^T ≥ 5/3.
Finally ln(1 + x) ≤ x. ∎

*Theorem 2.* Fix the tree for one copy, given the past. With u_ℓ = ⟨e_ℓ|a^{⊗n}⟩ and v_ℓ = ⟨e_ℓ|ā^{⊗n}⟩, the leaf probabilities are P_{ρ_s}(ℓ) = m_ℓ + s c_ℓ with m_ℓ = (|u_ℓ|² + |v_ℓ|²)/2 and c_ℓ = Re(u_ℓ v̄_ℓ). Lemma 1 for one copy gives Σ_ℓ |u_ℓ||v_ℓ| ≤ (2/3)^{n/2}; it is an equality, since the per-qubit factor is √(2/3) for every axis. Since c_ℓ² ≤ |u_ℓ|²|v_ℓ|² and 2xy/(x + y) ≤ √(xy) for x, y ≥ 0,

χ²(P_{ρ_s} ‖ P_{ρ_0}) = s² Σ_ℓ c_ℓ²/m_ℓ ≤ s² Σ_ℓ 2|u_ℓ|²|v_ℓ|²/(|u_ℓ|² + |v_ℓ|²) ≤ s² Σ_ℓ |u_ℓ||v_ℓ| = s²(2/3)^{n/2}.

The copies are independent and the tree for copy t depends only on earlier outcomes. By the chain rule, the relative entropy D between the two full outcome distributions is the sum over t of the expected relative entropy of copy t given the past, and D ≤ χ² for each copy, so D ≤ 25ε²(2/3)^{n/2} T for s = 5ε. Success probability 2/3 forces total variation at least 1/3, and total variation is at most √(D/2), so D ≥ 2/9 and T ≥ (2/225)(3/2)^{n/2}/ε². ∎

The argument follows the cross-term approach of [2, Section 3], which compares a superposition of product states with their mixture. With X, Y, Z axes and the state |a⟩, the per-qubit factor √(2/3) is the same for every allowed axis, and this is what makes the bound hold for every adaptive tree.

## Check

`sim/check.py` (output `sim/out_check.txt`) builds ψ_n and ρ_n and asserts, for n ≤ 6 and all 3^n settings of the axes, the leaf formulas, the identity Σ|u||v| = (2/3)^{n/2}, the bound χ²(P_ψ ‖ P_ρ) ≤ (2/3)^{n/2}, the per-copy chi-square bound for σ_ε at ε = 0.01, 0.1, 0.2, the identity χ²(P_{ρ_s} ‖ P_ρ) = s² Σ c²/m of Theorem 2, with P_{ρ_s} computed from the density matrix of ρ_s, for s up to 1, and the fidelity 1/2. The numbers below use the phase of |ā⟩ fixed in the scripts. For n ≤ 5 it asserts the identity and the bound on 200 random adaptive trees each, with the qubit order and the axes chosen at random from the outcomes so far. Over the non-adaptive settings, the largest χ²(P_ψ ‖ P_ρ) is 0.82, 0.75, 0.68, 0.64, 0.60, 0.57 times (2/3)^{n/2} for n = 1, …, 6, all attained by measuring every qubit along Z. For that setting `sim/allz.py` (output `sim/out_allz.txt`) computes χ² exactly up to n = 320: χ²/(2/3)^{n/2} times √n increases to 1.89 at n = 320, so the per-copy bound is attained up to a factor Θ(n^{−1/2}) (numerical). Since the squared distance between √P_ψ and √P_ρ is at least χ²/6 here (because |c_ℓ| ≤ m_ℓ), a likelihood-ratio test on all-Z data tells ψ_n from ρ_n with O(√n (3/2)^{n/2}) copies, so, for the phase of |ā⟩ fixed in the scripts, Theorem 1(a) is tight up to the factor √n for this pair, given the numerical asymptotics. `sim/inter.py` (output `sim/out_inter.txt`) draws 40 random fully adaptive trees on all nT qubits of T stored copies, for (n, T) = (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), and asserts the identity Σ_ℓ |⟨e_ℓ|p_s⟩||⟨e_ℓ|p_{s′}⟩| = q^{d(s,s′)}, the bound of Lemma 1 for every set A of copies and all patterns on A with ψ_n on the other copies, and the three bounds (1 + q)^T − 1, (1 + 2εq)^T − 1 and (1 + sq)^T − 1 on the summed leaf differences. `sim/blocks.py` is a local numerical search over non-adaptive settings: it minimizes the largest coefficient Σ|⟨e|A⟩||⟨e|A′⟩| over orthogonal pairs of k-qubit states A, A′ for k = 1, 2, 3; per qubit it finds √(2/3) each time, the value of the pair a, ā.

## Scope

- The model measures single qubits along X, Y and Z only. Measurements along other axes, joint measurements of several qubits, and measurements on several copies at once are not covered; with other single-qubit axes, polynomially many copies suffice [2].
- The 1/ε² dependence of fidelity estimation (Theorem 2) is proved for copies measured one after another; for stored copies Theorem 1(c) gives 1/ε.
- The lower bound concerns the worst case over targets: it is proved for the target ψ_n. The upper bound O(d^{0.7716}/ε²) [5] holds for every target.
- The hardness comes from the axis restriction alone: after the single-qubit rotation that maps ψ_n to (|0⟩^{⊗n} + |1⟩^{⊗n})/√2, measurements along the rotated axes of random elements of its stabilizer group accept with probability (1 + F)/2 at fidelity F, which certifies it with O(1/ε) copies.
- **Not formalized:** the theorems have no Lean proof.

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
