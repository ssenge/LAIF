# Certifying a cat state with single-qubit X, Y and Z measurements needs Ω((3/2)^{n/2}) copies, even adaptively

2026-11-25

## Problem

A known pure target state |ψ⟩ on n qubits is to be certified, or its fidelity with an unknown lab state σ estimated, from copies of σ. With arbitrary measurements, Θ(1/ε) copies certify and Θ(1/ε²) copies estimate the fidelity to ±ε. Many experiments measure each qubit only along the axes X, Y or Z. In that model, the classical-shadow estimator with uniformly random axes estimates the fidelity with O(d^{0.7716}/ε²) copies, d = 2^n, for every target ([5]; earlier o(d^{0.9675})/ε² [1]). For almost all targets, X, Y, Z measurements certify with O(1/ε²) copies [6] and estimate the fidelity efficiently [7]. Without the axis restriction, adaptive single-qubit measurements certify every pure state from O(n/ε) copies [2], while algorithms with little adaptivity need 2^{Ω(n)} copies for some target [2, Theorem 2]. Concrete targets that cannot be certified with polynomially many single-qubit measurements are asked for in [3]; for general axes none exist [2]. With X, Y, Z axes only, the target ψ_n below is one. For measurements of single X, Y, Z strings, fidelity estimation is studied in [4], and the cost of such estimators grows with the distance from stabilizer states [8].

Lower bounds for a worst-case target, X, Y, Z measurements on every qubit, q = (2/3)^{n/2}:

| | certification (1 against 1 − ε) | fidelity estimation to ±ε |
|---|---|---|
| Upper bound, non-adaptive | | O(d^{0.7716}/ε²) [5] |
| Previous best lower bound | Ω(1/ε), the bound for arbitrary measurements; 2^{Ω(n)} for algorithms with little adaptivity [2, Theorem 2] | Ω(1/ε²), the bound for arbitrary measurements; 2^{Ω(n)} for algorithms with little adaptivity, implied by [2, Theorem 2] |
| Theorems 1 and 2, stored copies, any order, fully adaptive | ln(5/3)(3/2)^{n/2}/(2ε) | ln(3/2)(3/2)^{n/2}/(16ε²) = Ω(d^{0.2924}/ε²) |

## Setting

Let |a⟩ be the single-qubit state whose expectation values of X, Y and Z are all 1/√3, and |ā⟩ a state orthogonal to it, with any phase. Define the cat state and its dephased version

|ψ_n⟩ = (|a⟩^{⊗n} + |ā⟩^{⊗n})/√2,  ρ_n = (|a⟩⟨a|^{⊗n} + |ā⟩⟨ā|^{⊗n})/2,

so ⟨ψ_n|ρ_n|ψ_n⟩ = 1/2. The state ψ_n is the cat state (|0⟩^{⊗n} + |1⟩^{⊗n})/√2 with one fixed single-qubit unitary applied to every qubit. For 0 ≤ s ≤ 1 let ρ_s = (1 − s)ρ_n + s|ψ_n⟩⟨ψ_n|, with fidelity (1 + s)/2, and for 0 < ε ≤ 1/2 let σ_ε = (1 − 2ε)|ψ_n⟩⟨ψ_n| + 2ερ_n, with fidelity 1 − ε.

**Model.** A strategy receives T copies of the lab state. It measures single qubits one at a time, each in the eigenbasis of X, Y or Z. Which qubit is measured next, along which axis, and whether to stop may depend on all earlier outcomes and on classical randomness. After an outcome e a qubit is left in the state |e⟩, uncorrelated with all other qubits, so measuring it again, along any axis, gives an outcome whose law is fixed by its earlier outcome and is the same under every hypothesis, so it adds only classical randomness; hence each qubit is measured at most once. At the end the strategy outputs a decision or an estimate.

All T copies are held at once, and the next qubit may belong to any copy, so strategies that measure the copies one after another are a special case.

## Result

**Theorem 1.** For every n ≥ 1, with q = (2/3)^{n/2}:

(a) a strategy that tells ψ_n from ρ_n with success probability at least 2/3 under each hypothesis uses T ≥ ln(5/3)/ln(1 + q) ≥ ln(5/3)(3/2)^{n/2} copies;

(b) a strategy that accepts ψ_n and rejects σ_ε, each with probability at least 2/3, uses T ≥ ln(5/3)/ln(1 + 2εq) ≥ ln(5/3)(3/2)^{n/2}/(2ε) copies.

**Theorem 2.** For 0 ≤ s ≤ 1 and every strategy, χ²(P_{ρ_s} ‖ P_{ρ_n}) ≤ (1 + s²q)^T − 1 for the outcome laws on T copies. Hence for 0 < ε < 1/4 a strategy that estimates ⟨ψ_n|σ|ψ_n⟩ to ±ε with probability at least 2/3 for every state σ uses T ≥ ln(3/2)/(16ε²q) = ln(3/2)(3/2)^{n/2}/(16ε²) copies.

Here ln(5/3) = 0.5108…, ln(3/2) = 0.4054…, and (3/2)^{n/2} = d^{log₂(3/2)/2} with log₂(3/2)/2 = 0.29248…, so all bounds grow as d^{0.2924}. So with X, Y, Z measurements the worst-case exponent of fidelity estimation lies between 0.2924 and 0.7716 [5], and certification of the explicit target ψ_n costs exponentially many copies for every adaptive strategy.

*Non-vacuity.* All states used are valid for the stated ranges of ε. The bounds exceed one copy: Theorem 1(a) from n = 3 on, Theorem 1(b) for every n once ε ≤ 1/4, and Theorem 2 for every n once ε ≤ 1/8. For the phase of |ā⟩ fixed in the scripts, the chi-square bound of Theorem 2 is attained up to a factor 0.8165 at one copy and n = 1 (`sim/stored2.py`), and the per-copy factor √(2/3) is an equality for every axis.

**Corollary 3** (other finite sets of axes). Let S be a finite set of unit vectors of ℝ³, and κ(S) the minimum over unit vectors r of max_{b∈S} √(1 − (r·b)²). Then κ(S) < 1, since finitely many great circles do not cover the sphere. Let |a⟩ be the state with |a⟩⟨a| = (I + r·σ)/2 for a minimizing r, where σ = (X, Y, Z), and |ā⟩ orthogonal to it. For strategies that measure every qubit along an axis of S, Theorems 1 and 2 hold with q = κ(S)^n, so the bounds grow as d^{log₂(1/κ(S))}. For S = {X, Y, Z}, κ = √(2/3), the case above. For S = {X, Z}, κ = 1/√2 at r = (1, 0, 1)/√2, which gives a target with real amplitudes and the bounds Ω(d^{1/2}/ε) for certification and Ω(d^{1/2}/ε²) for fidelity estimation.

*Proof.* Along an axis b the outcome probabilities are (1 ± r·b)/2 for |a⟩ and (1 ∓ r·b)/2 for |ā⟩, so Σ_e |⟨e|a⟩||⟨e|ā⟩| = √(1 − (r·b)²) ≤ κ(S). The proofs below use the per-qubit factor only through this upper bound: in Lemma 1, and in Theorem 2, where E[h_t after] = λ_b h_t ≤ κ(S)h_t and E[r_t²] ≤ κ(S)h_t. The identity Σ_e ⟨e|a⟩⟨ā|e⟩ = ⟨ā|a⟩ = 0 holds in every basis. ∎

## Proof

*Trees.* Given its random coins, a strategy is a decision tree: each node measures one not yet measured qubit along X, Y or Z. A random strategy is a mixture of such trees; recording the coins as part of the outcome, the total variation distance and the chi-square divergence become averages over the coins of their values for single trees, so bounds for each tree hold for the mixture. Measuring the remaining qubits at a leaf only refines the outcome, and refining cannot decrease the total variation distance, the chi-square divergence or the relative entropy (data processing). So assume every leaf ℓ has measured every qubit, with outcome states |e_j⟩, each an eigenvector of the chosen axis. The event of reaching ℓ is the product projector onto |e_ℓ⟩ = ⊗_j |e_j⟩.

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
Finally ln(1 + x) ≤ x. ∎

*Theorem 2.* Fix a tree on all nT qubits. For a leaf ℓ and a copy t, let u_t and v_t be the products of ⟨e_j|a⟩ and of ⟨e_j|ā⟩ over the qubits j of copy t, m_t = (|u_t|² + |v_t|²)/2 and c_t = Re(u_t v̄_t). Since ρ_s^{⊗T} is a product over copies and each copy of ρ_s has the leaf weight m_t + s c_t,

P_{ρ_s}(ℓ) = P_{ρ_n}(ℓ) Π_t (1 + s r_t),  r_t = c_t/m_t.

Run the tree under ρ_n^{⊗T}. At a node that measures a qubit of copy t, let u′, v′ be the products over the qubits of copy t measured so far and m′ = (|u′|² + |v′|²)/2. The outcome e has conditional probability m′_e/m′, where m′_e is m′ with u′⟨e|a⟩ and v′⟨e|ā⟩ in place of u′ and v′; this depends on the past only through copy t. Nodes with m′ = 0 are reached with probability 0 under both laws, since |c_t| ≤ m_t. Let λ = √(2/3), h_t = |u′||v′|/m′, R_t the number of unmeasured qubits of copy t, g_t = h_t λ^{R_t}, and

Z = Π_{t finished} (1 + s r_t)² · Π_{t unfinished} (1 + s² g_t).

At the root every g_t equals λ^n = q, so Z = (1 + s²q)^T, and at a leaf Z = (P_{ρ_s}/P_{ρ_n})². At each node only the factor of the measured copy changes, and its conditional expectation does not increase:

- *Not the last qubit of copy t:* E[h_t after] = Σ_e (m′_e/m′) |u′||v′||⟨e|a⟩||⟨e|ā⟩|/m′_e = λh_t, and R_t drops by one, so E[g_t after] = g_t.
- *The last qubit (R_t = 1):* with c_e = Re(u′v̄′⟨e|a⟩⟨ā|e⟩), the new value is r_t = c_e/m′_e. Since Σ_e ⟨e|a⟩⟨ā|e⟩ = ⟨ā|a⟩ = 0, E[r_t] = Σ_e c_e/m′ = 0. Since |c_e| ≤ |u′||v′||⟨e|a⟩||⟨e|ā⟩| ≤ m′_e, E[r_t²] = Σ_e c_e²/(m′ m′_e) ≤ λh_t = g_t. So E[(1 + s r_t)²] = 1 + s²E[r_t²] ≤ 1 + s²g_t.

Hence χ²(P_{ρ_s} ‖ P_{ρ_n}) + 1 = E[Z at the leaf] ≤ (1 + s²q)^T. If an event has probability at least 2/3 under one law and at most 1/3 under the other, the chi-square divergence of the two-outcome coarse-graining, and hence χ², is at least (1/3)²/((1/3)(2/3)) = 1/2, so (1 + s²q)^T ≥ 3/2. For s > 4ε the states ρ_n and ρ_s have fidelities 1/2 and 1/2 + s/2 with ψ_n, more than 2ε apart, so an estimate to ±ε tells them apart. With ln(1 + x) ≤ x this gives T ≥ ln(3/2)/(s²q) for every s in (4ε, 1], hence T ≥ ln(3/2)/(16ε²q). ∎

The proof of Theorem 1 follows the cross-term approach of [2, Section 3], which compares a superposition of product states with their mixture. With X, Y, Z axes and the state |a⟩, the per-qubit factor √(2/3) is the same for every allowed axis, and this is what makes the bound hold for every adaptive tree.

## Check

`sim/check.py` (output `sim/out_check.txt`) builds ψ_n and ρ_n and asserts, for n ≤ 6 and all 3^n settings of the axes, the leaf formulas, the identity Σ|u||v| = (2/3)^{n/2}, the bound χ²(P_ψ ‖ P_ρ) ≤ (2/3)^{n/2}, the per-copy chi-square bound for σ_ε at ε = 0.01, 0.1, 0.2, the one-copy identity χ²(P_{ρ_s} ‖ P_ρ) = s² Σ c²/m, with P_{ρ_s} computed from the density matrix of ρ_s, for s up to 1, and the fidelity 1/2. The numbers below use the phase of |ā⟩ fixed in the scripts. For n ≤ 5 it asserts the identity and the bound on 200 random adaptive trees each, with the qubit order and the axes chosen at random from the outcomes so far. Over the non-adaptive settings, the largest χ²(P_ψ ‖ P_ρ) is 0.82, 0.75, 0.68, 0.64, 0.60, 0.57 times (2/3)^{n/2} for n = 1, …, 6, all attained by measuring every qubit along Z. For that setting `sim/allz.py` (output `sim/out_allz.txt`) computes χ² exactly up to n = 320: χ²/(2/3)^{n/2} times √n increases to 1.89 at n = 320, so the per-copy bound is attained up to a factor Θ(n^{−1/2}) (numerical). Since the squared distance between √P_ψ and √P_ρ is at least χ²/6 here (because |c_ℓ| ≤ m_ℓ), a likelihood-ratio test on all-Z data tells ψ_n from ρ_n with O(√n (3/2)^{n/2}) copies, so, for the phase of |ā⟩ fixed in the scripts, Theorem 1(a) is tight up to the factor √n for this pair, given the numerical asymptotics. `sim/inter.py` (output `sim/out_inter.txt`) draws 40 random fully adaptive trees on all nT qubits of T stored copies, for (n, T) = (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), and asserts the identity Σ_ℓ |⟨e_ℓ|p_s⟩||⟨e_ℓ|p_{s′}⟩| = q^{d(s,s′)}, the bound of Lemma 1 for every set A of copies and all patterns on A with ψ_n on the other copies, and the bounds (1 + q)^T − 1 and (1 + 2εq)^T − 1 on the summed leaf differences of Theorem 1, and (1 + sq)^T − 1 for ρ_s. `sim/stored2.py` (output `sim/out_stored2.txt`) draws 40 random fully adaptive trees on all nT qubits for (n, T) = (1, 1), …, (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2) and asserts the product form of P_{ρ_s}/P_{ρ_n} at every leaf and the bound χ²(P_{ρ_s} ‖ P_{ρ_n}) ≤ (1 + s²q)^T − 1 for s = 0.05, 0.2, 0.5, 1, with both laws computed from the density matrices; the largest ratio of the two sides is 0.8165. `sim/axes.py` (output `sim/out_axes.txt`) computes κ(S) by local minimization from 400 starting points, which gives an admissible r and hence a valid upper estimate of κ(S); it asserts κ = √(2/3) for X, Y, Z and κ = 1/√2 for X, Z, and finds 0.9428 for X, Y, Z with the four diagonals (±1, ±1, 1)/√3 and 0.9849 for the 13 axes through the faces, edges and corners of a cube. `sim/blocks.py` is a local numerical search over non-adaptive settings: it minimizes the largest coefficient Σ|⟨e|A⟩||⟨e|A′⟩| over orthogonal pairs of k-qubit states A, A′ for k = 1, 2, 3; per qubit it finds √(2/3) each time, the value of the pair a, ā.

## Scope

- Theorems 1 and 2 concern single-qubit measurements along X, Y and Z, and Corollary 3 along any fixed finite set of axes. Measurements with axes from an infinite set, joint measurements of several qubits, and measurements on several copies at once are not covered; with other single-qubit axes, polynomially many copies suffice [2].
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
