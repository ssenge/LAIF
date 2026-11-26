# Constants in the sample complexity of wave matrix Lindbladization

2026-11-26

Wave matrix Lindbladization (WML) simulates the Lindbladian with one jump operator L on a d-dimensional system from copies of a program state that encodes L [1]. Each copy drives one step of time Δ = t/n. The number of copies is set by the leading constant of the one-step error, in the normalized diamond distance and with ‖L‖₂ = 1. This folder pins down that constant up to an additive constant.

| Quantity | Previous bound | Here |
|---|---|---|
| One-step error of WML, leading constant, worst case over L | at most (2d+3)/8 · ‖L‖∞² [1, Lemma 4] | between (2d−3)/4 and d/2 + 1 (Theorems 1 and 2) |
| Copies needed by WML for time t and error ε, ‖L‖∞ ≤ 1 | at most (2d+3)/8 · t²/ε [1, Theorem 3] | at most (d/2 + e^{1/d}) t²/ε for n > 2dt (Theorem 2) |
| Copies needed by WML in the worst case over L, as ε → 0 | at least d/32 · t²/ε [1, Theorem 10] | at least (d−1)/4 · t²/ε for every t, and (2d−3)/4 · t²/ε as t → 0 (Theorem 3) |
| Copies needed by any regular memoryless protocol with a bounded number of fresh copies per step and comparable step sizes, as n → ∞ | at least 10⁻⁴ · t²/ε, for every protocol [2] | at least (d−1)/4 · t²/ε, with the same constant as WML on the witness L = \|0⟩⟨0\| (Theorem 4) |
| One-copy error of any channel from S ⊗ P to S, worst case over L, as t → 0 | | at least (d−1)/4 · t² − O(t³) (Theorem 5) |

The first three rows are about the WML protocol, as in [1, Theorem 10]. The fourth row covers the class of Theorem 4, and the last row every channel that uses one copy. None of them bounds the minimum over all protocols, for which the lower bound 10⁻⁴ · t²/ε of [2] holds for every d.

## Setting

One WML step applies exp(ΔM) to ρ ⊗ π_L and traces out the program, where M is the fixed Lindbladian of [1, Eqs. (14), (15)] and π_L = |L⟩⟨L| with |L⟩ = (L ⊗ I)|Γ⟩. By the transfer matrix of [1, App. B], the step is

Φ_Δ = id + Δ ℒ + c_J(Δ) J + c_A(Δ) A + c_D(Δ) D₁∘J,

with J = L · L†, A = {L†L, ·}/2, ℒ = J − A, and D₁ = (I/d) Tr. The coefficients have the closed forms

- c_A = (2/d) u² φ(u),
- c_D = (d u²/(d²−2)) [4(d²−1) φ(v)/d² − 2φ(u)],
- c_J = −Δ² (d²−1) φ(v)/d − 2c_D/d²,

where u = Δd/2, v = Δ(d − 1/d) and φ(z) = (e^{−z} − 1 + z)/z². Their leading terms are c_J ≈ −dΔ²/2 and c_A ≈ c_D ≈ dΔ²/4.

## Results

**Theorem 1 (a jump operator with a large error).** Let L = |0⟩⟨1|, so ‖L‖₂ = ‖L‖∞ = 1, and take the input state |1⟩⟨1|. Then the one-step error of WML is Δ² (2d−3)/4 + O(Δ³).

- For d ≥ 5 and small Δ this exceeds Δ² (2d+3)/8. The excess is 7% at d = 5 and grows towards a factor 2 as d grows.
- The n-step error exceeds (2d+3) t²/(8n) for small t and n > 2dt. At t = 0.02 the ratio is 1.06 (d = 5), 1.18 (d = 6), 1.35 (d = 8) and 1.53 (d = 12).
- Full-rank perturbations of L give the same picture.

This hints at a possible gap in [1, Eq. (40)]. To leading order, L̃ − L = (Δd/4) A − (Δd/2) J, whose diamond norm for this L is 3Δd/4 rather than Δd/4. Eq. (41), which follows from Eq. (40), fails for every d ≥ 2: ‖Φ_Δ − id − Δℒ‖⋄/Δ² tends to (2d−1)/2 rather than d/2.

The tail estimate in [1, Eq. (36)] reads (3/4)Δ²‖L‖∞². With x = 2Δ‖L‖∞², the bound e^x − x − 1 ≤ (3/4)x² gives 3Δ²‖L‖∞⁴. The scaling O(d t²/ε) of [1] is not affected; only the constants change.

**Theorem 2 (corrected bound).** For every L with ‖L‖₂ = 1, every d ≥ 2 and every Δ ≤ 1/(2d),

½ ‖e^{Δℒ} − Φ_Δ‖⋄ ≤ Δ² ‖L‖∞² (d/2 + e^{1/d} ‖L‖∞²).

*Proof.*
- **Coefficients.** φ is decreasing with values in (0, 1/2], and v ≥ u. This gives 0 < c_A ≤ dΔ²/4 and 0 < c_D ≤ dΔ²/4, using φ(v) ≥ φ(1/2) > 1/3 for the sign. Both parts of c_J are negative, so |c_J| ≤ dΔ²/2.
- **Maps.** J and D₁∘J are completely positive with adjoint value L†L at the identity, and A is bounded by ‖L†L‖. So each has diamond norm at most ‖L‖∞², and ‖ℒ‖⋄ ≤ 2‖L‖∞².
- **Tail.** The exponential series gives ‖e^{Δℒ} − id − Δℒ‖⋄ ≤ e^x − 1 − x ≤ x² e^x/2, with x = 2Δ‖L‖∞² ≤ 1/d.

Summing these over n steps, the error after n > 2dt steps is at most (d/2 + e^{1/d}‖L‖∞²) ‖L‖∞² t²/n. So n ≥ max(2dt, (d/2 + e^{1/d}) t²/ε) copies suffice for ‖L‖∞ ≤ 1. Together with Theorem 1, the worst-case leading constant lies between d/2 − 3/4 and d/2 + 1.

**Theorem 3 (lower bound for WML).** For L = |0⟩⟨0|, the witness of [1, Theorem 10], with input |0⟩⟨0|:

- the input is fixed by e^{tℒ};
- each step leaks Δ² (d−1)/4 in trace distance, at leading order;
- these errors add up without decay.

Hence n · error/t² tends to (d−1)/4 as n → ∞, for every t. For L = |0⟩⟨1| the same limit tends to (2d−3)/4 as t → 0. The number of copies WML needs in the worst case over L is therefore at least (max{(d−1)/4, c(t)} − o(1)) t²/ε as ε → 0, where c(t) is the limit for L = |0⟩⟨1|. This is at least 8(d−1)/d ≥ 4 times the constant d/32 of [1, Theorem 10], for every t.

**Theorem 4 (lower bound for regular protocols with fresh copies in each step).** Consider protocols that are sequential and memoryless and use fresh copies of the program state in each step: step j uses k_j ≤ k_max copies and applies a channel Λ⁽ʲ⁾_{Δ_j} from S ⊗ P^{⊗k_j} to S, with Δ₁ + … + Δ_m = t and n = k₁ + … + k_m copies in all. Each family Λ_Δ is assumed to

- (H) agree with the target to first order: Λ_Δ(ρ ⊗ π_L^{⊗k}) = ρ + Δℒ_L(ρ) + O(Δ²) for all ρ and L;
- (R) be regular: Λ_Δ = Tr_P + ΔG + Δ²E + R_Δ with ‖E‖⋄ ≤ K and ‖R_Δ‖⋄ ≤ KΔ³ for Δ ≤ Δ₀, with one constant K for all steps;
- (S) use comparable step sizes: Δ_j ≤ c·k_j·t/n for a fixed constant c ≥ 1, as WML does with k_j = 1 and c = 1.

Let ε be the error on L = |0⟩⟨0| with input |0⟩⟨0|, in normalized trace distance; it is at most the worst-case diamond error. Then ε ≥ (d−1)/4 · S · (1 − O(√(t·max_j Δ_j) + max_j Δ_j)) for max_j Δ_j ≤ Δ₀, with S = Δ₁²/k₁ + … + Δ_m²/k_m ≥ t²/n, the constants depending on K, k_max and d. Hence n·ε ≥ ((d−1)/4 − o(1)) t² as n → ∞, for every fixed t: along protocols whose number of copies grows, error ε needs at least ((d−1)/4 − o(1)) t²/ε copies. Several copies per step do not lower the constant per copy. WML, with one copy per step, belongs to the class and its error on this witness is (d−1)/4 · t²/n to leading order (Theorem 3), so the constant cannot be raised for this witness.

*Proof sketch.*
1. **The map G is forced where it matters.** By (R), Λ₀ = Tr_P; on symmetric programs linearity alone forces this. The operators |v⟩⟨v|^{⊗k} with unit v span all operators on the symmetric subspace Sym^k(P), so (H) fixes G on L(S) ⊗ L(Sym^k(P)). There it equals the average over the copies of the one-copy map ρ ⊗ |L⟩⟨L′| ↦ Lρ L′† − ½(L′†L ρ + ρ L′†L), with the trace on the other copies. The Choi matrix of Tr_P is C₀ = |Γ⟩⟨Γ| ⊗ I.
2. **Positivity bounds E.** The Choi matrix of Λ_Δ is positive for Δ ∈ [0, Δ₀). For a vector e with C₀e = 0 and e†C₁e = 0, positivity at first order puts C₁e in the range of C₀. Testing with e + Δf, f = −C₀⁺C₁e, gives e†C₂e ≥ e†C₁C₀⁺C₁e, where C₂ is the Choi matrix of E. The right-hand side is at least its part on Sym^k(P), which step 1 fixes.
3. **The forced leak.** For L = |0⟩⟨0| and the vector e_i = |0⟩|L⟩^{⊗k} ⊗ |i⟩, i ≠ 0, the symmetric part equals 1/(4k). So a step with k copies moves at least (d−1)Δ²/(4k) out of |0⟩ at second order. Running k steps of WML with time Δ/k each attains this.
4. **Accumulation.** The exact evolution keeps |0⟩⟨0| fixed. Population that has left |0⟩ returns only at order Δ², because ⟨0|X|0⟩ = 0 and ⟨0|ℒ_L(X)|0⟩ = 0 for the part X of the state outside |0⟩⟨0|. The coherences between |0⟩ and its complement are at most the square root of the population outside |0⟩, so the return in step j is O(KΔ_j²(p + √p)) for an outside population p. Summing over the steps gives the bound on ε. By the Cauchy-Schwarz inequality, S ≥ (Δ₁ + … + Δ_m)²/(k₁ + … + k_m) = t²/n, and under (S), max_j Δ_j ≤ c·k_max·t/n tends to 0 as n grows. ∎

Protocols with memory across steps, steps far from Tr_P, or step sizes that do not shrink with n are outside the class. The bound is asymptotic in n: rescaling WML to Λ_Δ = Φ_{Δ(1−Δ/Δ₀)} with Δ₀ = t/n satisfies (H), (R) and (S), and every step of size Δ₀ is then Tr_P, which has zero error on this witness for that n.

**Theorem 5 (every channel that uses one copy).** For every d ≥ 2 there is a constant K_d such that every channel Λ from S ⊗ P to S and every t ∈ (0, 1] satisfy

sup_L ½ ‖Λ(· ⊗ π_L) − e^{tℒ_L}‖⋄ ≥ (d−1)/4 · t² − K_d t³,

with the supremum over all L with ‖L‖₂ = 1. No step structure, expansion or regularity in t is assumed. The supremum may be restricted to finitely many operators: L = |0⟩⟨0| together with any finite set whose program states span all operators on P.

*Proof.* Let ε be the supremum, A = Λ − Tr_P and G the forced map of Theorem 4, step 1, and set B = A − tG.
1. **B is small on every input.** For every L, B(ρ ⊗ π_L) = (e^{tℒ_L} − id − tℒ_L)(ρ) + (Λ(ρ ⊗ π_L) − e^{tℒ_L}(ρ)). Since ‖ℒ_L‖⋄ ≤ 2, this has diamond norm at most 2e²t² + 2ε. Fix finitely many L_k whose π_{L_k} span the operators on P. Every matrix unit of S ⊗ P is then a fixed combination of products Y ⊗ π_{L_k}, so every entry of the Choi matrix C_B of B is at most κ_d (t² + ε).
2. **Positivity.** The Choi matrix of Λ is C₀ + tC₁ + C_B ≥ 0, with C₀ and C₁ as in Theorem 4. For L = |0⟩⟨0| and e_i = |0⟩|L⟩ ⊗ |i⟩, i ≠ 0, test it with e_i + tf, f = −C₀⁺C₁e_i. The terms of order t² give −t²/4, as in Theorem 4. The terms that involve C_B give e_i†C_B e_i plus at most κ′_d t(t² + ε). The term t³ f†C₁f is O(t³). Hence e_i†C_B e_i ≥ t²/4 − κ″_d t(t² + ε).
3. **The witness.** For L = |0⟩⟨0|, ℒ_L(|0⟩⟨0|) = 0, so e^{tℒ_L} fixes |0⟩⟨0| and e_i†C_B e_i = ⟨i|Λ(|0⟩⟨0| ⊗ π_L)|i⟩. Summed over i ≠ 0 this is the population that leaves |0⟩, which is at most the trace distance to |0⟩⟨0|, hence at most ε.
4. **Conclusion.** Together, ε ≥ (d−1)t²/4 − (d−1)κ″_d t(t² + ε). If ε > (d−1)t²/4 there is nothing to prove; otherwise ε ≤ dt², and the claim follows with K_d = 2d(d−1)κ″_d. ∎

So even an unrestricted channel that uses one copy has the leading constant (d−1)/4. The optimal one-copy channel, computed by an exact semidefinite program over all channels, approaches this constant: over the operators of step 1 its error divided by t² is 0.2374, 0.2437 and 0.2470 for t = 0.04, 0.02 and 0.01 at d = 2, and 0.4667, 0.4834 and 0.4924 at d = 3.

**Numerical supremum.** The supremum of the leading constant over all L, computed with an exact semidefinite program for the diamond norm and local search over L, is about 0.300 at d = 2 and 0.750 at d = 3. At d = 3 this equals (2d−3)/4.

## Scope

- Theorems 1 and 3 are exact statements about explicit operators, checked numerically with plain-state certificates and with diamond norms from a semidefinite program.
- Theorems 2, 4 and 5 are written proofs (Claim). The constant K_d of Theorem 5 is not made explicit. Every coefficient identity of Theorem 2 is checked against the matrix exponential to 1e-12, and the Schur-complement value of Theorem 4 is checked exactly for d = 2, 3, 4 with one copy per step and for (d, k) = (2, 2), (3, 2), (4, 2), (2, 3), (3, 3).
- The step of WML is built twice: from the transfer matrix of [1, App. B], and directly from [1, Eq. (15)] on the full system and program space. The two agree to 1e-16 for d = 2, 3.
- The supremum over L for d ≥ 4 is not computed. Nothing here bounds the sample complexity over all protocols.

## Files

- `sim/wml.py`: the WML step from the transfer matrix and from the definition, the leading error map, and the diamond-norm semidefinite program.
- `sim/check_gap.py`, `sim/nstep.py`: Theorem 1, one step and n steps, with asserts (`check_gap.py --brute` adds the step from the definition at d = 5, about 8 GB).
- `sim/check_bound.py`: Theorem 2 against exact diamond norms on random and structured L.
- `sim/projector.py`: Theorem 3.
- `sim/class_bound.py`: the forced leak of Theorem 4 with one copy per step, from the full Choi matrices, with asserts for d = 2, 3, 4.
- `sim/kcopies.py`: the forced leak with k copies per step, (d−1)/(4k), and its attainment by k WML steps, with asserts for (d, k) up to (4, 2) and (3, 3).
- `sim/scan.py`, `sim/supL.py`: rank-one scan and the numerical supremum over L.
- `sim/opt.py`, `sim/opt2.py`: the optimal channel with n copies over all channels, as an exact semidefinite program on covariant Choi matrices (partially transposed permutation operators, block-diagonalized for n = 2); `sim/check_conv.py` checks its conventions against the full WML channel; `sim/frame_check.py` gives the numbers after Theorem 5.

## References

1. S. Park, Y. Seo, B. Go, D. Patel, M. M. Wilde, H. Kwon. Improved sample complexity bound for sample-based Lindbladian simulation. arXiv:2605.30301 (2026).
2. B. Go, H. Kwon, S. Park, D. Patel, M. M. Wilde. Sample-based Hamiltonian and Lindbladian simulation: non-asymptotic analysis of sample complexity. arXiv:2412.02134.

## Use of AI

The constructions, checks and text were produced with Claude Opus 5.5.
