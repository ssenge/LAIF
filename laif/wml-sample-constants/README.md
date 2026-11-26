# Constants in the sample complexity of wave matrix Lindbladization

2026-11-26

Wave matrix Lindbladization (WML) simulates the Lindbladian with one jump operator L on a d-dimensional system from copies of a program state that encodes L [1]. Each copy drives one step of time Δ = t/n. The number of copies is set by the leading constant of the one-step error, in the normalized diamond distance and with ‖L‖₂ = 1. This folder pins down that constant up to an additive constant.

| Quantity | Previous bound | Here |
|---|---|---|
| One-step error of WML, leading constant, worst case over L | at most (2d+3)/8 · ‖L‖∞² [1, Lemma 4] | between (2d−3)/4 and d/2 + 1 (Theorems 1 and 2) |
| Copies needed by WML for time t and error ε, ‖L‖∞ ≤ 1 | at most (2d+3)/8 · t²/ε [1, Theorem 3] | at most (d/2 + e^{1/d}) t²/ε for n > 2dt (Theorem 2) |
| Copies needed by WML in the worst case over L, as ε → 0 | at least d/32 · t²/ε [1, Theorem 10] | at least (d−1)/4 · t²/ε for every t, and (2d−3)/4 · t²/ε as t → 0 (Theorem 3) |
| Copies needed by any regular protocol with one fresh copy per step and comparable step sizes, as ε → 0 | at least 10⁻⁴ · t²/ε, for every protocol [2] | at least (d−1)/4 · t²/ε, with the same constant as WML on the witness L = \|0⟩⟨0\| (Theorem 4) |

The first three rows are about the WML protocol, as in [1, Theorem 10]. The last row covers the class of Theorem 4. None of them bounds the minimum over all protocols, for which the lower bound 10⁻⁴ · t²/ε of [2] holds for every d.

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

**Theorem 4 (lower bound for regular one-copy protocols).** Consider protocols that are sequential and memoryless and use one fresh copy of the program state per step: step k applies a channel Λ⁽ᵏ⁾_{Δ_k} from S ⊗ P to S, with Δ₁ + … + Δ_n = t. Each family Λ_Δ is assumed to

- (H) agree with the target to first order: Λ_Δ(ρ ⊗ π_L) = ρ + Δℒ_L(ρ) + O(Δ²) for all ρ and L;
- (R) be regular: Λ_Δ = Tr_P + ΔG + Δ²E + R_Δ with ‖E‖⋄ ≤ K and ‖R_Δ‖⋄ ≤ KΔ³ for Δ ≤ Δ₀, with one constant K for all steps;
- (S) use comparable step sizes: Δ_k ≤ c·t/n for a fixed constant c ≥ 1, as WML does with c = 1.

Let ε be the error on L = |0⟩⟨0| with input |0⟩⟨0|, in normalized trace distance; it is at most the worst-case diamond error. Then ε ≥ (d−1)/4 · S · (1 − O(√S + max_k Δ_k)) with S = Δ₁² + … + Δ_n² ≥ t²/n, the constants depending on K, c and d. Hence every such protocol needs at least ((d−1)/4 − o(1)) t²/ε copies as ε → 0, for every fixed t. WML belongs to the class and its error on this witness is (d−1)/4 · t²/n to leading order (Theorem 3), so the constant cannot be raised for this witness.

*Proof sketch.*
1. **The map G is forced.** By linearity, Λ₀ = Tr_P, and (H) fixes G: it is the linear extension of ρ ⊗ |L⟩⟨L′| ↦ Lρ L′† − ½(L′†L ρ + ρ L′†L). Hence every family has the same Choi matrix C₁ of G. The Choi matrix of Tr_P is C₀ = d P_Γ ⊗ I_P.
2. **Positivity bounds E.** The Choi matrix of Λ_Δ is positive for Δ ∈ [0, Δ₀). For a vector e with C₀e = 0 and C₁e in the range of C₀, test it with e + Δf, f = −C₀⁺C₁e. This gives e†C₂e ≥ e†C₁C₀⁺C₁e, where C₂ is the Choi matrix of E.
3. **The forced leak.** For L = |0⟩⟨0| and the vector e_i = |0⟩|L⟩ ⊗ |i⟩, i ≠ 0, the right-hand side equals 1/4. So ⟨i|E(|0⟩⟨0| ⊗ π_L)|i⟩ ≥ 1/4 for each of the d − 1 states |i⟩ ≠ |0⟩.
4. **Accumulation.** The exact evolution keeps |0⟩⟨0| fixed. Population that has left |0⟩ returns only at order Δ², because ⟨0|X|0⟩ = 0 and ⟨0|ℒ_L(X)|0⟩ = 0 for the part X of the state outside |0⟩⟨0|. The coherences between |0⟩ and its complement are at most the square root of the population outside |0⟩, so the return per step is O(KΔ_k²(p + √p)) for an outside population p. Summing over the steps, the error is at least (d−1)/4 · S · (1 − O(√S + max_k Δ_k)). Under (S), S ≤ c²t²/n and max_k Δ_k ≤ ct/n both tend to 0 as n grows. ∎

Protocols with memory across steps, several copies per step, steps far from Tr_P, or step sizes that do not shrink with n are outside the class. Without (S) the bound fails: rescaling WML to Λ_Δ = Φ_{Δ(1−Δ/Δ₀)} satisfies (H) and (R), and with steps of size exactly Δ₀ every step is Tr_P, which has zero error on this witness.

**Numerical supremum.** The supremum of the leading constant over all L, computed with an exact semidefinite program for the diamond norm and local search over L, is about 0.300 at d = 2 and 0.750 at d = 3. At d = 3 this equals (2d−3)/4.

## Scope

- Theorems 1 and 3 are exact statements about explicit operators, checked numerically with plain-state certificates and with diamond norms from a semidefinite program.
- Theorems 2 and 4 are written proofs (Claim). Every coefficient identity of Theorem 2 is checked against the matrix exponential to 1e-12, and the Schur-complement value of Theorem 4 is checked exactly for d = 2, 3, 4.
- The step of WML is built twice: from the transfer matrix of [1, App. B], and directly from [1, Eq. (15)] on the full system and program space. The two agree to 1e-16 for d = 2, 3.
- The supremum over L for d ≥ 4 is not computed. Nothing here bounds the sample complexity over all protocols.

## Files

- `sim/wml.py`: the WML step from the transfer matrix and from the definition, the leading error map, and the diamond-norm semidefinite program.
- `sim/check_gap.py`, `sim/nstep.py`: Theorem 1, one step and n steps, with asserts (`check_gap.py --brute` adds the step from the definition at d = 5, about 8 GB).
- `sim/check_bound.py`: Theorem 2 against exact diamond norms on random and structured L.
- `sim/projector.py`: Theorem 3.
- `sim/class_bound.py`: the forced leak of Theorem 4, with asserts for d = 2, 3, 4.
- `sim/scan.py`, `sim/supL.py`: rank-one scan and the numerical supremum over L.

## References

1. S. Park, Y. Seo, B. Go, D. Patel, M. M. Wilde, H. Kwon. Improved sample complexity bound for sample-based Lindbladian simulation. arXiv:2605.30301 (2026).
2. B. Go, H. Kwon, S. Park, D. Patel, M. M. Wilde. Sample-based Hamiltonian and Lindbladian simulation: non-asymptotic analysis of sample complexity. arXiv:2412.02134.

## Use of AI

The constructions, checks and text were produced with Claude Opus 5.5.
