# Constants in the sample complexity of wave matrix Lindbladization

2026-11-26

Wave matrix Lindbladization (WML) simulates the Lindbladian with one jump operator L on a d-dimensional system from copies of a program state that encodes L [1]. Each copy drives one step of time Δ = t/n. The number of copies is set by the leading constant of the one-step error, in the normalized diamond distance and with ‖L‖₂ = 1. This folder pins down that constant up to an additive constant.

| Quantity | Previous bound | Here |
|---|---|---|
| One-step error of WML, leading constant, worst case over L | at most (2d+3)/8 · ‖L‖∞² [1, Lemma 4] | between (2d−3)/4 and d/2 + 1 (Theorems 1 and 2) |
| Copies needed by WML for time t and error ε, ‖L‖∞ ≤ 1 | at most (2d+3)/8 · t²/ε [1, Theorem 3] | at most (d/2 + e^{1/d}) t²/ε for n > 2dt (Theorem 2) |
| Copies needed by WML in the worst case over L, as ε → 0 | at least d/32 · t²/ε [1, Theorem 10] | at least (d−1)/4 · t²/ε for every t, and (2d−3)/4 · t²/ε as t → 0 (Theorem 3) |

All three statements are about the WML protocol, as in [1, Theorem 10]. They say nothing about the minimum over all protocols.

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

**Numerical supremum.** The supremum of the leading constant over all L, computed with an exact semidefinite program for the diamond norm and local search over L, is about 0.300 at d = 2 and 0.750 at d = 3. At d = 3 this equals (2d−3)/4.

## Scope

- Theorems 1 and 3 are exact statements about explicit operators, checked numerically with plain-state certificates and with diamond norms from a semidefinite program.
- Theorem 2 is a written proof (Claim); every coefficient identity is checked against the matrix exponential to 1e-12.
- The step of WML is built twice: from the transfer matrix of [1, App. B], and directly from [1, Eq. (15)] on the full system and program space. The two agree to 1e-16 for d = 2, 3.
- The supremum over L for d ≥ 4 is not computed. Nothing here bounds the sample complexity over all protocols.

## Files

- `sim/wml.py`: the WML step from the transfer matrix and from the definition, the leading error map, and the diamond-norm semidefinite program.
- `sim/check_gap.py`, `sim/nstep.py`: Theorem 1, one step and n steps, with asserts (`check_gap.py --brute` adds the step from the definition at d = 5, about 8 GB).
- `sim/check_bound.py`: Theorem 2 against exact diamond norms on random and structured L.
- `sim/projector.py`: Theorem 3.
- `sim/scan.py`, `sim/supL.py`: rank-one scan and the numerical supremum over L.

## References

1. S. Park, Y. Seo, B. Go, D. Patel, M. M. Wilde, H. Kwon. Improved sample complexity bound for sample-based Lindbladian simulation. arXiv:2605.30301 (2026).

## Use of AI

The constructions, checks and text were produced with Claude Opus 5.5.
