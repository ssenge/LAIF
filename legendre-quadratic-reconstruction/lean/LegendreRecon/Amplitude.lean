import Mathlib

/-!
# The binomial step: exact success probability

Let `F` be a finite field with `q` elements, `χ` a nontrivial multiplicative character and `ψ` a primitive
additive character. Starting from a state with amplitudes `φ(y) = w(y) χ(y - D)`, the algorithm applies the
Fourier transform `|y⟩ ↦ q^{-1/2} Σ_k ψ(k y) |k⟩`, multiplies by `χ(k)`, applies the inverse transform
`|k⟩ ↦ q^{-1/2} Σ_z ψ(-k z) |z⟩` and measures. The amplitude of the outcome `D` is `q⁻¹` times

  `Σ_k χ(k) ψ(-k D) Σ_y φ(y) ψ(k y) = g(χ, ψ) Σ_{y ≠ D} w(y)`,

where `g` is the Gauss sum. For `w` the indicator of a set `H` this gives the success probability
`|H \ {D}| / q`, with no character sum estimate.
-/

open Finset

namespace LegendreRecon

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `Σ_k χ(k) ψ(k a) = χ⁻¹(a) g(χ, ψ)` for every `a`, including `a = 0`. -/
theorem sum_char_mul_add (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (a : F) :
    ∑ k, χ k * ψ (k * a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst ha
    simp [MulChar.sum_eq_zero_of_ne_one hχ, MulChar.map_zero]
  · have h := gaussSum_mulShift_eq χ ψ (Units.mk0 a ha)
    simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at h
    rw [show gaussSum χ ψ = ∑ a, χ a * ψ a from rfl, ← h]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm k a]

/-- The amplitude identity of the binomial step. -/
theorem amplitude (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (w : F → ℂ) (D : F) :
    ∑ k, χ k * ψ (-(k * D)) * ∑ y, w y * χ (y - D) * ψ (k * y) =
      gaussSum χ ψ * ∑ y ∈ univ.filter (· ≠ D), w y := by
  calc _ = ∑ y, w y * χ (y - D) * ∑ k, χ k * ψ (k * (y - D)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => ?_
        rw [show k * (y - D) = k * y + -(k * D) by ring, AddChar.map_add_eq_mul]
        ring
    _ = ∑ y, w y * (χ (y - D) * χ⁻¹ (y - D)) * gaussSum χ ψ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [sum_char_mul_add χ hχ ψ]
        ring
    _ = _ := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : y = D
        · simp [h, MulChar.map_zero]
        · have hu : χ (y - D) * χ⁻¹ (y - D) = 1 := by
            rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr h), map_one]
          rw [hu, ite_eq_left_iff.mpr (fun h' => absurd h h')]
          ring

omit [DecidableEq F] in
/-- `|g(χ, ψ)|² = q` for nontrivial `χ` and primitive `ψ`. -/
theorem normSq_gaussSum (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    Complex.normSq (gaussSum χ ψ) = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have h2 : ((Complex.normSq (gaussSum χ ψ) : ℝ) : ℂ) = ((Fintype.card F : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    simpa using h
  exact_mod_cast h2

omit [DecidableEq F] in
/-- Character values at nonzero points have modulus one. -/
theorem normSq_char (χ : MulChar F ℂ) {u : F} (hu : u ≠ 0) : Complex.normSq (χ u) = 1 := by
  have h : χ u * star (χ u) = 1 := by
    rw [MulChar.star_apply', MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hu, map_one]
  have h2 : ((Complex.normSq (χ u) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    simpa using h
  exact_mod_cast h2

/-- The squared norm of the start state `y ↦ 1_H(y) χ(y - D)` is `|H \ {D}|`. -/
theorem normSq_state (χ : MulChar F ℂ) (H : Finset F) (D : F) :
    ∑ y, Complex.normSq ((if y ∈ H then 1 else 0) * χ (y - D)) = ((H.filter (· ≠ D)).card : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ H)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    by_cases h : y = D
    · simp [h, MulChar.map_zero]
    · simp [hy, h, normSq_char χ (sub_ne_zero.mpr h)]
  · intro y _ hy
    simp [hy]

/-- Success probability of the binomial step: with start state `1_H(y) χ(y - D)` (normalized), the outcome
`D` has probability `|H \ {D}| / q`. -/
theorem success_probability (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (H : Finset F) (D : F) (hN : 0 < (H.filter (· ≠ D)).card) :
    Complex.normSq ((Fintype.card F : ℂ)⁻¹ *
        ∑ k, χ k * ψ (-(k * D)) * ∑ y, (if y ∈ H then 1 else 0) * χ (y - D) * ψ (k * y)) /
      ∑ y, Complex.normSq ((if y ∈ H then 1 else 0) * χ (y - D)) =
      ((H.filter (· ≠ D)).card : ℝ) / Fintype.card F := by
  rw [amplitude χ hχ ψ, normSq_state χ H D]
  have hs : ∑ y ∈ univ.filter (· ≠ D), (if y ∈ H then (1 : ℂ) else 0) = ((H.filter (· ≠ D)).card : ℂ) := by
    rw [Finset.sum_ite_mem, Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    congr 1
    ext y
    simp [and_comm]
  rw [hs, Complex.normSq_mul, Complex.normSq_mul, normSq_gaussSum χ hχ ψ hψ, Complex.normSq_inv,
    Complex.normSq_natCast, Complex.normSq_natCast]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hN' : (0 : ℝ) < (H.filter (· ≠ D)).card := by exact_mod_cast hN
  field_simp

end LegendreRecon
