import Mathlib

/-!
# Parameter arithmetic for long-block simulation of geometrically local Hamiltonians

Unit model constants. A block of side `ℓ` in dimension `D` evolves for time `t` with `r` product-formula steps of
order `p`, and control records of width `w` are scaled by a constant `c`; write `a = c * w`. The step count is
  r = t ^ ((p + 1) / p) * ℓ ^ (D / p),
and the step time is the largest one allowed by the size condition `a * r ≤ ℓ`:
  t = ℓ ^ ((p - D) / (p + 1)) * a ^ (-(p / (p + 1))).
Then:

* `size_identity`: a * r = ℓ;
* `coeff_identity`: r ^ p = t ^ (p + 1) * ℓ ^ D, so the coefficient ratio ℓ ^ D * t ^ (p + 1) / r ^ p equals one;
* `depth_per_time`: ℓ / t = ℓ ^ δ * a ^ (p / (p + 1)) with δ = (D + 1) / (p + 1);
* `delta_lt_one`, `delta_pos`: 0 < δ < 1 whenever 0 ≤ D < p;
* `depth_sum`: ⌈T / t⌉ steps of depth ℓ take at most T * (ℓ / t) + ℓ;
* `example_instance`: p = 4, D = 1, a = 1 and ℓ = 32 give t = 8 and r = 32, so steps of length 1/4.
-/

namespace LongBlock

open Real

/-- The step time allowed by the size condition. -/
noncomputable def stepTime (p D a ℓ : ℝ) : ℝ := ℓ ^ ((p - D) / (p + 1)) * a ^ (-(p / (p + 1)))

/-- The number of product-formula steps of a block of side `ℓ` and time `t`. -/
noncomputable def steps (p D t ℓ : ℝ) : ℝ := t ^ ((p + 1) / p) * ℓ ^ (D / p)

/-- The exponent of the depth per unit time. -/
noncomputable def delta (p D : ℝ) : ℝ := (D + 1) / (p + 1)

lemma stepTime_pos {p D a ℓ : ℝ} (ha : 0 < a) (hl : 0 < ℓ) : 0 < stepTime p D a ℓ := by
  unfold stepTime; positivity

/-- Size condition: `a * r = ℓ` at the step time `stepTime`. -/
theorem size_identity {p D a ℓ : ℝ} (hp : 0 < p) (ha : 0 < a) (hl : 0 < ℓ) :
    a * steps p D (stepTime p D a ℓ) ℓ = ℓ := by
  have hp0 : p ≠ 0 := hp.ne'
  have hp1 : p + 1 ≠ 0 := by linarith
  unfold steps stepTime
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hl.le, ← Real.rpow_mul ha.le]
  have e1 : (p - D) / (p + 1) * ((p + 1) / p) = (p - D) / p := by field_simp
  have e2 : -(p / (p + 1)) * ((p + 1) / p) = -1 := by field_simp
  have e3 : (p - D) / p + D / p = 1 := by field_simp; ring
  rw [e1, e2, Real.rpow_neg_one]
  calc a * (ℓ ^ ((p - D) / p) * a⁻¹ * ℓ ^ (D / p)) = ℓ ^ ((p - D) / p) * ℓ ^ (D / p) := by
        field_simp
    _ = ℓ := by rw [← Real.rpow_add hl, e3, Real.rpow_one]

/-- Coefficient condition: `r ^ p = t ^ (p + 1) * ℓ ^ D` for every step time `t > 0` and side `ℓ ≥ 0`. -/
theorem coeff_identity {p D t ℓ : ℝ} (hp : 0 < p) (ht : 0 < t) (hl : 0 ≤ ℓ) :
    steps p D t ℓ ^ p = t ^ (p + 1) * ℓ ^ D := by
  unfold steps
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ht.le, ← Real.rpow_mul hl]
  have hp0 : p ≠ 0 := hp.ne'
  rw [div_mul_cancel₀ _ hp0, div_mul_cancel₀ _ hp0]

/-- Depth per unit time: `ℓ / t = ℓ ^ δ * a ^ (p / (p + 1))`. -/
theorem depth_per_time {p D a ℓ : ℝ} (hp : 0 < p) (ha : 0 < a) (hl : 0 < ℓ) :
    ℓ / stepTime p D a ℓ = ℓ ^ delta p D * a ^ (p / (p + 1)) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  unfold stepTime delta
  have e : (1 : ℝ) = (p - D) / (p + 1) + (D + 1) / (p + 1) := by field_simp; ring
  have hl1 : ℓ = ℓ ^ ((p - D) / (p + 1)) * ℓ ^ ((D + 1) / (p + 1)) := by
    rw [← Real.rpow_add hl, ← e, Real.rpow_one]
  rw [Real.rpow_neg ha.le]
  have h1 : 0 < ℓ ^ ((p - D) / (p + 1)) := by positivity
  have h2 : 0 < a ^ (p / (p + 1)) := by positivity
  nth_rewrite 1 [hl1]
  field_simp

/-- The exponent is below one whenever `D < p`. -/
theorem delta_lt_one {p D : ℝ} (hp : D < p) (hD : 0 ≤ D) : delta p D < 1 := by
  unfold delta; rw [div_lt_one (by linarith)]; linarith

/-- The exponent is positive. -/
theorem delta_pos {p D : ℝ} (hD : 0 ≤ D) (hp : D < p) : 0 < delta p D := by
  unfold delta; apply div_pos <;> linarith

/-- Depth sum: `⌈T / t⌉` steps of depth `ℓ` cost at most `T * (ℓ / t) + ℓ`. -/
theorem depth_sum {T t ℓ : ℝ} (hT : 0 ≤ T) (ht : 0 < t) (hl : 0 ≤ ℓ) :
    (⌈T / t⌉ : ℝ) * ℓ ≤ T * (ℓ / t) + ℓ := by
  have hc : (⌈T / t⌉ : ℝ) ≤ T / t + 1 := (Int.ceil_lt_add_one (T / t)).le
  have : (T / t + 1) * ℓ = T * (ℓ / t) + ℓ := by field_simp
  calc (⌈T / t⌉ : ℝ) * ℓ ≤ (T / t + 1) * ℓ := mul_le_mul_of_nonneg_right hc hl
    _ = T * (ℓ / t) + ℓ := this

lemma thirtytwo_rpow : (32 : ℝ) ^ ((4 - 1 : ℝ) / (4 + 1)) = 8 := by
  have h : (32 : ℝ) = 2 ^ (5 : ℝ) := by norm_num
  rw [h, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- Non-vacuity: for p = 4, D = 1, a = 1 and ℓ = 32 the step time is 8 and the step count is 32 (more steps than
time, so steps of length 1/4), the exponent is 2/5 < 1, and the coefficient ratio is one. -/
theorem example_instance :
    stepTime 4 1 1 32 = 8 ∧ steps 4 1 (stepTime 4 1 1 32) 32 = 32 ∧ stepTime 4 1 1 32 < 32 ∧
      delta 4 1 = 2 / 5 ∧
      steps 4 1 (stepTime 4 1 1 32) 32 ^ (4 : ℝ) = stepTime 4 1 1 32 ^ ((4 : ℝ) + 1) * (32 : ℝ) ^ (1 : ℝ) := by
  have ht : stepTime 4 1 1 32 = 8 := by
    unfold stepTime; rw [Real.one_rpow, mul_one]; exact thirtytwo_rpow
  have hr : steps 4 1 (stepTime 4 1 1 32) 32 = 32 := by
    have := size_identity (p := 4) (D := 1) (a := 1) (ℓ := 32) (by norm_num) (by norm_num) (by norm_num)
    rwa [one_mul] at this
  refine ⟨ht, hr, by rw [ht]; norm_num, by unfold delta; norm_num, ?_⟩
  exact coeff_identity (by norm_num) (by rw [ht]; norm_num) (by norm_num)

end LongBlock
