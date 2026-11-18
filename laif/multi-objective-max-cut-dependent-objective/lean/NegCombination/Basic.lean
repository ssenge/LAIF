import Mathlib

/-!
# A third objective that is a negative combination of the first two

Let every edge carry weights `w₁ e`, `w₂ e` and `w₃ e = -a * w₁ e - b * w₂ e` with `a, b > 0`, and let the
value of a cut be the sum of the weights of its cut edges, all three to be maximized. Then the value vector of
a cut lies on the plane `y₃ = -a y₁ - b y₂`, and no cut dominates another: weak dominance in all three
values forces equal values. So every distinct value vector is Pareto-optimal.
-/

namespace NegCombination

open Finset

/-- On the plane `y₃ = -a y₁ - b y₂` with `a, b > 0`, weak dominance in all three coordinates forces
equality. -/
theorem eq_of_weak_dom {a b x₁ x₂ y₁ y₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂) (h₃ : -a * x₁ - b * x₂ ≤ -a * y₁ - b * y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have e₁ : 0 ≤ a * (y₁ - x₁) := mul_nonneg ha.le (by linarith)
  have e₂ : 0 ≤ b * (y₂ - x₂) := mul_nonneg hb.le (by linarith)
  have s₁ : a * (y₁ - x₁) = 0 := by linarith
  have s₂ : b * (y₂ - x₂) = 0 := by linarith
  have t₁ := (mul_eq_zero.1 s₁).resolve_left ha.ne'
  have t₂ := (mul_eq_zero.1 s₂).resolve_left hb.ne'
  exact ⟨by linarith, by linarith⟩

variable {E : Type*}

/-- The value of an edge set under `w₃ = -a w₁ - b w₂` is `-a` times its `w₁` value minus `b` times its
`w₂` value. -/
theorem sum_neg_comb (w₁ w₂ : E → ℝ) (a b : ℝ) (s : Finset E) :
    ∑ e ∈ s, (-a * w₁ e - b * w₂ e) = -a * ∑ e ∈ s, w₁ e - b * ∑ e ∈ s, w₂ e := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **No domination.** For two edge sets `S` and `T` (the cut edges of two cuts), if `T` is at least as
good as `S` in all three values, the two value vectors are equal. -/
theorem no_domination (w₁ w₂ : E → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (S T : Finset E)
    (h₁ : ∑ e ∈ S, w₁ e ≤ ∑ e ∈ T, w₁ e) (h₂ : ∑ e ∈ S, w₂ e ≤ ∑ e ∈ T, w₂ e)
    (h₃ : ∑ e ∈ S, (-a * w₁ e - b * w₂ e) ≤ ∑ e ∈ T, (-a * w₁ e - b * w₂ e)) :
    ∑ e ∈ S, w₁ e = ∑ e ∈ T, w₁ e ∧ ∑ e ∈ S, w₂ e = ∑ e ∈ T, w₂ e := by
  rw [sum_neg_comb, sum_neg_comb] at h₃
  exact eq_of_weak_dom ha hb h₁ h₂ h₃

/-- The construction with `w₃ = -0.5 w₁ - 5 w₂`. -/
theorem no_domination_half_five (w₁ w₂ : E → ℝ) (S T : Finset E)
    (h₁ : ∑ e ∈ S, w₁ e ≤ ∑ e ∈ T, w₁ e) (h₂ : ∑ e ∈ S, w₂ e ≤ ∑ e ∈ T, w₂ e)
    (h₃ : ∑ e ∈ S, (-(1 / 2) * w₁ e - 5 * w₂ e) ≤ ∑ e ∈ T, (-(1 / 2) * w₁ e - 5 * w₂ e)) :
    ∑ e ∈ S, w₁ e = ∑ e ∈ T, w₁ e ∧ ∑ e ∈ S, w₂ e = ∑ e ∈ T, w₂ e :=
  no_domination w₁ w₂ (by norm_num) (by norm_num) S T h₁ h₂ h₃

end NegCombination
