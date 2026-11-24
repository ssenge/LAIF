import Mathlib

/-!
# Scalar steps for the closest determinant state

Inequalities used in the overlap bound and in the lower bound of the closest determinant state.
-/

open Finset

namespace DetState

/-- For numbers in `[0, 1]`, `1 - ∏ a_i ≤ ∑ (1 - a_i)`. -/
theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    have hj0 := h0 j (mem_insert_self j s)
    have hj1 := h1 j (mem_insert_self j s)
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hP0 : 0 ≤ ∏ i ∈ s, a i := prod_nonneg (fun i hi => h0 i (mem_insert_of_mem hi))
    have hP1 : ∏ i ∈ s, a i ≤ 1 :=
      Finset.prod_le_one₀ (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    nlinarith [mul_nonneg (sub_nonneg.mpr hj1) (sub_nonneg.mpr hP1)]

/-- `1 - σ² ≤ 2 (1 - σ)` for every real `σ`. -/
theorem one_sub_sq_le (σ : ℝ) : 1 - σ ^ 2 ≤ 2 * (1 - σ) := by
  nlinarith [sq_nonneg (1 - σ)]

/-- `1 - c ≤ 1 - c²` for `c ∈ [0, 1]`. -/
theorem one_sub_le_one_sub_sq {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : 1 - c ≤ 1 - c ^ 2 := by
  nlinarith

/-- `log ((1 + x) / (1 - x)) ≤ 4 x` for `0 ≤ x ≤ 1/2`. -/
theorem log_ratio_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.log ((1 + x) / (1 - x)) ≤ 4 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hq : 0 < (1 + x) / (1 - x) := div_pos (by linarith) hpos
  have h := Real.log_le_sub_one_of_pos hq
  have : (1 + x) / (1 - x) - 1 = 2 * x / (1 - x) := by field_simp; ring
  rw [this] at h
  have : 2 * x / (1 - x) ≤ 4 * x := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

/-- The relative entropy of two coins with biases `1/2 ± 2ε` is at most `64 ε²` for `0 ≤ ε ≤ 1/8`. -/
theorem coin_divergence_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    4 * ε * Real.log ((1 + 4 * ε) / (1 - 4 * ε)) ≤ 64 * ε ^ 2 := by
  have := log_ratio_le (x := 4 * ε) (by linarith) (by linarith)
  nlinarith

/-- The reduction of the lower bound: a fidelity of at least `1/2 + ε` with the mixture of weights
`1/2 ± 2ε` of two orthogonal states forces `a - b ≥ 1/2`. -/
theorem reduction {a b ε : ℝ} (hε : 0 < ε) (hab : a + b ≤ 1)
    (h : (1 / 2 + 2 * ε) * a + (1 / 2 - 2 * ε) * b ≥ 1 / 2 + ε) : a - b ≥ 1 / 2 := by
  have h2 : 2 * ε * (a - b) ≥ ε := by nlinarith
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith

end DetState
