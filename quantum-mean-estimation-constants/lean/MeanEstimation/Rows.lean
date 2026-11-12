import MeanEstimation.Error

/-!
# Error bounds of the certified rows

Each theorem checks, in exact rational arithmetic, that the bound of `estimator_error` for the
parameters of one row (σ = 1, central band `b`, ratio `ρ`, `n` outer bands, angle width `η`
rounded up, `S = 1 + 1/16`) is at most `ε`. The bound increases with `η`, so it also holds
for the unrounded width.
-/

namespace MeanEstimation

/-- δ = 0.05, σ/ε = 10: margin 0.000148. -/
theorem row_005_10 :
    (1 : ℝ) * (1215850602607 / 100000000000000 : ℝ) + B (2 * 1 * 16 * (1215850602607 / 100000000000000 : ℝ) ^ 2) (17 / 16) (1 * 16 ^ 1) + (1215850602607 / 100000000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 1, (1 : ℝ) * 16 ^ (j + 1)) ≤
      (1 / 10 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.05, σ/ε = 33.33: margin 1.47e-05. -/
theorem row_005_33 :
    (2 : ℝ) * (270663068439 / 100000000000000 : ℝ) + B (2 * 1 * 32 * (270663068439 / 100000000000000 : ℝ) ^ 2) (17 / 16) (2 * 32 ^ 1) + (270663068439 / 100000000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 1, (2 : ℝ) * 32 ^ (j + 1)) ≤
      (3 / 100 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.05, σ/ε = 100: margin 1.58e-06. -/
theorem row_005_100 :
    (4 : ℝ) * (62829249919 / 100000000000000 : ℝ) + B (2 * 1 * 64 * (62829249919 / 100000000000000 : ℝ) ^ 2) (17 / 16) (4 * 64 ^ 1) + (62829249919 / 100000000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 1, (4 : ℝ) * 64 ^ (j + 1)) ≤
      (1 / 100 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.05, σ/ε = 333.3: margin 2.3e-07. -/
theorem row_005_333 :
    (4 : ℝ) * (599148951 / 2500000000000 : ℝ) + B (2 * 2 * 16 * (599148951 / 2500000000000 : ℝ) ^ 2) (17 / 16) (4 * 16 ^ 2) + (599148951 / 2500000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 2, (4 : ℝ) * 16 ^ (j + 1)) ≤
      (3 / 1000 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.05, σ/ε = 1000: margin 1e-08. -/
theorem row_005_1000 :
    (2 : ℝ) * (885535389 / 12500000000000 : ℝ) + B (2 * 2 * 32 * (885535389 / 12500000000000 : ℝ) ^ 2) (17 / 16) (2 * 32 ^ 2) + (885535389 / 12500000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 2, (2 : ℝ) * 32 ^ (j + 1)) ≤
      (1 / 1000 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.01, σ/ε = 10: margin 0.000148. -/
theorem row_001_10 :
    (1 : ℝ) * (1215850602607 / 100000000000000 : ℝ) + B (2 * 1 * 16 * (1215850602607 / 100000000000000 : ℝ) ^ 2) (17 / 16) (1 * 16 ^ 1) + (1215850602607 / 100000000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 1, (1 : ℝ) * 16 ^ (j + 1)) ≤
      (1 / 10 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.01, σ/ε = 33.33: margin 1.47e-05. -/
theorem row_001_33 :
    (2 : ℝ) * (270663068439 / 100000000000000 : ℝ) + B (2 * 1 * 32 * (270663068439 / 100000000000000 : ℝ) ^ 2) (17 / 16) (2 * 32 ^ 1) + (270663068439 / 100000000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 1, (2 : ℝ) * 32 ^ (j + 1)) ≤
      (3 / 100 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.01, σ/ε = 100: margin 1.58e-06. -/
theorem row_001_100 :
    (4 : ℝ) * (62829249919 / 100000000000000 : ℝ) + B (2 * 1 * 64 * (62829249919 / 100000000000000 : ℝ) ^ 2) (17 / 16) (4 * 64 ^ 1) + (62829249919 / 100000000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 1, (4 : ℝ) * 64 ^ (j + 1)) ≤
      (1 / 100 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.01, σ/ε = 333.3: margin 2.3e-07. -/
theorem row_001_333 :
    (4 : ℝ) * (599148951 / 2500000000000 : ℝ) + B (2 * 2 * 16 * (599148951 / 2500000000000 : ℝ) ^ 2) (17 / 16) (4 * 16 ^ 2) + (599148951 / 2500000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 2, (4 : ℝ) * 16 ^ (j + 1)) ≤
      (3 / 1000 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

/-- δ = 0.01, σ/ε = 1000: margin 1e-08. -/
theorem row_001_1000 :
    (2 : ℝ) * (885535389 / 12500000000000 : ℝ) + B (2 * 2 * 32 * (885535389 / 12500000000000 : ℝ) ^ 2) (17 / 16) (2 * 32 ^ 2) + (885535389 / 12500000000000 : ℝ) ^ 2 * (∑ j ∈ Finset.range 2, (2 : ℝ) * 32 ^ (j + 1)) ≤
      (1 / 1000 : ℝ) := by
  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num

end MeanEstimation
