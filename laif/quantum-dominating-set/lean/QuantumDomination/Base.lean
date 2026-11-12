import Mathlib

/-!
# The base of the quantum bound for Dominating Set

The classical algorithm of [1] runs in time O*(1.4969^n). A quantum walk on its search tree takes the square root,
and √1.4969 ≤ 1.2235. References are those of the folder README.
-/

/-- √1.4969 ≤ 1.2235. -/
theorem base_le : Real.sqrt 1.4969 ≤ 1.2235 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- The square root of the time, as a power: (1.4969^n)^(1/2) ≤ 1.2235^n for every n. -/
theorem pow_base_le (n : ℕ) : Real.sqrt (1.4969 ^ n) ≤ 1.2235 ^ n := by
  rw [Real.sqrt_le_left (by positivity), ← pow_mul, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- Edge Dominating Set and its relatives: √1.3226 ≤ 1.1501. -/
theorem edge_base_le : Real.sqrt 1.3226 ≤ 1.1501 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Independent Dominating Set, the base of the classical analysis: 2^0.424 ≤ 1.34165. -/
theorem indep_root_le : (2 : ℝ) ^ ((53 : ℝ) / 125) ≤ 1.34165 := by
  have h : ((2 : ℝ) ^ ((53 : ℝ) / 125)) ^ (125 : ℝ) ≤ (1.34165 : ℝ) ^ (125 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num)).mp h

/-- Independent Dominating Set: at most n/2500000 branchings have factor 6 above the base 1.34165, and
1.34165 · 6^(1/2500000) ≤ 1.1583². -/
theorem indep_base_le : (1.34165 : ℝ) * (6 : ℝ) ^ ((1 : ℝ) / 2500000) ≤ 1.1583 ^ 2 := by
  have hq : (6 : ℝ) ≤ ((1.1583 : ℝ) ^ 2 / 1.34165) ^ 2500000 := by
    have h := one_add_mul_le_pow (a := (1.1583 : ℝ) ^ 2 / 1.34165 - 1) (by norm_num) 2500000
    rw [add_sub_cancel] at h
    refine le_trans ?_ h
    norm_num
  have h : (6 : ℝ) ^ ((1 : ℝ) / 2500000) ≤ (1.1583 : ℝ) ^ 2 / 1.34165 := by
    have := Real.rpow_le_rpow (by norm_num) hq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2500000)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((2500000 : ℕ) : ℝ) * (1 / 2500000) = 1 by norm_num,
      Real.rpow_one] at this
  calc (1.34165 : ℝ) * (6 : ℝ) ^ ((1 : ℝ) / 2500000)
      ≤ 1.34165 * ((1.1583 : ℝ) ^ 2 / 1.34165) := by gcongr
    _ = 1.1583 ^ 2 := by norm_num
