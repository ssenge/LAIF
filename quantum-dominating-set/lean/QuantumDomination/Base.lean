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

/-- Independent Dominating Set: the square root of 2^0.424 is 2^(53/250) ≤ 1.1583. -/
theorem indep_base_le : (2 : ℝ) ^ ((53 : ℝ) / 250) ≤ 1.1583 := by
  have h : ((2 : ℝ) ^ ((53 : ℝ) / 250)) ^ (250 : ℝ) ≤ (1.1583 : ℝ) ^ (250 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num)).mp h
