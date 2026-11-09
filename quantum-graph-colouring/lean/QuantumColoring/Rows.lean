import Mathlib

/-!
# The closed-form rows k = 3, 4, 5

Row k = 3 is the square root of the 3-colouring base 1.3289 of [3]. Row k = 4 is the square root of the base 1.6981 of
the node bound in this folder, or 1.7159 of [8]. For k = 5 the bound of Theorem 9 of [1] comes from enumerating maximal
independent sets: 2^{d_5} ≤ max over s = 1..5 of s^{1/(2s)} · (2^{d_4})^{(s-1)/s}. The lemma `term_le` turns each term
into a polynomial inequality, which `norm_num` checks. References are those of the folder README.
-/

/-- If `s · x^(2(s-1)) ≤ y^(2s)`, then `s^(1/(2s)) · x'^((s-1)/s) ≤ y` for every `0 ≤ x' ≤ x`. -/
theorem term_le {s : ℕ} {x x' y : ℝ} (hs : 1 ≤ s) (hx' : 0 ≤ x') (hxx : x' ≤ x) (hy : 0 < y)
    (h : (s : ℝ) * x ^ (2 * (s - 1)) ≤ y ^ (2 * s)) :
    (s : ℝ) ^ (1 / (2 * (s : ℝ))) * x' ^ (((s : ℝ) - 1) / s) ≤ y := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have hx : 0 ≤ x := hx'.trans hxx
  have hmono : x' ^ (((s : ℝ) - 1) / s) ≤ x ^ (((s : ℝ) - 1) / s) :=
    Real.rpow_le_rpow hx' hxx (div_nonneg hs1 hs0.le)
  have ha : 0 ≤ (s : ℝ) ^ (1 / (2 * (s : ℝ))) * x ^ (((s : ℝ) - 1) / s) := by positivity
  refine (mul_le_mul_of_nonneg_left hmono (by positivity)).trans ?_
  rw [← Real.rpow_le_rpow_iff ha hy.le h2s, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hs0.le, ← Real.rpow_mul hx]
  have e1 : 1 / (2 * (s : ℝ)) * (2 * s) = 1 := by field_simp
  have e2 : ((s : ℝ) - 1) / s * (2 * s) = ((2 * (s - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hs]; push_cast; field_simp
  have e3 : (2 * (s : ℝ)) = ((2 * s : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e2, Real.rpow_one, Real.rpow_natCast, e3, Real.rpow_natCast]
  exact h

/-- Row k = 3: √1.3289 ≤ 1.1528. -/
theorem row3 : Real.sqrt 1.3289 ≤ 1.1528 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Row k = 3 from a node bound with base 1.32703: √1.32703 ≤ 1.1520. -/
theorem row3_cond : Real.sqrt 1.32703 ≤ 1.1520 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Row k = 4: √1.6981 ≤ 1.3032. -/
theorem row4 : Real.sqrt 1.6981 ≤ 1.3032 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Row k = 4 with the base of [8]: √1.7159 ≤ 1.3100. -/
theorem row4_base8 : Real.sqrt 1.7159 ≤ 1.3100 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Row k = 5, every term s = 1..5, with 2^{d_4} = √1.6981, so x^(2(s-1)) = 1.6981^(s-1). -/
theorem row5 (s : ℕ) (hs : 1 ≤ s) (hk : s ≤ 5) :
    (s : ℝ) ^ (1 / (2 * (s : ℝ))) * (Real.sqrt 1.6981) ^ (((s : ℝ) - 1) / s) ≤ 1.4518 := by
  refine term_le hs (Real.sqrt_nonneg _) le_rfl (by norm_num) ?_
  rw [pow_mul, Real.sq_sqrt (by norm_num)]
  interval_cases s <;> norm_num

/-- Row k = 5 with the base of [8], every term s = 1..5. -/
theorem row5_base8 (s : ℕ) (hs : 1 ≤ s) (hk : s ≤ 5) :
    (s : ℝ) ^ (1 / (2 * (s : ℝ))) * (Real.sqrt 1.7159) ^ (((s : ℝ) - 1) / s) ≤ 1.4578 := by
  refine term_le hs (Real.sqrt_nonneg _) le_rfl (by norm_num) ?_
  rw [pow_mul, Real.sq_sqrt (by norm_num)]
  interval_cases s <;> norm_num
