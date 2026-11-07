import Mathlib

/-!
# The closed-form rows k = 3, 4, 5

For k ≤ 5 the bound of Theorem 9 of [1] comes from enumerating maximal independent sets:
2^{d_k} ≤ max over s = 1..k of s^{1/(2s)} · (2^{d_{k-1}})^{(s-1)/s}. The lemma `term_le` turns each term into a
polynomial inequality, which `norm_num` checks. The 3-colouring base is 1.3217 [2], so 2^{d_3} = √1.3217.
References are those of the folder README.
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

/-- Row k = 3: √1.3217 ≤ 1.1497. -/
theorem row3 : Real.sqrt 1.3217 ≤ 1.1497 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Row k = 4, every term s = 1..4, with x = √1.3217, so x^(2(s-1)) = 1.3217^(s-1). -/
theorem row4 (s : ℕ) (hs : 1 ≤ s) (hk : s ≤ 4) :
    (s : ℝ) ^ (1 / (2 * (s : ℝ))) * (Real.sqrt 1.3217) ^ (((s : ℝ) - 1) / s) ≤ 1.32034 := by
  refine term_le hs (Real.sqrt_nonneg _) le_rfl (by norm_num) ?_
  rw [pow_mul, Real.sq_sqrt (by norm_num)]
  interval_cases s <;> norm_num

/-- Row k = 5, every term s = 1..5, from 2^{d_4} ≤ 1.32034. -/
theorem row5 (s : ℕ) (hs : 1 ≤ s) (hk : s ≤ 5) {x' : ℝ} (hx' : 0 ≤ x') (hx : x' ≤ 1.32034) :
    (s : ℝ) ^ (1 / (2 * (s : ℝ))) * x' ^ (((s : ℝ) - 1) / s) ≤ 1.4671 := by
  refine term_le hs hx' hx (by norm_num) ?_
  interval_cases s <;> norm_num
