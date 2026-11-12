import Mathlib

/-!
# Scalar steps of the doubling learner for Gaussian unitaries

* `exp_quarter_le`, `exp_half_le`, `exp_le_inv_one_sub`, `exp_056_le`, `exp_028_le`, `expm1_le_mul`,
  `neg_log_one_sub_le`: elementary bounds on the exponential and the logarithm.
* `energy_le`: the photon-number bound of Lemma 4, `m (e^{2γ} - 1)/2 + (e^γ + 1/4)² η²/2 ≤ 0.92 ñ`
  for `η² = ñ/2`, `γ ≤ 1/4` and `5 m γ ≤ ñ`.
* `sigma_le`, `tau_coef`, `nu_coef`: the covariance bound `(e^{1/2} + 1)/2 ≤ 1.325` and the constants
  of the two estimation events of Lemma 5.
* `log_lip`, `khat_le`, `wprime_le`, `kappa_le`, `mk_le`, `b_update`, `b_update_one`: the constants of
  the stage update of Lemma 6.
* `coarse_norm`, `coarse_dist`, `coarse_log`: the constants of the coarse stage.
* `prop22_const`, `g_le`, `prop22_combine`, `final_sym`, `final_disp`: the final error bound.
* `rotation_floor`, `rotation_p`, `rotation_dist`: the scalar steps of the rotation example.
* `geom_queries`: the number of chains of lengths `1, 2, ..., 2^L` adds up to `2^{L+1} - 1`.
-/

namespace GaussianDoubling

open Real

theorem exp_quarter_le : exp (1 / 4) ≤ 1.2841 := by
  by_contra h
  push_neg at h
  have h1 : exp 1 = exp (1 / 4) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (1.2841 : ℝ) ^ 4 < exp (1 / 4) ^ 4 := by gcongr
  have h3 := Real.exp_one_lt_d9
  norm_num at h2
  linarith

theorem exp_half_le : exp (1 / 2) ≤ 1.6488 := by
  by_contra h
  push_neg at h
  have h1 : exp 1 = exp (1 / 2) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (1.6488 : ℝ) ^ 2 < exp (1 / 2) ^ 2 := by gcongr
  have h3 := Real.exp_one_lt_d9
  norm_num at h2
  linarith

theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : exp x ≤ 1 / (1 - x) := by
  have h := Real.add_one_le_exp (-x)
  have hpos : 0 < 1 - x := by linarith
  rw [Real.exp_neg] at h
  rw [le_div_iff₀ hpos]
  have he := Real.exp_pos x
  calc exp x * (1 - x) = exp x * (-x + 1) := by ring
    _ ≤ exp x * (exp x)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (ne_of_gt he)

theorem exp_056_le : exp 0.56 ≤ 1.7541 := by
  have hs : exp 0.56 = exp (1 / 2) * exp 0.06 := by rw [← Real.exp_add]; norm_num
  have h1 := exp_half_le
  have h2 := exp_le_inv_one_sub (x := 0.06) (by norm_num)
  rw [hs]
  calc exp (1 / 2) * exp 0.06 ≤ 1.6488 * (1 / (1 - 0.06)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
    _ ≤ 1.7541 := by norm_num

theorem exp_028_le : exp 0.28 ≤ 1.33 := by
  have hs : exp 0.56 = exp 0.28 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 := exp_056_le
  have hp := Real.exp_pos 0.28
  nlinarith

theorem expm1_le_mul {x : ℝ} (hx : 0 ≤ x) : exp x - 1 ≤ x * exp x := by
  have h := Real.add_one_le_exp (-x)
  rw [Real.exp_neg] at h
  have he := Real.exp_pos x
  have h2 : (-x + 1) * exp x ≤ 1 := by
    calc (-x + 1) * exp x ≤ (exp x)⁻¹ * exp x := by gcongr
      _ = 1 := inv_mul_cancel₀ (ne_of_gt he)
  linarith

theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at h
  have he : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  linarith

/-- Lemma 4: the photon number of every input of a chain. -/
theorem energy_le (m nin γ : ℝ) (hm : 1 ≤ m) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 4)
    (hγm : 5 * m * γ ≤ nin) :
    m * (exp (2 * γ) - 1) / 2 + (exp γ + 1 / 4) ^ 2 * (nin / 2) / 2 ≤ 0.92 * nin := by
  have hnin : 0 ≤ nin := by nlinarith
  have h2γ : exp (2 * γ) ≤ 1.6488 := le_trans (Real.exp_le_exp.mpr (by linarith)) exp_half_le
  have hexpm1 : exp (2 * γ) - 1 ≤ 2 * γ * exp (2 * γ) := expm1_le_mul (by linarith)
  have hA : exp (2 * γ) - 1 ≤ 3.3 * γ := by nlinarith
  have hB : exp γ ≤ 1.2841 := le_trans (Real.exp_le_exp.mpr hγ) exp_quarter_le
  have hB0 : 0 ≤ exp γ := (Real.exp_pos γ).le
  have hC : (exp γ + 1 / 4) ^ 2 ≤ 2.36 := by nlinarith
  have hD : m * (exp (2 * γ) - 1) / 2 ≤ 0.33 * nin := by nlinarith
  have hE : (exp γ + 1 / 4) ^ 2 * (nin / 2) / 2 ≤ 0.59 * nin := by nlinarith
  linarith

/-- Lemma 5: the heterodyne covariance `(W^k W^kᵀ + 1)/2` has norm at most `1.325`. -/
theorem sigma_le : (exp (1 / 2) + 1) / 2 ≤ 1.325 := by
  have := exp_half_le
  linarith

theorem tau_coef : Real.sqrt (1.325 / 200) ≤ 0.0814 := by
  rw [show (0.0814 : ℝ) = Real.sqrt (0.0814 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem nu_coef : Real.sqrt (1.325 / 400) * (1 / 4) ≤ 0.0145 := by
  have h : Real.sqrt (1.325 / 400) ≤ 0.058 := by
    rw [show (0.058 : ℝ) = Real.sqrt (0.058 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- Lemma 6: the radius of the logarithm series and its constant. -/
theorem log_lip : exp (1 / 4) - 1 + 0.0814 * (1 / 4) ≤ 0.305 ∧ 1 / (1 - (0.305 : ℝ)) ≤ 1.44 := by
  have := exp_quarter_le
  constructor
  · linarith
  · norm_num

theorem khat_le : (1.44 : ℝ) * 0.0814 ≤ 0.118 ∧ (1 + (0.118 : ℝ)) * (1 / 4) ≤ 0.28 := by
  constructor <;> norm_num

theorem wprime_le : exp 0.56 * 0.118 ≤ 0.21 := by
  have := exp_056_le
  nlinarith

theorem kappa_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 4) : -Real.log (1 - 0.21 * y) ≤ y / 2 := by
  have h := neg_log_one_sub_le (x := 0.21 * y) (by linarith) (by linarith)
  have hp : 0 < 1 - 0.21 * y := by linarith
  have h2 : 0.21 * y / (1 - 0.21 * y) ≤ y / 2 := by
    rw [div_le_iff₀ hp]
    nlinarith
  linarith

theorem mk_le : exp (1 / 4) - 1 ≤ 0.285 := by
  have := exp_quarter_le
  linarith

theorem b_update {e : ℝ} (he : e ≤ exp (1 / 4)) : 1.33 * (0.285 / 4 + 0.0145 * e) ≤ 1 / 8 := by
  have := exp_quarter_le
  nlinarith

theorem b_update_one : 1.33 * 0.0145 * exp (1 / 4) ≤ 1 / 8 := by
  have := exp_quarter_le
  nlinarith

/-- Coarse stage: `‖T‖ ≤ 1.06 z` and `‖T⁻¹ S - 1‖ ≤ 0.24 γ` for `ε₀ = γ/(40 z³)`. -/
theorem coarse_norm {z γ : ℝ} (hz : 1 ≤ z) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 4) :
    (2 * z + 1) * (γ / (40 * z ^ 3)) < 1 / 2 ∧ z + 9 * z ^ 2 * (γ / (40 * z ^ 3)) ≤ 1.06 * z := by
  have hz0 : 0 < z := by linarith
  have h3 : 0 < 40 * z ^ 3 := by positivity
  constructor
  · rw [mul_div_assoc', div_lt_iff₀ h3]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hz 3, sq_nonneg z]
  · have hs : 9 * z ^ 2 * (γ / (40 * z ^ 3)) = 9 * γ / (40 * z) := by
      field_simp
    rw [hs]
    have h40 : 0 < 40 * z := by positivity
    have : 9 * γ / (40 * z) ≤ 0.06 * z := by
      rw [div_le_iff₀ h40]
      nlinarith
    linarith

theorem coarse_dist {z γ : ℝ} (hz : 1 ≤ z) (hγ0 : 0 ≤ γ) :
    1.06 * z * (9 * z ^ 2 * (γ / (40 * z ^ 3))) ≤ 0.24 * γ := by
  have hz0 : 0 < z := by linarith
  have hs : 1.06 * z * (9 * z ^ 2 * (γ / (40 * z ^ 3))) = 0.2385 * γ := by
    field_simp
    ring
  rw [hs]
  nlinarith

theorem coarse_log {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 4) :
    -Real.log (1 - 0.24 * γ) ≤ 0.26 * γ := by
  have h := neg_log_one_sub_le (x := 0.24 * γ) (by linarith) (by linarith)
  have hp : 0 < 1 - 0.24 * γ := by linarith
  have h2 : 0.24 * γ / (1 - 0.24 * γ) ≤ 0.26 * γ := by
    rw [div_le_iff₀ hp]
    nlinarith
  linarith

/-- The constant of the continuity bound for symplectic Gaussian unitaries. -/
theorem prop22_const {m : ℝ} (hm : 1 ≤ m) :
    Real.sqrt 6 + Real.sqrt 10 + 5 * Real.sqrt (2 * m) ≤ 9 * Real.sqrt (2 * m) := by
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s6 := Real.sqrt_nonneg 6
  have s10 := Real.sqrt_nonneg 10
  have s2 := Real.sqrt_nonneg 2
  have hprod : Real.sqrt 6 * Real.sqrt 10 ≤ 7.75 := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [show (7.75 : ℝ) = Real.sqrt (7.75 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsum : Real.sqrt 6 + Real.sqrt 10 ≤ 4 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt 6 + Real.sqrt 10 - 4 * Real.sqrt 2)]
  have hm2 : Real.sqrt 2 ≤ Real.sqrt (2 * m) := Real.sqrt_le_sqrt (by linarith)
  linarith

theorem g_le {x : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ 1.06) :
    Real.sqrt (π / (x + 1)) + Real.sqrt (2 * x) ≤ 2.71 := by
  have h1 : Real.sqrt (π / (x + 1)) ≤ 1.2534 := by
    rw [show (1.2534 : ℝ) = Real.sqrt (1.2534 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.pi_lt_d4]
  have h2 : Real.sqrt (2 * x) ≤ 1.4561 := by
    rw [show (1.4561 : ℝ) = Real.sqrt (1.4561 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem prop22_combine {m n θ : ℝ} (hm : 0 ≤ m) :
    9 * Real.sqrt (2 * m) * (n + 1) * (Real.sqrt (2 * m) * θ) = 18 * m * (n + 1) * θ := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * m by linarith)
  have : 9 * Real.sqrt (2 * m) * (n + 1) * (Real.sqrt (2 * m) * θ)
      = 9 * (Real.sqrt (2 * m) * Real.sqrt (2 * m)) * (n + 1) * θ := by ring
  rw [this, h]
  ring

/-- Final step, symplectic part: `2.71² · 18 · 0.21 m (n + 1) γ / k ≤ ε²/4` for
`k ≥ 112 m (n + 1) γ / ε²`. -/
theorem final_sym {m n γ ε k : ℝ} (hA : 0 ≤ m * (n + 1) * γ) (hε : 0 < ε) (hk : 0 < k)
    (hkA : 112 * m * (n + 1) * γ / ε ^ 2 ≤ k) :
    2.71 ^ 2 * 18 * 0.21 * m * (n + 1) * γ / k ≤ ε ^ 2 / 4 := by
  have he2 : 0 < ε ^ 2 := by positivity
  rw [div_le_iff₀ he2] at hkA
  rw [div_le_iff₀ hk]
  nlinarith

/-- Final step, displacement part: `√2 s · z η / (8k) ≤ ε/2` for `k ≥ z η s / (2 √2 ε)`. -/
theorem final_disp {s z η ε k : ℝ} (hs : 0 ≤ s) (hz : 0 ≤ z) (hη : 0 ≤ η) (hε : 0 < ε)
    (hk : 0 < k) (hkB : z * η * s / (2 * Real.sqrt 2 * ε) ≤ k) :
    Real.sqrt 2 * s * (z * η / (8 * k)) ≤ ε / 2 := by
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hd : 0 < 2 * Real.sqrt 2 * ε := by positivity
  rw [div_le_iff₀ hd] at hkB
  have hgoal : Real.sqrt 2 * s * (z * η / (8 * k)) = Real.sqrt 2 * (z * η * s) / (8 * k) := by
    ring
  rw [hgoal, div_le_iff₀ (by positivity)]
  have h3 : Real.sqrt 2 * (z * η * s) ≤ Real.sqrt 2 * (k * (2 * Real.sqrt 2 * ε)) :=
    mul_le_mul_of_nonneg_left hkB s2.le
  have h4 : Real.sqrt 2 * (k * (2 * Real.sqrt 2 * ε)) = 2 * (Real.sqrt 2 * Real.sqrt 2) * k * ε := by
    ring
  rw [h4, h2] at h3
  linarith

/-- Rotation example: `⌊π/θ⌋ ≥ 2n` for `θ ≤ π/(2n + 1)`. -/
theorem rotation_floor {n θ : ℝ} (hn : 0 ≤ n) (hθ : 0 < θ) (hθn : θ ≤ π / (2 * n + 1)) :
    2 * n ≤ (⌊π / θ⌋₊ : ℝ) := by
  have hpos : 0 < 2 * n + 1 := by linarith
  have h1 : 2 * n + 1 ≤ π / θ := by
    rw [le_div_iff₀ hθ]
    rw [le_div_iff₀ hpos] at hθn
    linarith
  have h2 := Nat.lt_floor_add_one (π / θ)
  linarith

theorem rotation_p {n θ k : ℝ} (hn : 0 ≤ n) (hθ : 0 < θ) (hk : 0 < k) (hkθ : k ≤ π / θ) :
    n * θ / π ≤ n / k := by
  have hπ := Real.pi_pos
  rw [le_div_iff₀ hθ] at hkθ
  rw [div_le_div_iff₀ hπ hk]
  nlinarith

theorem rotation_dist {p c : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hc : c ≤ 0) :
    p ≤ 2 * p * (1 - p) * (1 - c) := by
  nlinarith [mul_nonneg hp0 (show 0 ≤ -c by linarith), mul_nonneg (mul_nonneg hp0 hp0) (show 0 ≤ -c by linarith)]

/-- The chains of lengths `1, 2, 4, ..., 2^L` contain `2^{L+1} - 1` queries in total. -/
theorem geom_queries (L : ℕ) : ∑ t ∈ Finset.range (L + 1), 2 ^ t = 2 ^ (L + 1) - 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ (L + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (L + 1)]
    omega

end GaussianDoubling
