import Mathlib

/-!
# One mode of a uniformly damped oscillator

In dimensionless time `τ = γ t` and stiffness `ℓ = λ / γ²`, a mode of `u'' + 2γ u' + λ u = 0` started from
`u(0) = 0`, `u'(0) = γ` is `G(τ)` with `G'' + 2 G' + ℓ G = 0`, `G(0) = 0`, `G'(0) = 1`. Its derivative is `Gd`.
The kinetic-energy fraction at time `τ` of a mode of unit energy is at most `ℓ G² + Gd²`
(the squared norm of the second row of the mode propagator in energy coordinates).

This file gives the closed forms in the overdamped (`ℓ = 1 - ρ²`, `0 < ρ ≤ 1`), critical (`ℓ = 1`) and
underdamped (`ℓ = 1 + ω²`, `ω > 0`) cases, checks that they solve the equation, and proves
`ℓ G² + Gd² ≤ 8 / τ` for `τ ≥ 8` in all cases (and for all `τ > 0` when `ρ ≥ 1/2`).
-/

open Real

namespace DampedOsc

/-- Overdamped mode, `ρ = √(1 - ℓ)`. -/
noncomputable def Gover (ρ τ : ℝ) : ℝ := (exp (-(τ * (1 - ρ))) - exp (-(τ * (1 + ρ)))) / (2 * ρ)

/-- Derivative of the overdamped mode. -/
noncomputable def Gdover (ρ τ : ℝ) : ℝ :=
  (-(1 - ρ) * exp (-(τ * (1 - ρ))) + (1 + ρ) * exp (-(τ * (1 + ρ)))) / (2 * ρ)

/-- Second derivative of the overdamped mode. -/
noncomputable def Gddover (ρ τ : ℝ) : ℝ :=
  ((1 - ρ) ^ 2 * exp (-(τ * (1 - ρ))) - (1 + ρ) ^ 2 * exp (-(τ * (1 + ρ)))) / (2 * ρ)

/-- Underdamped mode, `ω = √(ℓ - 1)`. -/
noncomputable def Gunder (ω τ : ℝ) : ℝ := exp (-τ) * sin (τ * ω) / ω

/-- Derivative of the underdamped mode. -/
noncomputable def Gdunder (ω τ : ℝ) : ℝ := exp (-τ) * (cos (τ * ω) - sin (τ * ω) / ω)

/-- Critical mode, `ℓ = 1`. -/
noncomputable def Gcrit (τ : ℝ) : ℝ := τ * exp (-τ)

/-- Derivative of the critical mode. -/
noncomputable def Gdcrit (τ : ℝ) : ℝ := (1 - τ) * exp (-τ)

lemma hasDerivAt_exp_neg_mul (c τ : ℝ) :
    HasDerivAt (fun s => exp (-(s * c))) (-c * exp (-(τ * c))) τ := by
  have h0 : HasDerivAt (fun s => -(s * c)) (-c) τ := (hasDerivAt_mul_const c).neg
  have h := h0.exp
  rw [show -c * exp (-(τ * c)) = exp (-(τ * c)) * -c by ring]
  exact h

theorem Gover_hasDerivAt (ρ τ : ℝ) : HasDerivAt (Gover ρ) (Gdover ρ τ) τ := by
  have h := ((hasDerivAt_exp_neg_mul (1 - ρ) τ).sub (hasDerivAt_exp_neg_mul (1 + ρ) τ)).div_const (2 * ρ)
  have e : Gdover ρ τ = (-(1 - ρ) * exp (-(τ * (1 - ρ))) - -(1 + ρ) * exp (-(τ * (1 + ρ)))) / (2 * ρ) := by
    unfold Gdover; ring
  rw [e]; exact h

theorem Gdover_hasDerivAt (ρ τ : ℝ) : HasDerivAt (Gdover ρ) (Gddover ρ τ) τ := by
  have h := (((hasDerivAt_exp_neg_mul (1 - ρ) τ).const_mul (-(1 - ρ))).add
    ((hasDerivAt_exp_neg_mul (1 + ρ) τ).const_mul (1 + ρ))).div_const (2 * ρ)
  have e : Gddover ρ τ = (-(1 - ρ) * (-(1 - ρ) * exp (-(τ * (1 - ρ)))) +
      (1 + ρ) * (-(1 + ρ) * exp (-(τ * (1 + ρ))))) / (2 * ρ) := by
    unfold Gddover; ring
  rw [e]; exact h

/-- The overdamped closed form solves `G'' + 2 G' + (1 - ρ²) G = 0` with `G(0) = 0`, `G'(0) = 1`. -/
theorem Gover_ode (ρ τ : ℝ) (hρ : ρ ≠ 0) :
    Gddover ρ τ + 2 * Gdover ρ τ + (1 - ρ ^ 2) * Gover ρ τ = 0 ∧ Gover ρ 0 = 0 ∧ Gdover ρ 0 = 1 := by
  refine ⟨?_, by simp [Gover], ?_⟩
  · unfold Gddover Gdover Gover; field_simp; ring
  · unfold Gdover; simp; field_simp; ring

theorem Gunder_hasDerivAt (ω τ : ℝ) (hω : ω ≠ 0) : HasDerivAt (Gunder ω) (Gdunder ω τ) τ := by
  have h1 : HasDerivAt (fun s => exp (-s)) (-exp (-τ)) τ := by
    simpa using (hasDerivAt_neg τ).exp
  have h2 : HasDerivAt (fun s => sin (s * ω)) (cos (τ * ω) * ω) τ := by
    simpa using ((hasDerivAt_id τ).mul_const ω).sin
  have h := (h1.mul h2).div_const ω
  have e : Gdunder ω τ = (-exp (-τ) * sin (τ * ω) + exp (-τ) * (cos (τ * ω) * ω)) / ω := by
    unfold Gdunder; field_simp; ring
  rw [e]; exact h

/-- Second derivative of the underdamped mode. -/
noncomputable def Gddunder (ω τ : ℝ) : ℝ :=
  exp (-τ) * ((1 - ω ^ 2) * sin (τ * ω) / ω - 2 * cos (τ * ω))

theorem Gdunder_hasDerivAt (ω τ : ℝ) (hω : ω ≠ 0) : HasDerivAt (Gdunder ω) (Gddunder ω τ) τ := by
  have h1 : HasDerivAt (fun s => exp (-s)) (-exp (-τ)) τ := by
    simpa using (hasDerivAt_neg τ).exp
  have hs : HasDerivAt (fun s => sin (s * ω)) (cos (τ * ω) * ω) τ := by
    simpa using ((hasDerivAt_id τ).mul_const ω).sin
  have hc : HasDerivAt (fun s => cos (s * ω)) (-sin (τ * ω) * ω) τ := by
    simpa using ((hasDerivAt_id τ).mul_const ω).cos
  have h := h1.mul (hc.sub (hs.div_const ω))
  have e : Gddunder ω τ = -exp (-τ) * (cos (τ * ω) - sin (τ * ω) / ω) +
      exp (-τ) * (-sin (τ * ω) * ω - cos (τ * ω) * ω / ω) := by
    unfold Gddunder; field_simp; ring
  rw [e]; exact h

/-- The underdamped closed form solves `G'' + 2 G' + (1 + ω²) G = 0` with `G(0) = 0`, `G'(0) = 1`. -/
theorem Gunder_ode (ω τ : ℝ) (hω : ω ≠ 0) :
    Gddunder ω τ + 2 * Gdunder ω τ + (1 + ω ^ 2) * Gunder ω τ = 0 ∧ Gunder ω 0 = 0 ∧ Gdunder ω 0 = 1 := by
  refine ⟨?_, by simp [Gunder], by simp [Gdunder]⟩
  unfold Gddunder Gdunder Gunder; field_simp; ring

/-- The critical closed form solves `G'' + 2 G' + G = 0` with `G(0) = 0`, `G'(0) = 1`. -/
theorem Gcrit_ode (τ : ℝ) :
    HasDerivAt Gcrit (Gdcrit τ) τ ∧ HasDerivAt Gdcrit ((τ - 2) * exp (-τ)) τ ∧
      (τ - 2) * exp (-τ) + 2 * Gdcrit τ + Gcrit τ = 0 ∧ Gcrit 0 = 0 ∧ Gdcrit 0 = 1 := by
  have h1 : HasDerivAt (fun s => exp (-s)) (-exp (-τ)) τ := by
    simpa using (hasDerivAt_neg τ).exp
  refine ⟨?_, ?_, by simp only [Gdcrit, Gcrit]; ring, by simp [Gcrit], by simp [Gdcrit]⟩
  · have h := (hasDerivAt_id τ).mul h1
    rw [show Gdcrit τ = 1 * exp (-τ) + id τ * -exp (-τ) by unfold Gdcrit; simp; ring]
    exact h
  · have h := ((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ)).mul h1
    rw [show (τ - 2) * exp (-τ) = (0 - 1) * exp (-τ) + (1 - id τ) * -exp (-τ) by simp; ring]
    exact h

/-! ### Elementary bounds -/

/-- `y e^{-y} ≤ 1`. -/
lemma mul_exp_neg_le_one (y : ℝ) : y * exp (-y) ≤ 1 := by
  have h := add_one_le_exp y
  have hp : 0 < exp (-y) := exp_pos _
  have : exp y * exp (-y) = 1 := by rw [← exp_add]; simp
  nlinarith

/-- For `τ ≥ 8`, `(2 + 4τ + 4τ²) e^{-τ} ≤ 8/τ`. -/
lemma poly_exp_neg_le (τ : ℝ) (hτ : 8 ≤ τ) : (2 + 4 * τ + 4 * τ ^ 2) * exp (-τ) ≤ 8 / τ := by
  have hτ0 : 0 < τ := by linarith
  have h7 := pow_div_factorial_le_exp (x := τ) hτ0.le 7
  have hf : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hf] at h7
  have hE : exp τ * exp (-τ) = 1 := by rw [← exp_add]; simp
  have hp : 0 < exp (-τ) := exp_pos _
  rw [le_div_iff₀ hτ0]
  -- τ (2 + 4τ + 4τ²) ≤ 8 τ⁷ / 5040 ≤ 8 e^τ
  have hpoly : τ * (2 + 4 * τ + 4 * τ ^ 2) ≤ 8 * (τ ^ 7 / 5040) := by
    have h8 : (8 : ℝ) ^ 3 ≤ τ ^ 3 := pow_le_pow_left₀ (by norm_num) hτ 3
    have h2 : 2 + 4 * τ + 4 * τ ^ 2 ≤ 5 * τ ^ 2 := by nlinarith
    have : 630 * (5 * τ ^ 2) ≤ τ ^ 6 := by nlinarith [pow_pos hτ0 3]
    nlinarith [pow_pos hτ0 3, pow_pos hτ0 2]
  calc (2 + 4 * τ + 4 * τ ^ 2) * exp (-τ) * τ = τ * (2 + 4 * τ + 4 * τ ^ 2) * exp (-τ) := by ring
    _ ≤ 8 * (τ ^ 7 / 5040) * exp (-τ) := by gcongr
    _ ≤ 8 * exp τ * exp (-τ) := by gcongr
    _ = 8 := by rw [mul_assoc, hE]; ring

/-! ### The kinetic-energy bound -/

/-- Overdamped modes with `ρ ≥ 1/2`: `ℓ G² + Gd² ≤ 3/τ` for every `τ > 0`. -/
theorem ke_over_large (ρ τ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ) :
    (1 - ρ ^ 2) * Gover ρ τ ^ 2 + Gdover ρ τ ^ 2 ≤ 3 / τ := by
  set a := exp (-(τ * (1 - ρ))) with ha
  set b := exp (-(τ * (1 + ρ))) with hb
  have ha0 : 0 < a := exp_pos _
  have hb0 : 0 < b := exp_pos _
  have hba : b ≤ a := exp_le_exp.2 (by nlinarith)
  have hρ0 : 0 < ρ := by linarith
  have hα0 : 0 ≤ 1 - ρ := by linarith
  -- 2 τ (1 - ρ) a² ≤ 1 and 3 τ b² ≤ 1
  have hy : (2 * τ * (1 - ρ)) * a ^ 2 ≤ 1 := by
    have : a ^ 2 = exp (-(2 * τ * (1 - ρ))) := by rw [ha, sq, ← exp_add]; ring_nf
    rw [this]; exact mul_exp_neg_le_one _
  have hb2 : (3 * τ) * b ^ 2 ≤ 1 := by
    have e1 : b ^ 2 = exp (-(2 * τ * (1 + ρ))) := by rw [hb, sq, ← exp_add]; ring_nf
    have e2 : exp (-(2 * τ * (1 + ρ))) ≤ exp (-(3 * τ)) := exp_le_exp.2 (by nlinarith)
    have := mul_exp_neg_le_one (3 * τ)
    rw [e1]; nlinarith [exp_pos (-(3 * τ))]
  have hG : Gover ρ τ = (a - b) / (2 * ρ) := rfl
  have hGd : Gdover ρ τ = (-(1 - ρ) * a + (1 + ρ) * b) / (2 * ρ) := rfl
  have h2ρ : 0 < 2 * ρ := by linarith
  have hG0 : 0 ≤ Gover ρ τ := by rw [hG]; exact div_nonneg (by linarith) h2ρ.le
  have hGle : Gover ρ τ ≤ a := by rw [hG, div_le_iff₀ h2ρ]; nlinarith
  have hGdabs : |Gdover ρ τ| ≤ (1 - ρ) * a + 3 / 2 * b := by
    rw [hGd, abs_le]; constructor
    · rw [le_div_iff₀ h2ρ]; nlinarith [mul_nonneg hα0 ha0.le]
    · rw [div_le_iff₀ h2ρ]; nlinarith [mul_nonneg hα0 ha0.le]
  have t1 : (1 - ρ ^ 2) * Gover ρ τ ^ 2 ≤ 2 * (1 - ρ) * a ^ 2 := by
    have : Gover ρ τ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hG0 hGle 2
    have hl : 1 - ρ ^ 2 ≤ 2 * (1 - ρ) := by nlinarith
    have hl0 : 0 ≤ 1 - ρ ^ 2 := by nlinarith
    nlinarith [sq_nonneg (Gover ρ τ), sq_nonneg a]
  have t2 : Gdover ρ τ ^ 2 ≤ 2 * (1 - ρ) ^ 2 * a ^ 2 + 9 / 2 * b ^ 2 := by
    have h := sq_le_sq' (abs_le.1 hGdabs).1 (abs_le.1 hGdabs).2
    nlinarith [sq_nonneg ((1 - ρ) * a - 3 / 2 * b)]
  have t4 : τ * ((1 - ρ) ^ 2 * a ^ 2) ≤ 1 / 4 := by
    have : τ * ((1 - ρ) ^ 2 * a ^ 2) = (1 - ρ) * (τ * (1 - ρ) * a ^ 2) := by ring
    rw [this]
    have h1 : τ * (1 - ρ) * a ^ 2 ≤ 1 / 2 := by nlinarith
    have h2 : 0 ≤ τ * (1 - ρ) * a ^ 2 := by positivity
    nlinarith
  rw [le_div_iff₀ hτ]
  nlinarith

/-- Overdamped modes with `ρ < 1/2`: `ℓ G² + Gd² ≤ 8/τ` for `τ ≥ 8`. -/
theorem ke_over_small (ρ τ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1 / 2) (hτ : 8 ≤ τ) :
    (1 - ρ ^ 2) * Gover ρ τ ^ 2 + Gdover ρ τ ^ 2 ≤ 8 / τ := by
  have hτ0 : 0 < τ := by linarith
  set a := exp (-(τ * (1 - ρ))) with ha
  set b := exp (-(τ * (1 + ρ))) with hb
  have ha0 : 0 < a := exp_pos _
  have hb0 : 0 < b := exp_pos _
  -- b = a e^{-2τρ} and a - b ≤ 2 τ ρ a
  have hbab : b = a * exp (-(2 * τ * ρ)) := by rw [ha, hb, ← exp_add]; ring_nf
  have hdiff : a - b ≤ 2 * τ * ρ * a := by
    have := add_one_le_exp (-(2 * τ * ρ))
    rw [hbab]; nlinarith
  have hbaa : b ≤ a := by rw [hbab]; exact mul_le_of_le_one_right ha0.le (exp_le_one_iff.2 (by nlinarith))
  have hG : Gover ρ τ = (a - b) / (2 * ρ) := rfl
  have hG0 : 0 ≤ Gover ρ τ := by rw [hG]; apply div_nonneg <;> linarith
  have hGle : Gover ρ τ ≤ τ * a := by
    rw [hG, div_le_iff₀ (by linarith)]; linarith
  have hGd : Gdover ρ τ = (a + b) / 2 - Gover ρ τ := by
    have e : Gdover ρ τ = (-(1 - ρ) * a + (1 + ρ) * b) / (2 * ρ) := rfl
    rw [e, hG]; field_simp; ring
  have hGdabs : |Gdover ρ τ| ≤ (1 + τ) * a := by
    rw [hGd, abs_le]; constructor <;> nlinarith
  have hl0 : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hl1 : 1 - ρ ^ 2 ≤ 1 := by nlinarith
  have h1 : (1 - ρ ^ 2) * Gover ρ τ ^ 2 ≤ τ ^ 2 * a ^ 2 := by
    have : Gover ρ τ ^ 2 ≤ (τ * a) ^ 2 := pow_le_pow_left₀ hG0 hGle 2
    nlinarith [sq_nonneg (Gover ρ τ)]
  have h2 : Gdover ρ τ ^ 2 ≤ (1 + τ) ^ 2 * a ^ 2 := by
    have := sq_le_sq' (abs_le.1 hGdabs).1 (abs_le.1 hGdabs).2
    nlinarith
  have ha2 : a ^ 2 ≤ exp (-τ) := by
    rw [ha, sq, ← exp_add]; exact exp_le_exp.2 (by nlinarith)
  have hkey := poly_exp_neg_le τ hτ
  calc (1 - ρ ^ 2) * Gover ρ τ ^ 2 + Gdover ρ τ ^ 2 ≤ (τ ^ 2 + (1 + τ) ^ 2) * a ^ 2 := by nlinarith
    _ ≤ (2 + 4 * τ + 4 * τ ^ 2) * exp (-τ) := by
        have : τ ^ 2 + (1 + τ) ^ 2 ≤ 2 + 4 * τ + 4 * τ ^ 2 := by nlinarith
        exact mul_le_mul this ha2 (sq_nonneg a) (by positivity)
    _ ≤ 8 / τ := hkey

/-- Underdamped modes: `ℓ G² + Gd² ≤ 8/τ` for `τ ≥ 8`. -/
theorem ke_under (ω τ : ℝ) (hω : 0 < ω) (hτ : 8 ≤ τ) :
    (1 + ω ^ 2) * Gunder ω τ ^ 2 + Gdunder ω τ ^ 2 ≤ 8 / τ := by
  have hτ0 : 0 < τ := by linarith
  set e := exp (-τ) with he
  set s := sin (τ * ω) with hs
  set c := cos (τ * ω) with hc
  have he0 : 0 < e := exp_pos _
  have hs1 : |s| ≤ 1 := abs_sin_le_one _
  have hc1 : |c| ≤ 1 := abs_cos_le_one _
  have hsx : |s| ≤ τ * ω := by
    have h := abs_sin_le_abs (x := τ * ω)
    rw [abs_of_nonneg (mul_nonneg hτ0.le hω.le)] at h
    exact h
  have hq : |s / ω| ≤ τ := by rw [abs_div, abs_of_pos hω, div_le_iff₀ hω]; linarith
  have h1 : (1 + ω ^ 2) * Gunder ω τ ^ 2 ≤ e ^ 2 * (τ ^ 2 + 1) := by
    have : (1 + ω ^ 2) * Gunder ω τ ^ 2 = e ^ 2 * ((s / ω) ^ 2 + s ^ 2) := by
      have e1 : Gunder ω τ = e * s / ω := rfl
      rw [e1]; field_simp
    rw [this]
    have a1 : (s / ω) ^ 2 ≤ τ ^ 2 := by
      have := sq_le_sq' (abs_le.1 hq).1 (abs_le.1 hq).2; linarith
    have a2 : s ^ 2 ≤ 1 := by have := sq_le_sq' (abs_le.1 hs1).1 (abs_le.1 hs1).2; linarith
    nlinarith [sq_nonneg e]
  have h2 : Gdunder ω τ ^ 2 ≤ e ^ 2 * (1 + τ) ^ 2 := by
    have : |c - s / ω| ≤ 1 + τ := (abs_sub _ _).trans (by linarith)
    have := sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
    have e1 : Gdunder ω τ = e * (c - s / ω) := rfl
    rw [e1, mul_pow]; nlinarith [sq_nonneg e]
  have he2 : e ^ 2 ≤ e := by
    have : e ≤ 1 := exp_le_one_iff.2 (by linarith)
    nlinarith
  have hkey := poly_exp_neg_le τ hτ
  calc (1 + ω ^ 2) * Gunder ω τ ^ 2 + Gdunder ω τ ^ 2 ≤ e ^ 2 * (τ ^ 2 + 1 + (1 + τ) ^ 2) := by nlinarith
    _ ≤ e * (2 + 4 * τ + 4 * τ ^ 2) := by
        have : τ ^ 2 + 1 + (1 + τ) ^ 2 ≤ 2 + 4 * τ + 4 * τ ^ 2 := by nlinarith
        exact mul_le_mul he2 this (by positivity) he0.le
    _ ≤ 8 / τ := by rw [mul_comm]; exact hkey

/-- Critical modes: `G² + Gd² ≤ 8/τ` for `τ ≥ 8`. -/
theorem ke_crit (τ : ℝ) (hτ : 8 ≤ τ) : 1 * Gcrit τ ^ 2 + Gdcrit τ ^ 2 ≤ 8 / τ := by
  have hτ0 : 0 < τ := by linarith
  set e := exp (-τ) with he
  have he0 : 0 < e := exp_pos _
  have he2 : e ^ 2 ≤ e := by
    have : e ≤ 1 := exp_le_one_iff.2 (by linarith)
    nlinarith
  have hkey := poly_exp_neg_le τ hτ
  show 1 * (τ * e) ^ 2 + ((1 - τ) * e) ^ 2 ≤ 8 / τ
  calc 1 * (τ * e) ^ 2 + ((1 - τ) * e) ^ 2 = e ^ 2 * (τ ^ 2 + (1 - τ) ^ 2) := by ring
    _ ≤ e * (2 + 4 * τ + 4 * τ ^ 2) := by
        have : τ ^ 2 + (1 - τ) ^ 2 ≤ 2 + 4 * τ + 4 * τ ^ 2 := by nlinarith
        exact mul_le_mul he2 this (by positivity) he0.le
    _ ≤ 8 / τ := by rw [mul_comm]; exact hkey

/-- Every mode: the kinetic-energy fraction `ℓ G² + Gd²` is at most `8/τ` once `τ ≥ 8`. -/
theorem ke_all (τ : ℝ) (hτ : 8 ≤ τ) :
    (∀ ρ, 0 < ρ → ρ ≤ 1 → (1 - ρ ^ 2) * Gover ρ τ ^ 2 + Gdover ρ τ ^ 2 ≤ 8 / τ) ∧
    (1 * Gcrit τ ^ 2 + Gdcrit τ ^ 2 ≤ 8 / τ) ∧
    (∀ ω, 0 < ω → (1 + ω ^ 2) * Gunder ω τ ^ 2 + Gdunder ω τ ^ 2 ≤ 8 / τ) := by
  have hτ0 : 0 < τ := by linarith
  refine ⟨fun ρ h0 h1 => ?_, ke_crit τ hτ, fun ω h => ke_under ω τ h hτ⟩
  rcases lt_or_ge ρ (1 / 2) with h | h
  · exact ke_over_small ρ τ h0 h hτ
  · exact (ke_over_large ρ τ h h1 hτ0).trans (div_le_div_of_nonneg_right (by norm_num) hτ0.le)

end DampedOsc
