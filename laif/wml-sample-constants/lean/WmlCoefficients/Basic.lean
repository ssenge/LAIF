import Mathlib

/-!
# The coefficients of one wave matrix Lindbladization step

One step is Φ_Δ = id + Δℒ + c_J J + c_A A + c_D D₁∘J with
c_A = (2/d) u² φ(u), c_D = (d u²/(d²−2)) (4(d²−1) φ(v)/d² − 2φ(u)), c_J = −Δ²(d²−1) φ(v)/d − 2c_D/d²,
u = Δd/2, v = Δ(d − 1/d) and φ(z) = (e^{−z} − 1 + z)/z². This file proves the scalar steps of the per-step bound
½‖e^{Δℒ} − Φ_Δ‖⋄ ≤ Δ² κ (d/2 + e^{1/d} κ), κ = ‖L‖∞² ≤ 1, for d ≥ 2 and Δ ≤ 1/(2d):

* `phi_pos`, `phi_le_half`, `phi_antitoneOn`, `phi_half_gt`: 0 < φ ≤ 1/2 on (0, ∞), φ is antitone there, and φ(1/2) > 1/3.
* `cA_pos`, `cA_le`, `cD_pos`, `cD_le`, `cJ_neg`, `neg_cJ_le`: 0 < c_A, c_D ≤ dΔ²/4 and 0 < −c_J ≤ dΔ²/2.
* `exp_tail`: e^x − 1 − x ≤ x² e^x/2 for x ≥ 0.
* `step_bound`: the sum of these bounds, with the tail at x = 2Δκ, is at most Δ² κ (d/2 + e^{1/d} κ).

The diamond-norm bounds on the maps J, A and D₁∘J and the series bound on the tail are not part of this file.
-/

namespace WmlCoefficients

open Real Set

/-- A function with nonnegative derivative on (0, ∞) and value 0 at 0 is nonnegative on [0, ∞). -/
theorem nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hd : ∀ x, 0 < x → 0 ≤ f' x) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hf x).continuousAt.continuousWithinAt
    · exact fun x _ => (hf x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x).deriv]
      exact hd x hx
  intro x hx
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  linarith

theorem exp_mul_exp_neg (x : ℝ) : exp x * exp (-x) = 1 := by
  rw [← exp_add]; simp

/-- e^{−z} ≤ 1 − z + z²/2 for z ≥ 0. -/
theorem exp_neg_le_quad (z : ℝ) (hz : 0 ≤ z) : exp (-z) ≤ 1 - z + z ^ 2 / 2 := by
  have key := nonneg_of_hasDerivAt (f := fun z => 1 - z + z ^ 2 / 2 - exp (-z))
    (f' := fun z => -1 + z + exp (-z))
    (by
      intro x
      have h := (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_neg x).exp)
      convert h using 1
      (try simp); (try ring))
    (by simp)
    (by
      intro x _
      have := add_one_le_exp (-x)
      linarith) z hz
  (try simp at key); linarith

/-- e^x − 1 − x ≤ x² e^x/2 for x ≥ 0. -/
theorem exp_tail (x : ℝ) (hx : 0 ≤ x) : exp x - 1 - x ≤ x ^ 2 * exp x / 2 := by
  have key := nonneg_of_hasDerivAt (f := fun x => x ^ 2 * exp x / 2 - exp x + 1 + x)
    (f' := fun x => x * exp x + x ^ 2 * exp x / 2 - exp x + 1)
    (by
      intro y
      have h := (((((hasDerivAt_pow 2 y).mul (hasDerivAt_exp y)).div_const 2).sub (hasDerivAt_exp y)).add
        (hasDerivAt_const y (1 : ℝ))).add (hasDerivAt_id' y)
      convert h using 1
      (try simp); (try ring))
    (by simp)
    (by
      intro y _
      have h1 := add_one_le_exp (-y)
      have h2 := exp_mul_exp_neg y
      have hp := exp_pos y
      nlinarith [mul_le_mul_of_nonneg_left h1 hp.le, sq_nonneg y, mul_nonneg (sq_nonneg y) hp.le]) x hx
  (try simp at key); linarith

/-- (z + 2) e^{−z} ≥ 2 − z for z ≥ 0. -/
theorem pade_lower (z : ℝ) (hz : 0 ≤ z) : 2 - z ≤ (z + 2) * exp (-z) := by
  have key := nonneg_of_hasDerivAt (f := fun z => (z + 2) * exp (-z) + z - 2)
    (f' := fun z => 1 - (z + 1) * exp (-z))
    (by
      intro y
      have h := ((((hasDerivAt_id' y).add (hasDerivAt_const y (2 : ℝ))).mul ((hasDerivAt_neg y).exp)).add
        (hasDerivAt_id' y)).sub (hasDerivAt_const y (2 : ℝ))
      convert h using 1
      (try simp); (try ring))
    (by simp)
    (by
      intro y _
      have h1 := add_one_le_exp y
      have h2 := exp_mul_exp_neg y
      have hp := exp_pos (-y)
      nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]) z hz
  (try simp at key); linarith

/-- φ(z) = (e^{−z} − 1 + z)/z². -/
noncomputable def phi (z : ℝ) : ℝ := (exp (-z) - 1 + z) / z ^ 2

theorem phi_pos (z : ℝ) (hz : 0 < z) : 0 < phi z := by
  unfold phi
  have := add_one_lt_exp (neg_ne_zero.2 hz.ne')
  apply div_pos _ (by positivity)
  linarith

theorem phi_le_half (z : ℝ) (hz : 0 < z) : phi z ≤ 1 / 2 := by
  unfold phi
  rw [div_le_iff₀ (by positivity)]
  have := exp_neg_le_quad z hz.le
  linarith

theorem phi_hasDerivAt (z : ℝ) (hz : 0 < z) :
    HasDerivAt phi (((-exp (-z) + 1) * z ^ 2 - (exp (-z) - 1 + z) * (2 * z)) / (z ^ 2) ^ 2) z := by
  have hc : HasDerivAt (fun y => exp (-y) - 1 + y) (-exp (-z) + 1) z := by
    have h := (((hasDerivAt_neg z).exp).sub (hasDerivAt_const z (1 : ℝ))).add (hasDerivAt_id' z)
    convert h using 1; ring
  have hd : HasDerivAt (fun y => y ^ 2) (2 * z) z := by
    convert hasDerivAt_pow 2 z using 1; ring
  exact hc.div hd (by positivity)

theorem phi_antitoneOn : AntitoneOn phi (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (phi_hasDerivAt x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun x hx => (phi_hasDerivAt x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(phi_hasDerivAt x hx).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hp := pade_lower x (le_of_lt hx)
    have hx' : 0 < x := hx
    -- numerator = x (2 − x − (x + 2) e^{−x}) ≤ 0
    have : (-exp (-x) + 1) * x ^ 2 - (exp (-x) - 1 + x) * (2 * x) = x * (2 - x - (x + 2) * exp (-x)) := by
      ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hx'.le (by linarith)

theorem phi_half_gt : 1 / 3 < phi (1 / 2) := by
  unfold phi
  have h1 : exp (-(1 / 2 : ℝ)) * exp (-(1 / 2)) = exp (-1) := by rw [← exp_add]; norm_num
  have h2 := exp_neg_one_gt_d9
  have hp := exp_pos (-(1 / 2 : ℝ))
  have : (7 : ℝ) / 12 < exp (-(1 / 2)) := by nlinarith
  rw [lt_div_iff₀ (by norm_num)]
  nlinarith

/-- Coefficients of the step. -/
noncomputable def cA (d Δ : ℝ) : ℝ := (2 / d) * (Δ * d / 2) ^ 2 * phi (Δ * d / 2)

noncomputable def cD (d Δ : ℝ) : ℝ :=
  (d * (Δ * d / 2) ^ 2 / (d ^ 2 - 2)) * (4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2 - 2 * phi (Δ * d / 2))

noncomputable def cJ (d Δ : ℝ) : ℝ := -Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d - 2 * cD d Δ / d ^ 2

section coefficients

variable {d Δ : ℝ} (hd : 2 ≤ d) (hΔ : 0 < Δ) (hΔd : Δ ≤ 1 / (2 * d))
include hd hΔ hΔd

theorem u_pos : 0 < Δ * d / 2 := by have : 0 < d := by linarith
                                    positivity

theorem u_le_v : Δ * d / 2 ≤ Δ * (d - 1 / d) := by
  have hd0 : 0 < d := by linarith
  have : 1 / d ≤ d / 2 := by rw [div_le_div_iff₀ hd0 (by norm_num)]; nlinarith
  nlinarith

theorem v_le_half : Δ * (d - 1 / d) ≤ 1 / 2 := by
  have hd0 : 0 < d := by linarith
  have h1 : 0 < 1 / d := by positivity
  have h2 : Δ * d ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hΔd; nlinarith
  nlinarith

theorem cA_pos : 0 < cA d Δ := by
  have hd0 : 0 < d := by linarith
  have := phi_pos _ (u_pos hd hΔ hΔd)
  unfold cA; positivity

theorem cA_le : cA d Δ ≤ d * Δ ^ 2 / 4 := by
  have hd0 : 0 < d := by linarith
  have h := phi_le_half _ (u_pos hd hΔ hΔd)
  unfold cA
  have e : d * Δ ^ 2 / 4 = (2 / d) * (Δ * d / 2) ^ 2 * (1 / 2) := by field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem bracket_pos : 0 < 4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2 - 2 * phi (Δ * d / 2) := by
  have hd0 : 0 < d := by linarith
  have hu := u_pos hd hΔ hΔd
  have hv : 0 < Δ * (d - 1 / d) := lt_of_lt_of_le hu (u_le_v hd hΔ hΔd)
  have h1 : phi (1 / 2) ≤ phi (Δ * (d - 1 / d)) :=
    phi_antitoneOn hv (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0) (v_le_half hd hΔ hΔd)
  have h2 := phi_half_gt
  have h3 := phi_le_half _ hu
  have hq : 3 / 4 ≤ (d ^ 2 - 1) / d ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have : 4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2 = 4 * ((d ^ 2 - 1) / d ^ 2) * phi (Δ * (d - 1 / d)) := by
    field_simp
  rw [this]
  nlinarith

theorem cD_pos : 0 < cD d Δ := by
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d ^ 2 - 2 := by nlinarith
  have := bracket_pos hd hΔ hΔd
  unfold cD
  exact mul_pos (div_pos (by positivity) hd2) this

theorem cD_le : cD d Δ ≤ d * Δ ^ 2 / 4 := by
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d ^ 2 - 2 := by nlinarith
  have hu := u_pos hd hΔ hΔd
  have hv : 0 < Δ * (d - 1 / d) := lt_of_lt_of_le hu (u_le_v hd hΔ hΔd)
  have hmono : phi (Δ * (d - 1 / d)) ≤ phi (Δ * d / 2) := phi_antitoneOn hu hv (u_le_v hd hΔ hΔd)
  have hh := phi_le_half _ hu
  have hpv := phi_pos _ hv
  -- d² · bracket = 4(d²−1)φ(v) − 2d²φ(u) ≤ (2d² − 4)φ(u) ≤ d² − 2
  have hb : d ^ 2 * (4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2 - 2 * phi (Δ * d / 2)) ≤ d ^ 2 - 2 := by
    have e : d ^ 2 * (4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2 - 2 * phi (Δ * d / 2))
        = 4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) - 2 * d ^ 2 * phi (Δ * d / 2) := by field_simp
    rw [e]
    have hd1 : 0 ≤ d ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hmono hd1]
  unfold cD
  have e2 : d * (Δ * d / 2) ^ 2 / (d ^ 2 - 2) = (d * Δ ^ 2 / 4) * (d ^ 2 / (d ^ 2 - 2)) := by
    field_simp; try norm_num
  rw [e2, mul_assoc]
  have : d ^ 2 / (d ^ 2 - 2) * (4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2 - 2 * phi (Δ * d / 2)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hd2]; exact hb
  calc d * Δ ^ 2 / 4 * (d ^ 2 / (d ^ 2 - 2) * (4 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ^ 2
          - 2 * phi (Δ * d / 2)))
      ≤ d * Δ ^ 2 / 4 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = d * Δ ^ 2 / 4 := by ring

theorem cJ_neg : cJ d Δ < 0 := by
  have hd0 : 0 < d := by linarith
  have hu := u_pos hd hΔ hΔd
  have hv : 0 < Δ * (d - 1 / d) := lt_of_lt_of_le hu (u_le_v hd hΔ hΔd)
  have hpv := phi_pos _ hv
  have hD := cD_pos hd hΔ hΔd
  have hd1 : 0 < d ^ 2 - 1 := by nlinarith
  unfold cJ
  have : 0 < Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d := by positivity
  have : 0 < 2 * cD d Δ / d ^ 2 := by positivity
  have e : -Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d
      = -(Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d) := by ring
  linarith

theorem neg_cJ_le : -cJ d Δ ≤ d * Δ ^ 2 / 2 := by
  have hd0 : 0 < d := by linarith
  have hu := u_pos hd hΔ hΔd
  have hv : 0 < Δ * (d - 1 / d) := lt_of_lt_of_le hu (u_le_v hd hΔ hΔd)
  have hh := phi_le_half _ hv
  have hD := cD_le hd hΔ hΔd
  have hd1 : 0 ≤ d ^ 2 - 1 := by nlinarith
  unfold cJ
  have h1 : Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d ≤ Δ ^ 2 * (d ^ 2 - 1) * (1 / 2) / d := by
    apply div_le_div_of_nonneg_right _ hd0.le
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have h2 : 2 * cD d Δ / d ^ 2 ≤ 2 * (d * Δ ^ 2 / 4) / d ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have e : Δ ^ 2 * (d ^ 2 - 1) * (1 / 2) / d + 2 * (d * Δ ^ 2 / 4) / d ^ 2 = d * Δ ^ 2 / 2 := by
    field_simp; ring
  have e2 : -(-Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d - 2 * cD d Δ / d ^ 2)
      = Δ ^ 2 * (d ^ 2 - 1) * phi (Δ * (d - 1 / d)) / d + 2 * cD d Δ / d ^ 2 := by ring
  rw [e2]; linarith

/-- The per-step bound: with κ = ‖L‖∞² ∈ (0, 1] and the tail at x = 2Δκ,
½((−c_J + c_A + c_D) κ + (e^x − 1 − x)) ≤ Δ² κ (d/2 + e^{1/d} κ). -/
theorem step_bound (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ((-cJ d Δ + cA d Δ + cD d Δ) * κ + (exp (2 * Δ * κ) - 1 - 2 * Δ * κ)) / 2
      ≤ Δ ^ 2 * κ * (d / 2 + exp (1 / d) * κ) := by
  have hd0 : 0 < d := by linarith
  have hJ := neg_cJ_le hd hΔ hΔd
  have hA := cA_le hd hΔ hΔd
  have hD := cD_le hd hΔ hΔd
  have hx0 : 0 ≤ 2 * Δ * κ := by positivity
  have hT := exp_tail (2 * Δ * κ) hx0
  have hx1 : 2 * Δ * κ ≤ 1 / d := by
    have : Δ * d ≤ 1 / 2 := by rw [le_div_iff₀ (by positivity)] at hΔd; nlinarith
    rw [le_div_iff₀ hd0]; nlinarith
  have hE : exp (2 * Δ * κ) ≤ exp (1 / d) := exp_le_exp.2 hx1
  have h1 : (-cJ d Δ + cA d Δ + cD d Δ) * κ ≤ d * Δ ^ 2 * κ :=
    by nlinarith
  have h2 : (2 * Δ * κ) ^ 2 * exp (2 * Δ * κ) / 2 ≤ 2 * Δ ^ 2 * κ ^ 2 * exp (1 / d) := by
    have : 0 ≤ (2 * Δ * κ) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hE this]
  nlinarith

end coefficients

/-! ### Content of the statements -/

/-- The hypotheses of `step_bound` hold at d = 2, Δ = 1/4, κ = 1, and its left-hand side is positive there. -/
theorem step_bound_satisfiable :
    0 < ((-cJ 2 (1 / 4) + cA 2 (1 / 4) + cD 2 (1 / 4)) * 1 + (exp (2 * (1 / 4) * 1) - 1 - 2 * (1 / 4) * 1)) / 2 := by
  have h1 := cJ_neg (d := 2) (Δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 := cA_pos (d := 2) (Δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  have h3 := cD_pos (d := 2) (Δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  have h4 := exp_tail (2 * (1 / 4) * 1) (by norm_num)
  have h5 := add_one_le_exp (2 * (1 / 4) * (1 : ℝ))
  nlinarith

/-- φ is not constant: φ(1/2) < φ at a smaller argument is not needed, but φ(1/2) < 1/2. -/
theorem phi_half_lt : phi (1 / 2) < 1 / 2 := by
  unfold phi
  have h1 : exp (-(1 / 2 : ℝ)) * exp (-(1 / 2)) = exp (-1) := by rw [← exp_add]; norm_num
  have h2 := exp_neg_one_lt_d9
  have hp := exp_pos (-(1 / 2 : ℝ))
  have : exp (-(1 / 2)) < (5 : ℝ) / 8 := by nlinarith
  rw [div_lt_iff₀ (by norm_num)]
  nlinarith

end WmlCoefficients
