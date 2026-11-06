import DampedOsc.Walk

/-!
# Damping by walls

If `y` solves the undamped equation `ÿ = -A y`, then `x(t) = e^{-γt} y(t)` solves the damped equation
`ẍ + 2γ ẋ + (A + γ²) x = 0` with velocity `ẋ = e^{-γt} (ẏ - γ y)`. For a network with generator
`A = M⁻¹K` this says: adding a wall of stiffness `m_j γ²` at every mass and damping `2γ M` turns the undamped
trajectory into `e^{-γt}` times itself (for `x(0) = 0` the initial data agree).

This file also proves the initial values of the displacement response `F = Gd + 2G` and the series of
`Walk.lean` in the critical case.
-/

open Real

namespace DampedOsc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `x = e^{-γt} y` with `ÿ = -A y` solves the damped equation with walls `γ²`. -/
theorem damped_of_undamped (A : E →L[ℝ] E) (γ : ℝ) (y y' : ℝ → E)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hy' : ∀ t, HasDerivAt y' (-A (y t)) t) (t : ℝ) :
    HasDerivAt (fun s => exp (-(s * γ)) • y s) (exp (-(t * γ)) • (y' t - γ • y t)) t ∧
    HasDerivAt (fun s => exp (-(s * γ)) • (y' s - γ • y s))
      (-(2 * γ) • (exp (-(t * γ)) • (y' t - γ • y t)) -
        (A (exp (-(t * γ)) • y t) + γ ^ 2 • (exp (-(t * γ)) • y t))) t := by
  constructor
  · have h := (hasDerivAt_exp_neg_mul γ t).smul (hy t)
    convert h using 1
    module
  · have h := (hasDerivAt_exp_neg_mul γ t).smul ((hy' t).sub ((hy t).const_smul γ))
    convert h using 1
    rw [map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply]
    module

/-- The displacement response starts at one: `F(0) = Gd(0) + 2G(0) = 1` (overdamped). -/
theorem Fover_zero (ρ : ℝ) (hρ : ρ ≠ 0) : Gdover ρ 0 + 2 * Gover ρ 0 = 1 := by
  unfold Gdover Gover; simp; field_simp; ring

/-- `F' = G'' + 2G' = -ℓ G`, so `F'(0) = 0` (overdamped, `ℓ = 1 - ρ²`). -/
theorem Fover_deriv (ρ τ : ℝ) (hρ : ρ ≠ 0) :
    HasDerivAt (fun s => Gdover ρ s + 2 * Gover ρ s) (-(1 - ρ ^ 2) * Gover ρ τ) τ := by
  have h := (Gdover_hasDerivAt ρ τ).add ((Gover_hasDerivAt ρ τ).const_mul 2)
  have e := Gover_ode ρ τ hρ
  convert h using 1
  linarith

/-- `F(0) = 1` (underdamped). -/
theorem Funder_zero (ω : ℝ) : Gdunder ω 0 + 2 * Gunder ω 0 = 1 := by
  unfold Gdunder Gunder; simp

/-- `F(0) = 1` (critical). -/
theorem Fcrit_zero : Gdcrit 0 + 2 * Gcrit 0 = 1 := by
  unfold Gdcrit Gcrit; simp

/-- Critical case `β = 0` of the series: only the `k = 0` weight survives, `w₀(τ) = (1 + τ) e^{-τ} = F`. -/
theorem hasSum_wx_crit (τ : ℝ) :
    HasSum (fun k => wx τ k * (0 : ℝ) ^ k) (Gdcrit τ + 2 * Gcrit τ) := by
  have h := hasSum_ite_eq (0 : ℕ) (wx τ 0)
  convert h using 1
  · funext k
    rcases k with _ | k <;> simp
  · unfold Gdcrit Gcrit wx; simp; ring

end DampedOsc
