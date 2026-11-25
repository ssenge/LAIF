import HarvestThreshold.Model

/-!
# Uniqueness of the critical point for general one-dimensional diffusions

Population `dX = (f(X) - h) dt + v(X) dB` on `(0, ∞)` with a harvesting rate `0 ≤ h ≤ k(X)`. The
threshold strategy harvests `k(X)` above `η` and nothing below. With
`m = exp(∫_{x₁}^x 2f/v²) / v²`, `m₀ = m exp(-∫_{x₁}^x 2k/v²)` and `λ = m / m₀`, the stationary mean
harvest of the threshold strategy is `H(η) = λ R / (A + λ B)` with `A = ∫_0^η m`, `B = ∫_η^∞ m₀`,
`R = ∫_η^∞ k m₀`.

Main result (`Assumption.critical_point_unique`): if the integrals are finite, the boundary terms
`v² m` at `0` and `v² m₀` at `∞` vanish, and `f` is unimodal (at each `η`, `f < f(η)` on `(0, η)` or
on `(η, ∞)`), then `H` has at most one critical point in `(0, ∞)`. No integrability of `m₀` near `0`
and no condition on the type of the boundary at `∞` is assumed.
-/

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace HarvestThreshold

/-- Coefficients of the controlled diffusion: drift `f`, noise `v > 0`, cap `k > 0`, continuous on
`(0, ∞)`, and a reference point `x₁ > 0`. -/
structure Diffusion where
  f : ℝ → ℝ
  v : ℝ → ℝ
  k : ℝ → ℝ
  x₁ : ℝ
  hx₁ : 0 < x₁
  hf : ContinuousOn f (Ioi 0)
  hv : ContinuousOn v (Ioi 0)
  hk : ContinuousOn k (Ioi 0)
  hvpos : ∀ x, 0 < x → 0 < v x
  hkpos : ∀ x, 0 < x → 0 < k x

namespace Diffusion

variable (d : Diffusion)

/-- `Φ(x) = ∫_{x₁}^x 2 f / v²`. -/
noncomputable def Φ (x : ℝ) : ℝ := ∫ z in d.x₁..x, 2 * d.f z / d.v z ^ 2
/-- `Ψ(x) = ∫_{x₁}^x 2 k / v²`. -/
noncomputable def Ψ (x : ℝ) : ℝ := ∫ z in d.x₁..x, 2 * d.k z / d.v z ^ 2
/-- Speed density of the unharvested process. -/
noncomputable def m (x : ℝ) : ℝ := exp (d.Φ x) / d.v x ^ 2
/-- Speed density of the process harvested at full capacity. -/
noncomputable def m₀ (x : ℝ) : ℝ := d.m x * exp (-d.Ψ x)
/-- `λ = m / m₀`. -/
noncomputable def lam (x : ℝ) : ℝ := exp (d.Ψ x)

noncomputable def A (η : ℝ) : ℝ := ∫ y in (0 : ℝ)..η, d.m y
noncomputable def P (η : ℝ) : ℝ := ∫ y in (0 : ℝ)..η, d.f y * d.m y
noncomputable def B (η : ℝ) : ℝ := ∫ y in Ioi η, d.m₀ y
noncomputable def Q (η : ℝ) : ℝ := ∫ y in Ioi η, d.f y * d.m₀ y
noncomputable def R (η : ℝ) : ℝ := ∫ y in Ioi η, d.k y * d.m₀ y

/-- Stationary mean harvest of the threshold strategy with threshold `η`. -/
noncomputable def yieldH (η : ℝ) : ℝ := d.lam η * d.R η / (d.A η + d.lam η * d.B η)

lemma continuousOn_ratio {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) :
    ContinuousOn (fun z => 2 * g z / d.v z ^ 2) (Ioi 0) :=
  (continuousOn_const.mul hg).div (d.hv.pow 2) fun z hz => (pow_pos (d.hvpos z hz) 2).ne'

lemma hasDerivAt_integral {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => ∫ z in d.x₁..x, 2 * g z / d.v z ^ 2) (2 * g x / d.v x ^ 2) x := by
  have hc := d.continuousOn_ratio hg
  have hsub : uIcc d.x₁ x ⊆ Ioi 0 := fun z hz =>
    lt_of_lt_of_le (lt_inf_iff.mpr ⟨d.hx₁, hx⟩) hz.1
  exact integral_hasDerivAt_right ((hc.mono hsub).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hc.continuousAt (Ioi_mem_nhds hx))

lemma hasDerivAt_Φ {x : ℝ} (hx : 0 < x) : HasDerivAt d.Φ (2 * d.f x / d.v x ^ 2) x :=
  d.hasDerivAt_integral d.hf hx

lemma hasDerivAt_Ψ {x : ℝ} (hx : 0 < x) : HasDerivAt d.Ψ (2 * d.k x / d.v x ^ 2) x :=
  d.hasDerivAt_integral d.hk hx

lemma m_pos {x : ℝ} (hx : 0 < x) : 0 < d.m x :=
  div_pos (exp_pos _) (pow_pos (d.hvpos x hx) 2)
lemma m₀_pos {x : ℝ} (hx : 0 < x) : 0 < d.m₀ x := mul_pos (d.m_pos hx) (exp_pos _)
lemma lam_pos (x : ℝ) : 0 < d.lam x := exp_pos _

lemma m_eq_lam_mul (x : ℝ) : d.m x = d.lam x * d.m₀ x := by
  unfold m₀ lam
  rw [mul_comm (d.m x), ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

lemma continuousOn_m : ContinuousOn d.m (Ioi 0) := by
  have hΦ : ContinuousOn d.Φ (Ioi 0) := fun x hx => (d.hasDerivAt_Φ hx).continuousAt.continuousWithinAt
  exact (continuous_exp.comp_continuousOn hΦ).div (d.hv.pow 2)
    fun z hz => (pow_pos (d.hvpos z hz) 2).ne'

lemma continuousOn_m₀ : ContinuousOn d.m₀ (Ioi 0) := by
  have hΨ : ContinuousOn d.Ψ (Ioi 0) := fun x hx => (d.hasDerivAt_Ψ hx).continuousAt.continuousWithinAt
  exact d.continuousOn_m.mul (continuous_exp.comp_continuousOn hΨ.neg)

/-- `v² m = exp Φ` on `(0, ∞)`. -/
lemma v2m {x : ℝ} (hx : 0 < x) : d.v x ^ 2 * d.m x = exp (d.Φ x) := by
  unfold m
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (pow_pos (d.hvpos x hx) 2).ne', mul_one]

/-- `v² m₀ = exp (Φ - Ψ)` on `(0, ∞)`. -/
lemma v2m₀ {x : ℝ} (hx : 0 < x) : d.v x ^ 2 * d.m₀ x = exp (d.Φ x - d.Ψ x) := by
  unfold m₀; rw [← mul_assoc, d.v2m hx, ← exp_add, sub_eq_add_neg]

lemma hasDerivAt_v2m {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => exp (d.Φ x)) (2 * (d.f x * d.m x)) x := by
  convert (d.hasDerivAt_Φ hx).exp using 1
  unfold m; ring

lemma hasDerivAt_v2m₀ {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => exp (d.Φ x - d.Ψ x)) (2 * (d.f x * d.m₀ x - d.k x * d.m₀ x)) x := by
  convert ((d.hasDerivAt_Φ hx).sub (d.hasDerivAt_Ψ hx)).exp using 1
  simp only [Pi.sub_apply]
  unfold m₀ m
  rw [sub_eq_add_neg (d.Φ x), exp_add]
  ring

lemma hasDerivAt_lam {x : ℝ} (hx : 0 < x) :
    HasDerivAt d.lam (d.lam x * (2 * d.k x / d.v x ^ 2)) x := by
  exact (d.hasDerivAt_Ψ hx).exp

/-- **Assumption 2.1**: finite integrals, vanishing boundary terms, and unimodal growth. -/
structure Assumption : Prop where
  intA : ∀ η, 0 < η → IntervalIntegrable d.m volume 0 η
  intP : ∀ η, 0 < η → IntervalIntegrable (fun y => d.f y * d.m y) volume 0 η
  intB : ∀ η, 0 < η → IntegrableOn d.m₀ (Ioi η)
  intQ : ∀ η, 0 < η → IntegrableOn (fun y => d.f y * d.m₀ y) (Ioi η)
  intR : ∀ η, 0 < η → IntegrableOn (fun y => d.k y * d.m₀ y) (Ioi η)
  lim0 : Tendsto (fun x => exp (d.Φ x)) (𝓝[>] 0) (𝓝 0)
  limInf : Tendsto (fun x => exp (d.Φ x - d.Ψ x)) atTop (𝓝 0)
  shape : ∀ η, 0 < η → (∀ y ∈ Ioo 0 η, d.f y < d.f η) ∨ (∀ y, η < y → d.f y < d.f η)

/-- A strictly increasing, then strictly decreasing growth function meets the shape condition. -/
lemma shape_of_unimodal {f : ℝ → ℝ} {xp : ℝ} (hinc : StrictMonoOn f (Ioc 0 xp))
    (hdec : StrictAntiOn f (Ici xp)) (η : ℝ) (hη : 0 < η) :
    (∀ y ∈ Ioo 0 η, f y < f η) ∨ (∀ y, η < y → f y < f η) := by
  rcases le_or_gt η xp with h | h
  · exact Or.inl fun y hy => hinc ⟨hy.1, (hy.2.trans_le h).le⟩ ⟨hη, h⟩ hy.2
  · exact Or.inr fun y hy => hdec (mem_Ici.mpr h.le) (mem_Ici.mpr (h.trans hy).le) hy

/-- The shape condition for a strictly increasing growth function. -/
lemma shape_of_strictMonoOn {f : ℝ → ℝ} (hinc : StrictMonoOn f (Ioi 0)) (η : ℝ) (hη : 0 < η) :
    (∀ y ∈ Ioo 0 η, f y < f η) ∨ (∀ y, η < y → f y < f η) :=
  Or.inl fun y hy => hinc hy.1 hη hy.2

namespace Assumption

variable {d} (h : d.Assumption)
include h

lemma A_pos {η : ℝ} (hη : 0 < η) : 0 < d.A η :=
  intervalIntegral_pos_of_pos_on (h.intA η hη) (fun y hy => d.m_pos hy.1) hη

lemma B_pos {η : ℝ} (hη : 0 < η) : 0 < d.B η :=
  Params.setIntegral_Ioi_pos (h.intB η hη) fun y hy => d.m₀_pos (hη.trans hy)

lemma hasDerivAt_left {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (hint : ∀ η, 0 < η → IntervalIntegrable g volume 0 η) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, g y) (g η) η :=
  integral_hasDerivAt_right (hint η hη) (hg.stronglyMeasurableAtFilter isOpen_Ioi η hη)
    (hg.continuousAt (Ioi_mem_nhds hη))

lemma hasDerivAt_A {η : ℝ} (hη : 0 < η) : HasDerivAt d.A (d.m η) η :=
  hasDerivAt_left h d.continuousOn_m h.intA hη

lemma hasDerivAt_P {η : ℝ} (hη : 0 < η) : HasDerivAt d.P (d.f η * d.m η) η :=
  hasDerivAt_left h (d.hf.mul d.continuousOn_m) h.intP hη

lemma hasDerivAt_B {η : ℝ} (hη : 0 < η) : HasDerivAt d.B (-d.m₀ η) η :=
  Params.hasDerivAt_tail d.continuousOn_m₀ h.intB hη

lemma hasDerivAt_Q {η : ℝ} (hη : 0 < η) : HasDerivAt d.Q (-(d.f η * d.m₀ η)) η :=
  Params.hasDerivAt_tail (d.hf.mul d.continuousOn_m₀) h.intQ hη

/-- Left identity: `2 P(η) = v(η)² m(η)`. -/
lemma two_P {η : ℝ} (hη : 0 < η) : 2 * d.P η = exp (d.Φ η) := by
  have hII : IntegrableOn (fun y => 2 * (d.f y * d.m y)) (Icc 0 η) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hη.le).1 (h.intP η hη)).const_mul 2
  have hε : ∀ ε ∈ Ioo 0 η, ∫ y in ε..η, 2 * (d.f y * d.m y) = exp (d.Φ η) - exp (d.Φ ε) := by
    intro ε hε
    refine integral_eq_sub_of_hasDerivAt (fun x hx => d.hasDerivAt_v2m ?_) ?_
    · rw [uIcc_of_le hε.2.le] at hx; exact hε.1.trans_le hx.1
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hε.2.le).2
        (hII.mono_set (Icc_subset_Icc hε.1.le le_rfl))
  have hcont : ContinuousWithinAt (fun ε => ∫ y in ε..η, 2 * (d.f y * d.m y)) (Icc 0 η) 0 := by
    have := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (a := 0) (b := η)
      (by rw [uIcc_of_le hη.le]; exact hII)
    rw [uIcc_of_le hη.le] at this
    exact this 0 (left_mem_Icc.mpr hη.le)
  have hlim1 : Tendsto (fun ε => ∫ y in ε..η, 2 * (d.f y * d.m y)) (𝓝[>] 0)
      (𝓝 (∫ y in (0 : ℝ)..η, 2 * (d.f y * d.m y))) :=
    hcont.mono_of_mem_nhdsWithin (mem_of_superset (Ioo_mem_nhdsGT hη) Ioo_subset_Icc_self)
  have hlim2 : Tendsto (fun ε => ∫ y in ε..η, 2 * (d.f y * d.m y)) (𝓝[>] 0)
      (𝓝 (exp (d.Φ η) - 0)) := by
    refine (tendsto_const_nhds.sub h.lim0).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hη] with ε hε' using (hε ε hε').symm
  have := tendsto_nhds_unique hlim1 hlim2
  rw [intervalIntegral.integral_const_mul, sub_zero] at this
  exact this

/-- Right identity: `2 (Q(η) - R(η)) = -v(η)² m₀(η)`. -/
lemma two_QR {η : ℝ} (hη : 0 < η) : 2 * (d.Q η - d.R η) = -exp (d.Φ η - d.Ψ η) := by
  have hF : ∀ y ∈ Ioi η, HasDerivAt (fun x => exp (d.Φ x - d.Ψ x))
      (2 * (d.f y * d.m₀ y - d.k y * d.m₀ y)) y := fun y hy => d.hasDerivAt_v2m₀ (hη.trans hy)
  have hcont : ContinuousWithinAt (fun x => exp (d.Φ x - d.Ψ x)) (Ici η) η :=
    (d.hasDerivAt_v2m₀ hη).continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun y => 2 * (d.f y * d.m₀ y - d.k y * d.m₀ y)) (Ioi η) :=
    ((h.intQ η hη).sub (h.intR η hη)).const_mul 2
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hF hint h.limInf
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub (h.intQ η hη) (h.intR η hη)]
    at this
  rw [Q, R, this, zero_sub]

/-- Lemma 2.2: the yield equals the stationary mean of the growth. -/
lemma yieldH_eq_mean {η : ℝ} (hη : 0 < η) :
    d.yieldH η = (d.P η + d.lam η * d.Q η) / (d.A η + d.lam η * d.B η) := by
  unfold yieldH
  congr 1
  have h1 := h.two_P hη
  have h2 := h.two_QR hη
  have hl : d.lam η * exp (d.Φ η - d.Ψ η) = exp (d.Φ η) := by
    unfold lam; rw [← exp_add]; congr 1; ring
  linear_combination (-1 / 2 : ℝ) * h1 + (-(d.lam η) / 2) * h2 + (1 / 2 : ℝ) * hl

/-- Mean growth below or above the threshold is below the growth at the threshold. -/
lemma mean_lt {η : ℝ} (hη : 0 < η) : d.P η / d.A η < d.f η ∨ d.Q η / d.B η < d.f η := by
  rcases h.shape η hη with hs | hs
  · left
    rw [div_lt_iff₀ (h.A_pos hη)]
    have hint : IntervalIntegrable (fun y => (d.f η - d.f y) * d.m y) volume 0 η := by
      have heq : (fun y => (d.f η - d.f y) * d.m y) = fun y => d.f η * d.m y - d.f y * d.m y := by
        funext y; ring
      rw [heq]; exact ((h.intA η hη).const_mul (d.f η)).sub (h.intP η hη)
    have hpos : 0 < ∫ y in (0 : ℝ)..η, (d.f η - d.f y) * d.m y :=
      intervalIntegral_pos_of_pos_on hint (fun y hy => mul_pos (sub_pos.mpr (hs y hy))
        (d.m_pos hy.1)) hη
    have heq : ∫ y in (0 : ℝ)..η, (d.f η - d.f y) * d.m y = d.f η * d.A η - d.P η := by
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub ((h.intA η hη).const_mul _) (h.intP η hη),
        intervalIntegral.integral_const_mul]
      rfl
    linarith
  · right
    rw [div_lt_iff₀ (h.B_pos hη)]
    have hint : IntegrableOn (fun y => (d.f η - d.f y) * d.m₀ y) (Ioi η) := by
      have := ((h.intB η hη).const_mul (d.f η)).sub (h.intQ η hη)
      exact IntegrableOn.congr_fun this (fun y _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioi
    have hpos : 0 < ∫ y in Ioi η, (d.f η - d.f y) * d.m₀ y :=
      Params.setIntegral_Ioi_pos hint fun y hy =>
        mul_pos (sub_pos.mpr (hs y hy)) (d.m₀_pos (hη.trans hy))
    have heq : ∫ y in Ioi η, (d.f η - d.f y) * d.m₀ y = d.f η * d.B η - d.Q η := by
      simp only [sub_mul]
      rw [MeasureTheory.integral_sub ((h.intB η hη).const_mul _) (h.intQ η hη),
        MeasureTheory.integral_const_mul]
      rfl
    linarith

/-- **Theorem 2.5**, uniqueness part: under Assumption 2.1, the stationary mean harvest of the
threshold strategy has at most one critical point in `(0, ∞)`. -/
theorem critical_point_unique {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hHx : HasDerivAt d.yieldH 0 x) (hHy : HasDerivAt d.yieldH 0 y) : x = y := by
  have hEq : ∀ t, 0 < t → (fun u => (d.P u + d.lam u * d.Q u) / (d.A u + d.lam u * d.B u))
      =ᶠ[𝓝 t] d.yieldH := fun t ht => by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact (h.yieldH_eq_mean hu).symm
  exact HarvestThreshold.critical_point_unique (A := d.A) (B := d.B) (P := d.P) (Q := d.Q)
    (lam := d.lam) (lam' := fun t => d.lam t * (2 * d.k t / d.v t ^ 2)) (m := d.m) (m₀ := d.m₀)
    (f := d.f)
    (fun _ ht => h.hasDerivAt_A ht) (fun _ ht => h.hasDerivAt_B ht) (fun _ ht => h.hasDerivAt_P ht)
    (fun _ ht => h.hasDerivAt_Q ht) (fun _ ht => d.hasDerivAt_lam ht)
    (fun _ ht => h.A_pos ht) (fun _ ht => h.B_pos ht) (fun t _ => d.lam_pos t)
    (fun t ht => mul_pos (d.lam_pos t) (div_pos (mul_pos two_pos (d.hkpos t ht))
      (pow_pos (d.hvpos t ht) 2)))
    (fun _ ht => d.m_pos ht) (fun _ ht => d.m₀_pos ht) (fun t _ => d.m_eq_lam_mul t)
    (fun _ ht => h.mean_lt ht) hx hy
    (hHx.congr_of_eventuallyEq (hEq x hx)) (hHy.congr_of_eventuallyEq (hEq y hy))

/-- Content lemma: under Assumption 2.1 the yield is differentiable at every `η > 0`, with
`H' = λ' A B (Q/B - P/A) / (A + λ B)²`; so the uniqueness statement is not about a function
without derivatives. -/
theorem yieldH_hasDerivAt {η : ℝ} (hη : 0 < η) :
    HasDerivAt d.yieldH (d.lam η * (2 * d.k η / d.v η ^ 2) *
      (d.A η * d.B η * (d.Q η / d.B η - d.P η / d.A η)) / (d.A η + d.lam η * d.B η) ^ 2) η := by
  have hr := ratio_hasDerivAt (h.hasDerivAt_A hη) (h.hasDerivAt_B hη) (h.hasDerivAt_P hη)
    (h.hasDerivAt_Q hη) (d.hasDerivAt_lam hη) rfl rfl rfl rfl rfl (h.A_pos hη) (h.B_pos hη)
    (d.lam_pos η) (d.m_eq_lam_mul η)
  refine hr.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hη] with u hu
  exact h.yieldH_eq_mean hu

end Assumption

/-! ### Non-vacuity: an example satisfying Assumption 2.1 -/

/-- Drift `1 - x`, noise `√(2x)`, cap `x / 2`, reference point `1`. -/
noncomputable def example₁ : Diffusion where
  f := fun x => 1 - x
  v := fun x => Real.sqrt (2 * x)
  k := fun x => x / 2
  x₁ := 1
  hx₁ := one_pos
  hf := (by fun_prop : Continuous fun x : ℝ => 1 - x).continuousOn
  hv := (by fun_prop : Continuous fun x : ℝ => Real.sqrt (2 * x)).continuousOn
  hk := (by fun_prop : Continuous fun x : ℝ => x / 2).continuousOn
  hvpos := fun x hx => Real.sqrt_pos.mpr (by linarith)
  hkpos := fun x hx => half_pos hx

namespace Example

lemma v_sq {z : ℝ} (hz : 0 < z) : example₁.v z ^ 2 = 2 * z :=
  Real.sq_sqrt (by linarith)

lemma pos_of_uIcc {x z : ℝ} (hx : 0 < x) (hz : z ∈ uIcc (1 : ℝ) x) : 0 < z :=
  lt_of_lt_of_le (lt_inf_iff.mpr ⟨one_pos, hx⟩) hz.1

lemma Φ_eq {x : ℝ} (hx : 0 < x) : example₁.Φ x = log x - (x - 1) := by
  have hcongr : EqOn (fun z => 2 * example₁.f z / example₁.v z ^ 2) (fun z => z⁻¹ - 1) (uIcc 1 x) := by
    intro z hz
    have hz0 := pos_of_uIcc hx hz
    simp only
    rw [v_sq hz0]
    show 2 * (1 - z) / (2 * z) = z⁻¹ - 1
    field_simp
  have hinv : IntervalIntegrable (fun z : ℝ => z⁻¹) volume 1 x :=
    ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun z hz =>
      mem_compl_singleton_iff.mpr (pos_of_uIcc hx hz).ne')
  unfold Φ
  change ∫ z in (1 : ℝ)..x, 2 * example₁.f z / example₁.v z ^ 2 = _
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hinv intervalIntegrable_const,
    integral_inv_of_pos one_pos hx, intervalIntegral.integral_const, div_one, smul_eq_mul, mul_one]

lemma Ψ_eq {x : ℝ} (hx : 0 < x) : example₁.Ψ x = (x - 1) / 2 := by
  have hcongr : EqOn (fun z => 2 * example₁.k z / example₁.v z ^ 2) (fun _ => (1 : ℝ) / 2)
      (uIcc 1 x) := by
    intro z hz
    have hz0 := pos_of_uIcc hx hz
    simp only
    rw [v_sq hz0]
    show 2 * (z / 2) / (2 * z) = 1 / 2
    field_simp
  unfold Ψ
  change ∫ z in (1 : ℝ)..x, 2 * example₁.k z / example₁.v z ^ 2 = _
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma expΦ {x : ℝ} (hx : 0 < x) : exp (example₁.Φ x) = x * exp (-(x - 1)) := by
  rw [Φ_eq hx, sub_eq_add_neg, exp_add, exp_log hx]

lemma m_eq {x : ℝ} (hx : 0 < x) : example₁.m x = exp (-(x - 1)) / 2 := by
  unfold m
  rw [expΦ hx, v_sq hx]
  field_simp

lemma m₀_eq {x : ℝ} (hx : 0 < x) :
    example₁.m₀ x = exp (3 / 2) / 2 * exp (-(3 / 2) * x) := by
  unfold m₀
  have e : -(x - 1) + -((x - 1) / 2) = 3 / 2 + -(3 / 2) * x := by ring
  rw [m_eq hx, Ψ_eq hx, div_mul_eq_mul_div, ← exp_add, e, exp_add]
  ring

lemma intOn {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {η : ℝ} (hη : 0 < η)
    (hint : IntegrableOn (fun y => g y * exp (-(3 / 2) * y)) (Ioi η)) :
    IntegrableOn (fun y => g y * example₁.m₀ y) (Ioi η) := by
  refine IntegrableOn.congr_fun (hint.const_mul (exp (3 / 2) / 2)) (fun y hy => ?_) measurableSet_Ioi
  rw [m₀_eq (hη.trans hy)]; ring

lemma int_exp {η : ℝ} : IntegrableOn (fun y : ℝ => exp (-(3 / 2) * y)) (Ioi η) :=
  exp_neg_integrableOn_Ioi η (by norm_num : (0 : ℝ) < 3 / 2)

lemma int_id_exp {η : ℝ} (hη : 0 < η) : IntegrableOn (fun y : ℝ => y * exp (-(3 / 2) * y)) (Ioi η) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 3 / 2) (by norm_num) one_pos
    (by norm_num)
  simp only [rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi hη.le)

lemma intervalIntegrable_of_eq {g G : ℝ → ℝ} (hG : Continuous G) (heq : ∀ x, 0 < x → g x = G x)
    {η : ℝ} (hη : 0 < η) : IntervalIntegrable g volume 0 η := by
  refine (hG.intervalIntegrable 0 η).congr fun x hx => ?_
  rw [uIoc_of_le hη.le] at hx
  exact (heq x hx.1).symm

theorem assumption : example₁.Assumption where
  intA η hη := intervalIntegrable_of_eq (G := fun x => exp (-(x - 1)) / 2) (by fun_prop)
    (fun x hx => m_eq hx) hη
  intP η hη := intervalIntegrable_of_eq (G := fun x => (1 - x) * (exp (-(x - 1)) / 2)) (by fun_prop)
    (fun x hx => by rw [m_eq hx]; rfl) hη
  intB η hη := by
    have := intOn (g := fun _ => 1) continuousOn_const hη (by simpa using int_exp)
    simpa using this
  intQ η hη := intOn (example₁.hf) hη (by
    have := (int_exp (η := η)).sub (int_id_exp hη)
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ioi
    show exp (-(3 / 2) * y) - y * exp (-(3 / 2) * y) = (1 - y) * exp (-(3 / 2) * y)
    ring)
  intR η hη := intOn (example₁.hk) hη (by
    have := (int_id_exp hη).const_mul (1 / 2)
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ioi
    show 1 / 2 * (y * exp (-(3 / 2) * y)) = y / 2 * exp (-(3 / 2) * y)
    ring)
  lim0 := by
    have hc : Tendsto (fun x : ℝ => x * exp (-(x - 1))) (𝓝[>] 0) (𝓝 0) := by
      have := (by fun_prop : Continuous fun x : ℝ => x * exp (-(x - 1))).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx using (expΦ hx).symm
  limInf := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3 / 2) (by norm_num)
    simp only [rpow_one] at h1
    have hc := h1.const_mul (exp (3 / 2))
    rw [mul_zero] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have e : log x - (x - 1) - (x - 1) / 2 = log x + (3 / 2 + -(3 / 2) * x) := by ring
    rw [Φ_eq hx, Ψ_eq hx, e, exp_add, exp_log hx, exp_add]
    ring
  shape η _ := Or.inr fun y hy => by show 1 - y < 1 - η; linarith

/-- Non-vacuity of Assumption 2.1: it holds for the example. -/
theorem nonvacuous : ∃ d : Diffusion, d.Assumption := ⟨example₁, assumption⟩

end Example

end Diffusion

end HarvestThreshold
