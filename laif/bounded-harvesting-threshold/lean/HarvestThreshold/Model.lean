import HarvestThreshold.Crossing

/-!
# The logistic harvesting model with a bounded harvesting rate

Model of Section 4 of [1] (Hening, Nguyen, Ungureanu, Wong, *Asymptotic harvesting of populations
in random environments*, J. Math. Biol. 78 (2019), arXiv:1710.01221):
`dX = X (μ - κ X - h) dt + σ X dB` with harvesting rate `h ∈ [0, M]`. For the threshold strategy
that harvests at rate `M` above `η` and not below, `yieldH η` is the asymptotic yield, equation (4.4)
of [1], written with the stationary density (4.3) and its normalizing constant.

Main result: `yieldH_critical_point_unique`, for all `μ > σ² / 2`, `κ > 0`, `M > 0`, `σ² > 0`: two
critical points of `yieldH` in `(0, ∞)` coincide. This is the uniqueness part of Conjecture 4.1
of [1].
-/

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace HarvestThreshold

/-- Parameters of the logistic model: growth rate `μ`, competition `κ`, harvesting cap `M`,
noise variance `σ2 = σ²`, with the persistence condition `σ² / 2 < μ`. -/
structure Params where
  μ : ℝ
  κ : ℝ
  M : ℝ
  σ2 : ℝ
  hκ : 0 < κ
  hM : 0 < M
  hσ2 : 0 < σ2
  hμ : σ2 / 2 < μ

/-- The parameters of Figure 1 of [1]: `σ² = 1`, `M = μ = κ = 1`. Here `μ - M ≤ σ² / 2`. -/
def Params.fig1 : Params := ⟨1, 1, 1, 1, one_pos, one_pos, one_pos, by norm_num⟩

namespace Params

variable (p : Params)

/-- `s = 2 / σ²`. -/
noncomputable def s : ℝ := 2 / p.σ2
/-- `a = 2 μ / σ²`. -/
noncomputable def a : ℝ := p.s * p.μ
/-- `α = 2 (μ - M) / σ²`. -/
noncomputable def al : ℝ := p.s * (p.μ - p.M)
/-- `c = 2 κ / σ²`. -/
noncomputable def c : ℝ := p.s * p.κ

lemma s_pos : 0 < p.s := div_pos two_pos p.hσ2
lemma c_pos : 0 < p.c := mul_pos p.s_pos p.hκ
lemma one_lt_a : 1 < p.a := by
  have h := p.hσ2
  have : p.a = 2 * p.μ / p.σ2 := by unfold a s; ring
  rw [this, lt_div_iff₀ h]; linarith [p.hμ]
lemma al_add : p.al + p.s * p.M = p.a := by unfold al a; ring

/-- Speed density without harvesting, `y^(a-2) e^(-c y)`. -/
noncomputable def m (y : ℝ) : ℝ := y ^ (p.a - 2) * exp (-p.c * y)
/-- Speed density under full harvesting, `y^(α-2) e^(-c y)`. -/
noncomputable def m₀ (y : ℝ) : ℝ := y ^ (p.al - 2) * exp (-p.c * y)
/-- `λ(η) = η^(2M/σ²)`. -/
noncomputable def lam (η : ℝ) : ℝ := η ^ (p.s * p.M)
/-- Growth `f(y) = y (μ - κ y)`. -/
def f (y : ℝ) : ℝ := y * (p.μ - p.κ * y)

noncomputable def A (η : ℝ) : ℝ := ∫ y in (0 : ℝ)..η, p.m y
noncomputable def P (η : ℝ) : ℝ := ∫ y in (0 : ℝ)..η, p.f y * p.m y
noncomputable def B (η : ℝ) : ℝ := ∫ y in Ioi η, p.m₀ y
noncomputable def Q (η : ℝ) : ℝ := ∫ y in Ioi η, p.f y * p.m₀ y
noncomputable def R (η : ℝ) : ℝ := ∫ y in Ioi η, y * p.m₀ y

/-- Equation (4.4) of [1]: the asymptotic yield of the threshold strategy with threshold `η`,
`∫_η^∞ y M ρ(y) dy`, where `ρ` is the stationary density (4.3) with the normalizing constant `C₁`
of [1] written out. -/
noncomputable def yieldH (η : ℝ) : ℝ :=
  (∫ y in Ioi η, y * p.M * (1 / (p.σ2 * y ^ 2) * (y / η) ^ (2 * (p.μ - p.M) / p.σ2)
      * exp (-(2 * p.κ / p.σ2) * (y - η)))) /
  ((∫ y in (0 : ℝ)..η, 1 / (p.σ2 * y ^ 2) * (y / η) ^ (2 * p.μ / p.σ2)
      * exp (-(2 * p.κ / p.σ2) * (y - η))) +
    ∫ y in Ioi η, 1 / (p.σ2 * y ^ 2) * (y / η) ^ (2 * (p.μ - p.M) / p.σ2)
      * exp (-(2 * p.κ / p.σ2) * (y - η)))

/-! ### Basic facts -/

lemma m_pos {y : ℝ} (hy : 0 < y) : 0 < p.m y := mul_pos (rpow_pos_of_pos hy _) (exp_pos _)
lemma m₀_pos {y : ℝ} (hy : 0 < y) : 0 < p.m₀ y := mul_pos (rpow_pos_of_pos hy _) (exp_pos _)
lemma lam_pos {y : ℝ} (hy : 0 < y) : 0 < p.lam y := rpow_pos_of_pos hy _

lemma m_eq_lam_mul {y : ℝ} (hy : 0 < y) : p.m y = p.lam y * p.m₀ y := by
  unfold m m₀ lam
  rw [← mul_assoc, ← rpow_add hy]
  congr 2
  linarith [p.al_add]

lemma continuousOn_rpow_exp (q : ℝ) :
    ContinuousOn (fun y : ℝ => y ^ q * exp (-p.c * y)) (Ioi 0) :=
  (continuousOn_id.rpow_const fun y hy => Or.inl (ne_of_gt hy)).mul
    (by fun_prop : Continuous fun y : ℝ => exp (-p.c * y)).continuousOn

lemma continuousOn_m : ContinuousOn p.m (Ioi 0) := p.continuousOn_rpow_exp _
lemma continuousOn_m₀ : ContinuousOn p.m₀ (Ioi 0) := p.continuousOn_rpow_exp _
lemma continuous_f : Continuous p.f := by unfold f; fun_prop

/-- `y^q e^(-c y)` is integrable on `(η, ∞)` for every real `q` when `η > 0`. -/
lemma integrableOn_rpow_exp (q : ℝ) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y : ℝ => y ^ q * exp (-p.c * y)) (Ioi η) := by
  rcases le_or_gt q 0 with hq | hq
  · have hg : IntegrableOn (fun y : ℝ => η ^ q * exp (-p.c * y)) (Ioi η) :=
      (exp_neg_integrableOn_Ioi η p.c_pos).const_mul _
    refine hg.mono' ((p.continuousOn_rpow_exp q).mono (Ioi_subset_Ioi hη.le)
      |>.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := hη.trans hy
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (rpow_pos_of_pos hy0 _) (exp_pos _))]
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos hη hy.le hq) (exp_pos _).le
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : (-1 : ℝ) < q) one_pos p.c_pos
    simp only [rpow_one] at h
    exact IntegrableOn.congr_fun (h.mono_set (Ioi_subset_Ioi hη.le)) (fun y _ => by ring_nf)
      measurableSet_Ioi

lemma integrableOn_pow_mul_m₀ (k : ℕ) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y => y ^ k * p.m₀ y) (Ioi η) := by
  refine IntegrableOn.congr_fun (p.integrableOn_rpow_exp (p.al - 2 + k) hη) (fun y hy => ?_)
    measurableSet_Ioi
  have hy0 : 0 < y := hη.trans hy
  unfold m₀
  show y ^ (p.al - 2 + k) * exp (-p.c * y) = y ^ k * (y ^ (p.al - 2) * exp (-p.c * y))
  rw [rpow_add hy0, rpow_natCast]; ring

lemma integrableOn_m₀ {η : ℝ} (hη : 0 < η) : IntegrableOn p.m₀ (Ioi η) := by
  simpa using p.integrableOn_pow_mul_m₀ 0 hη

lemma integrableOn_id_mul_m₀ {η : ℝ} (hη : 0 < η) : IntegrableOn (fun y => y * p.m₀ y) (Ioi η) := by
  simpa using p.integrableOn_pow_mul_m₀ 1 hη

lemma integrableOn_f_mul_m₀ {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y => p.f y * p.m₀ y) (Ioi η) := by
  have h := ((p.integrableOn_pow_mul_m₀ 1 hη).const_mul p.μ).sub
    ((p.integrableOn_pow_mul_m₀ 2 hη).const_mul p.κ)
  refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, pow_one]; unfold f; ring

lemma intervalIntegrable_m (η : ℝ) : IntervalIntegrable p.m volume 0 η := by
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ (p.a - 2)) volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith [p.one_lt_a])
  exact h1.mul_continuousOn (by fun_prop : Continuous fun y : ℝ => exp (-p.c * y)).continuousOn

lemma intervalIntegrable_g_mul_m {g : ℝ → ℝ} (hg : Continuous g) (η : ℝ) :
    IntervalIntegrable (fun y => g y * p.m y) volume 0 η :=
  (p.intervalIntegrable_m η).continuousOn_mul hg.continuousOn

/-- Positivity of an integral over `(η, ∞)` of a positive integrable function. -/
lemma setIntegral_Ioi_pos {g : ℝ → ℝ} {η : ℝ} (hint : IntegrableOn g (Ioi η))
    (hpos : ∀ y, η < y → 0 < g y) : 0 < ∫ y in Ioi η, g y := by
  rw [← intervalIntegral.integral_interval_add_Ioi hint (hint.mono_set (Ioi_subset_Ioi (by linarith)))
    (b := η + 1)]
  have h1 : 0 < ∫ y in η..(η + 1), g y := by
    refine intervalIntegral_pos_of_pos_on ?_ (fun y hy => hpos y hy.1) (by linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (hint.mono_set Ioc_subset_Ioi_self)
  have h2 : 0 ≤ ∫ y in Ioi (η + 1), g y :=
    setIntegral_nonneg measurableSet_Ioi fun y hy => (hpos y (by linarith [mem_Ioi.mp hy])).le
  linarith

lemma A_pos {η : ℝ} (hη : 0 < η) : 0 < p.A η :=
  intervalIntegral_pos_of_pos_on (p.intervalIntegrable_m η) (fun y hy => p.m_pos hy.1) hη

lemma B_pos {η : ℝ} (hη : 0 < η) : 0 < p.B η :=
  setIntegral_Ioi_pos (p.integrableOn_m₀ hη) fun y hy => p.m₀_pos (hη.trans hy)

/-! ### Derivatives in the threshold -/

lemma hasDerivAt_lam {η : ℝ} (hη : 0 < η) :
    HasDerivAt p.lam (p.s * p.M * η ^ (p.s * p.M - 1)) η :=
  Real.hasDerivAt_rpow_const (Or.inl hη.ne')

lemma hasDerivAt_left {g : ℝ → ℝ} (hg : Continuous g) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, g y * p.m y) (g η * p.m η) η := by
  have hc : ContinuousOn (fun y => g y * p.m y) (Ioi 0) := hg.continuousOn.mul p.continuousOn_m
  exact integral_hasDerivAt_right (p.intervalIntegrable_g_mul_m hg η)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi η hη) (hc.continuousAt (Ioi_mem_nhds hη))

lemma hasDerivAt_A {η : ℝ} (hη : 0 < η) : HasDerivAt p.A (p.m η) η := by
  have h := p.hasDerivAt_left continuous_const hη (g := fun _ => (1 : ℝ))
  simp only [one_mul] at h
  exact h

lemma hasDerivAt_P {η : ℝ} (hη : 0 < η) : HasDerivAt p.P (p.f η * p.m η) η :=
  p.hasDerivAt_left p.continuous_f hη

/-- Derivative of a tail integral `η ↦ ∫_η^∞ g`. -/
lemma hasDerivAt_tail {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (hint : ∀ η, 0 < η → IntegrableOn g (Ioi η)) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun u => ∫ y in Ioi u, g y) (-g η) η := by
  have hb : (0 : ℝ) < η / 2 := by linarith
  have hII : IntervalIntegrable g volume (η / 2) η :=
    (hg.mono fun y (hy : y ∈ Icc (η / 2) η) => show (0 : ℝ) < y from lt_of_lt_of_le hb hy.1
      ).intervalIntegrable_of_Icc (by linarith)
  have hd : HasDerivAt (fun u => (∫ y in Ioi (η / 2), g y) - ∫ y in (η / 2)..u, g y) (-g η) η := by
    have := integral_hasDerivAt_right hII (hg.stronglyMeasurableAtFilter isOpen_Ioi η hη)
      (hg.continuousAt (Ioi_mem_nhds hη))
    simpa using this.const_sub (∫ y in Ioi (η / 2), g y)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (by linarith : η / 2 < η)] with u hu
  rw [← intervalIntegral.integral_interval_add_Ioi (hint u (hb.trans hu)) (hint _ hb),
    intervalIntegral.integral_symm]
  ring

lemma hasDerivAt_B {η : ℝ} (hη : 0 < η) : HasDerivAt p.B (-p.m₀ η) η :=
  hasDerivAt_tail p.continuousOn_m₀ (fun _ h => p.integrableOn_m₀ h) hη

lemma hasDerivAt_Q {η : ℝ} (hη : 0 < η) : HasDerivAt p.Q (-(p.f η * p.m₀ η)) η :=
  hasDerivAt_tail (p.continuous_f.continuousOn.mul p.continuousOn_m₀)
    (fun _ h => p.integrableOn_f_mul_m₀ h) hη

/-! ### Mean growth below and above the threshold -/

/-- Below the peak of `f`, the mean of `f` over `(0, η)` is below `f(η)`; above it, the mean over
`(η, ∞)` is below `f(η)`. -/
lemma mean_lt {η : ℝ} (hη : 0 < η) : p.P η / p.A η < p.f η ∨ p.Q η / p.B η < p.f η := by
  rcases le_or_gt η (p.μ / (2 * p.κ)) with hle | hgt
  · left
    rw [div_lt_iff₀ (p.A_pos hη)]
    have hk := p.hκ
    have h2 : 2 * p.κ * η ≤ p.μ := by rwa [le_div_iff₀ (by linarith), mul_comm] at hle
    have hint := p.intervalIntegrable_g_mul_m (g := fun y => p.f η - p.f y)
      (continuous_const.sub p.continuous_f) η
    have hpos : 0 < ∫ y in (0 : ℝ)..η, (p.f η - p.f y) * p.m y := by
      refine intervalIntegral_pos_of_pos_on hint (fun y hy => mul_pos ?_ (p.m_pos hy.1)) hη
      have : p.f η - p.f y = (η - y) * (p.μ - p.κ * (η + y)) := by unfold f; ring
      rw [this]
      exact mul_pos (by linarith [hy.2]) (by nlinarith [hy.2])
    have heq : ∫ y in (0 : ℝ)..η, (p.f η - p.f y) * p.m y = p.f η * p.A η - p.P η := by
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub ((p.intervalIntegrable_m η).const_mul _)
        (p.intervalIntegrable_g_mul_m p.continuous_f η), intervalIntegral.integral_const_mul]
      rfl
    linarith
  · right
    rw [div_lt_iff₀ (p.B_pos hη)]
    have hk := p.hκ
    have h2 : p.μ < 2 * p.κ * η := by rwa [div_lt_iff₀ (by linarith), mul_comm] at hgt
    have hint : IntegrableOn (fun y => (p.f η - p.f y) * p.m₀ y) (Ioi η) := by
      have := ((p.integrableOn_m₀ hη).const_mul (p.f η)).sub (p.integrableOn_f_mul_m₀ hη)
      exact IntegrableOn.congr_fun this (fun y _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioi
    have hpos : 0 < ∫ y in Ioi η, (p.f η - p.f y) * p.m₀ y := by
      refine setIntegral_Ioi_pos hint fun y hy => mul_pos ?_ (p.m₀_pos (hη.trans hy))
      have : p.f η - p.f y = (y - η) * (p.κ * (η + y) - p.μ) := by unfold f; ring
      rw [this]
      exact mul_pos (by linarith) (by nlinarith)
    have heq : ∫ y in Ioi η, (p.f η - p.f y) * p.m₀ y = p.f η * p.B η - p.Q η := by
      simp only [sub_mul]
      rw [MeasureTheory.integral_sub ((p.integrableOn_m₀ hη).const_mul _) (p.integrableOn_f_mul_m₀ hη),
        MeasureTheory.integral_const_mul]
      rfl
    linarith

/-! ### Yield equals mean growth -/

lemma integral_left {η : ℝ} (hη : 0 < η) :
    p.s * p.P η = η ^ p.a * exp (-p.c * η) := by
  have hF : ∀ y ∈ Ioo (0 : ℝ) η, HasDerivAt (fun y : ℝ => y ^ p.a * exp (-p.c * y))
      (p.s * (p.f y * p.m y)) y := by
    intro y hy
    have hy0 := hy.1
    have h1 := Real.hasDerivAt_rpow_const (p := p.a) (Or.inl hy0.ne')
    have h2 : HasDerivAt (fun y : ℝ => exp (-p.c * y)) (exp (-p.c * y) * (-p.c)) y := by
      simpa using ((hasDerivAt_id y).const_mul (-p.c)).exp
    convert h1.mul h2 using 1
    have e1 : y ^ (p.a - 1) = y * y ^ (p.a - 2) := by
      rw [show p.a - 1 = (p.a - 2) + 1 by ring, rpow_add hy0, rpow_one]; ring
    have e2 : y ^ p.a = y ^ 2 * y ^ (p.a - 2) := by
      rw [← rpow_two, ← rpow_add hy0]
      congr 1; ring
    rw [e1, e2]
    unfold f m a c
    ring
  have hcont : ContinuousOn (fun y : ℝ => y ^ p.a * exp (-p.c * y)) (Icc 0 η) :=
    ((continuousOn_id.rpow_const fun _ _ => Or.inr (by linarith [p.one_lt_a])).mul
      (by fun_prop : Continuous fun y : ℝ => exp (-p.c * y)).continuousOn)
  have hint : IntervalIntegrable (fun y => p.s * (p.f y * p.m y)) volume 0 η :=
    (p.intervalIntegrable_g_mul_m p.continuous_f η).const_mul _
  have := integral_eq_sub_of_hasDerivAt_of_le hη.le hcont hF hint
  rw [intervalIntegral.integral_const_mul] at this
  rw [P, this, zero_rpow (by linarith [p.one_lt_a]), zero_mul, sub_zero]

lemma integral_right {η : ℝ} (hη : 0 < η) :
    p.s * (p.Q η - p.M * p.R η) = -(η ^ p.al * exp (-p.c * η)) := by
  have hF : ∀ y ∈ Ioi η, HasDerivAt (fun y : ℝ => y ^ p.al * exp (-p.c * y))
      (p.s * (p.f y * p.m₀ y - p.M * (y * p.m₀ y))) y := by
    intro y hy
    have hy0 : 0 < y := hη.trans hy
    have h1 := Real.hasDerivAt_rpow_const (p := p.al) (Or.inl hy0.ne')
    have h2 : HasDerivAt (fun y : ℝ => exp (-p.c * y)) (exp (-p.c * y) * (-p.c)) y := by
      simpa using ((hasDerivAt_id y).const_mul (-p.c)).exp
    convert h1.mul h2 using 1
    have e1 : y ^ (p.al - 1) = y * y ^ (p.al - 2) := by
      rw [show p.al - 1 = (p.al - 2) + 1 by ring, rpow_add hy0, rpow_one]; ring
    have e2 : y ^ p.al = y ^ 2 * y ^ (p.al - 2) := by
      rw [← rpow_two, ← rpow_add hy0]
      congr 1; ring
    rw [e1, e2]
    unfold f m₀ al c
    ring
  have hcont : ContinuousWithinAt (fun y : ℝ => y ^ p.al * exp (-p.c * y)) (Ici η) η :=
    ((p.continuousOn_rpow_exp p.al).continuousAt (Ioi_mem_nhds hη)).continuousWithinAt
  have hint : IntegrableOn (fun y => p.s * (p.f y * p.m₀ y - p.M * (y * p.m₀ y))) (Ioi η) :=
    ((p.integrableOn_f_mul_m₀ hη).sub ((p.integrableOn_id_mul_m₀ hη).const_mul _)).const_mul _
  have hlim : Tendsto (fun y : ℝ => y ^ p.al * exp (-p.c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p.al p.c p.c_pos
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hF hint hlim
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub (p.integrableOn_f_mul_m₀ hη)
    ((p.integrableOn_id_mul_m₀ hη).const_mul _), MeasureTheory.integral_const_mul] at this
  rw [Q, R, this, zero_sub]

/-- The yield (4.4) of [1] in rescaled form. -/
lemma yieldH_eq_scaled {η : ℝ} (hη : 0 < η) :
    p.yieldH η = p.M * p.lam η * p.R η / (p.A η + p.lam η * p.B η) := by
  -- kernel identity: `1/(σ² y²) (y/η)^e e^(-c(y-η)) = (η^(-e) e^(cη) / σ²) y^(e-2) e^(-cy)`
  have hker : ∀ e y : ℝ, 0 < y → 1 / (p.σ2 * y ^ 2) * (y / η) ^ e * exp (-(2 * p.κ / p.σ2) * (y - η))
      = (η ^ (-e) * exp (p.c * η) / p.σ2) * (y ^ (e - 2) * exp (-p.c * y)) := by
    intro e y hy
    have hσ := p.hσ2.ne'
    have hexp : exp (-(2 * p.κ / p.σ2) * (y - η)) = exp (p.c * η) * exp (-p.c * y) := by
      rw [← exp_add]; congr 1; unfold c s; ring
    rw [hexp, div_rpow hy.le hη.le, rpow_sub hy, rpow_neg hη.le, rpow_two]
    field_simp
  have ha : 2 * p.μ / p.σ2 = p.a := by unfold a s; ring
  have hal : 2 * (p.μ - p.M) / p.σ2 = p.al := by unfold al s; ring
  set K₁ := η ^ (-p.a) * exp (p.c * η) / p.σ2 with hK₁
  set K₂ := η ^ (-p.al) * exp (p.c * η) / p.σ2 with hK₂
  have hK₁pos : 0 < K₁ := div_pos (mul_pos (rpow_pos_of_pos hη _) (exp_pos _)) p.hσ2
  have hK₂ : K₂ = p.lam η * K₁ := by
    rw [hK₂, hK₁, lam, ← mul_div_assoc, ← mul_assoc, ← rpow_add hη]
    congr 3
    linarith [p.al_add]
  have hnum : (∫ y in Ioi η, y * p.M * (1 / (p.σ2 * y ^ 2) * (y / η) ^ (2 * (p.μ - p.M) / p.σ2)
      * exp (-(2 * p.κ / p.σ2) * (y - η)))) = p.M * K₂ * p.R η := by
    rw [R, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [hal, hker _ y (hη.trans hy), m₀]
    ring
  have hlow : (∫ y in (0 : ℝ)..η, 1 / (p.σ2 * y ^ 2) * (y / η) ^ (2 * p.μ / p.σ2)
      * exp (-(2 * p.κ / p.σ2) * (y - η))) = K₁ * p.A η := by
    rw [A, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
    rw [uIoc_of_le hη.le] at hy
    rw [ha, hker _ y hy.1, m]
  have hup : (∫ y in Ioi η, 1 / (p.σ2 * y ^ 2) * (y / η) ^ (2 * (p.μ - p.M) / p.σ2)
      * exp (-(2 * p.κ / p.σ2) * (y - η))) = K₂ * p.B η := by
    rw [B, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [hal, hker _ y (hη.trans hy), m₀]
  rw [yieldH, hnum, hlow, hup, hK₂]
  have := p.A_pos hη
  have := p.B_pos hη
  have := p.lam_pos hη
  field_simp

/-- Lemma 1: the yield equals the stationary mean of the growth `f`. -/
lemma yieldH_eq_mean {η : ℝ} (hη : 0 < η) :
    p.yieldH η = (p.P η + p.lam η * p.Q η) / (p.A η + p.lam η * p.B η) := by
  rw [p.yieldH_eq_scaled hη]
  congr 1
  have h1 := p.integral_left hη
  have h2 := p.integral_right hη
  have hlam : p.lam η * η ^ p.al = η ^ p.a := by
    rw [lam, ← rpow_add hη]; congr 1; linarith [p.al_add]
  have hs := p.s_pos.ne'
  apply mul_left_cancel₀ hs
  have : p.s * (p.P η + p.lam η * p.Q η)
      = η ^ p.a * exp (-p.c * η) + p.lam η * (p.s * (p.Q η - p.M * p.R η)) + p.s * p.M * p.lam η * p.R η := by
    rw [← h1]; ring
  rw [this, h2, ← hlam]
  ring

/-! ### Main theorem -/

/-- **Uniqueness of the optimal threshold** (Conjecture 4.1 of [1], uniqueness part), for all
parameters with `σ² / 2 < μ`, `κ > 0`, `M > 0`: the asymptotic yield (4.4) has at most one critical
point in `(0, ∞)`. -/
theorem yieldH_critical_point_unique {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hHx : HasDerivAt p.yieldH 0 x) (hHy : HasDerivAt p.yieldH 0 y) : x = y := by
  have hEq : ∀ t, 0 < t → (fun u => (p.P u + p.lam u * p.Q u) / (p.A u + p.lam u * p.B u))
      =ᶠ[𝓝 t] p.yieldH := fun t ht => by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact (p.yieldH_eq_mean hu).symm
  exact critical_point_unique (A := p.A) (B := p.B) (P := p.P) (Q := p.Q) (lam := p.lam)
    (lam' := fun t => p.s * p.M * t ^ (p.s * p.M - 1)) (m := p.m) (m₀ := p.m₀) (f := p.f)
    (fun _ h => p.hasDerivAt_A h) (fun _ h => p.hasDerivAt_B h) (fun _ h => p.hasDerivAt_P h)
    (fun _ h => p.hasDerivAt_Q h) (fun _ h => p.hasDerivAt_lam h)
    (fun _ h => p.A_pos h) (fun _ h => p.B_pos h) (fun _ h => p.lam_pos h)
    (fun _ h => mul_pos (mul_pos p.s_pos p.hM) (rpow_pos_of_pos h _))
    (fun _ h => p.m_pos h) (fun _ h => p.m₀_pos h) (fun _ h => p.m_eq_lam_mul h)
    (fun _ h => p.mean_lt h) hx hy
    (hHx.congr_of_eventuallyEq (hEq x hx)) (hHy.congr_of_eventuallyEq (hEq y hy))


/-- The derivative of the yield (4.4) in closed form, for every threshold `η > 0`. -/
theorem yieldH_hasDerivAt {η : ℝ} (hη : 0 < η) :
    HasDerivAt p.yieldH (p.s * p.M * η ^ (p.s * p.M - 1) *
      (p.A η * p.B η * (p.Q η / p.B η - p.P η / p.A η)) / (p.A η + p.lam η * p.B η) ^ 2) η := by
  have h := ratio_hasDerivAt (p.hasDerivAt_A hη) (p.hasDerivAt_B hη) (p.hasDerivAt_P hη)
    (p.hasDerivAt_Q hη) (p.hasDerivAt_lam hη) rfl rfl rfl rfl rfl (p.A_pos hη) (p.B_pos hη)
    (p.lam_pos hη) (p.m_eq_lam_mul hη)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hη] with u hu
  exact p.yieldH_eq_mean hu

/-- Content lemma: the yield is strictly decreasing at `η = μ / κ`, where the growth `f` vanishes;
its derivative there is negative. -/
theorem yieldH_deriv_neg_at_zero_of_growth :
    ∃ d < 0, HasDerivAt p.yieldH d (p.μ / p.κ) := by
  have hk := p.hκ
  have hμ0 : 0 < p.μ := by linarith [p.hμ, p.hσ2]
  set x₀ := p.μ / p.κ with hx₀
  have hx : 0 < x₀ := div_pos hμ0 hk
  refine ⟨_, ?_, p.yieldH_hasDerivAt hx⟩
  have hQ : p.Q x₀ < 0 := by
    have hpos : 0 < ∫ y in Ioi x₀, -(p.f y * p.m₀ y) :=
      setIntegral_Ioi_pos (p.integrableOn_f_mul_m₀ hx).neg fun y hy => by
        have hy0 : 0 < y := hx.trans hy
        have : p.κ * y > p.μ := by rwa [hx₀, div_lt_iff₀ hk, mul_comm] at hy
        have hf : p.f y < 0 := by unfold f; nlinarith
        nlinarith [p.m₀_pos hy0]
    rw [MeasureTheory.integral_neg] at hpos
    unfold Q; linarith
  have hP : 0 < p.P x₀ := by
    refine intervalIntegral_pos_of_pos_on (p.intervalIntegrable_g_mul_m p.continuous_f x₀)
      (fun y hy => mul_pos ?_ (p.m_pos hy.1)) hx
    have : p.κ * y < p.μ := by have := hy.2; rwa [hx₀, lt_div_iff₀ hk, mul_comm] at this
    unfold f; nlinarith [hy.1]
  have hD : p.Q x₀ / p.B x₀ - p.P x₀ / p.A x₀ < 0 := by
    have := div_neg_of_neg_of_pos hQ (p.B_pos hx)
    have := div_pos hP (p.A_pos hx)
    linarith
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (mul_pos (mul_pos p.s_pos p.hM) (rpow_pos_of_pos hx _))
      (mul_neg_of_pos_of_neg (mul_pos (p.A_pos hx) (p.B_pos hx)) hD)
  · exact pow_pos (add_pos (p.A_pos hx) (mul_pos (p.lam_pos hx) (p.B_pos hx))) 2

/-- Theorem 2.1 of [1], in the weaker form used here: for `Φ(x) = x` and `μ > σ²/2`, an optimal
harvesting strategy is of threshold type with a threshold `x̂ ∈ (0, ∞)`; since every threshold
strategy is admissible, its yield (4.4) is at least the yield of every other threshold. -/
def Theorem21 : Prop := ∃ x, 0 < x ∧ ∀ η, 0 < η → p.yieldH η ≤ p.yieldH x

/-- **Conjecture 4.1 of [1]**, assuming Theorem 2.1 of [1] for the existence of a maximizer: there is
exactly one `x* > 0` with `H'(x*) = 0`, and it maximizes the yield (4.4) over all thresholds. -/
theorem conjecture_4_1 (h21 : p.Theorem21) :
    ∃! x, 0 < x ∧ HasDerivAt p.yieldH 0 x ∧ ∀ η, 0 < η → p.yieldH η ≤ p.yieldH x := by
  obtain ⟨x, hx, hmax⟩ := h21
  have hloc : IsLocalMax p.yieldH x := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact hmax u hu
  have hd := p.yieldH_hasDerivAt hx
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [h0] at hd
  refine ⟨x, ⟨hx, hd, hmax⟩, fun y hy => ?_⟩
  exact p.yieldH_critical_point_unique hy.1 hx hy.2.1 hd

/-- Non-vacuity of the parameter hypotheses: the parameters of Figure 1 of [1] satisfy them, and
there `μ - M ≤ σ² / 2`, the case outside the integrability assumption of arXiv:2608.17778. -/
theorem fig1_case : Params.fig1.μ - Params.fig1.M ≤ Params.fig1.σ2 / 2 := by
  simp [Params.fig1]

end Params

end HarvestThreshold
