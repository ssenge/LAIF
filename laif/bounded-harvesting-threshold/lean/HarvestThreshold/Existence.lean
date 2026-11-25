import HarvestThreshold.Model

/-!
# Existence of the optimal threshold

The yield (4.4) of [1] has a critical point `x* > 0`; it is strictly increasing on `(0, x*]` and
strictly decreasing on `[x*, ∞)`. With `yieldH_critical_point_unique` this proves Conjecture 4.1
of [1] for all parameters with `σ² / 2 < μ`, `κ > 0`, `M > 0`, with no further hypothesis.

Write `D = Q / B - P / A`; the derivative of the yield is a positive multiple of `D`, and
`D(μ / κ) < 0`. A point with `D > 0` below `μ / κ` comes from two cases:
* `α = 2 (μ - M) / σ² > 1`: an explicit small threshold, from `A ≥ e^(-cη) η^(a-1) / (a - 1)` and
  bounds on the tails `∫_η^∞ m₀` and `∫_η^∞ y m₀`;
* `α ≤ 1`: the yield is at most `M ∫_η^∞ y m₀ / ∫_η^∞ m₀`, which is small for small `η` because
  `∫_η^∞ m₀ ≥ e^(-c) log (1 / η)`; so the yield increases somewhere below `μ / κ`.
-/

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace HarvestThreshold

namespace Params

variable (p : Params)

/-- Mean growth above the threshold minus mean growth below it. -/
noncomputable def D (η : ℝ) : ℝ := p.Q η / p.B η - p.P η / p.A η

/-- The positive factor in the derivative of the yield. -/
noncomputable def kfac (η : ℝ) : ℝ :=
  p.s * p.M * η ^ (p.s * p.M - 1) * (p.A η * p.B η) / (p.A η + p.lam η * p.B η) ^ 2

lemma kfac_pos {η : ℝ} (hη : 0 < η) : 0 < p.kfac η :=
  div_pos (mul_pos (mul_pos (mul_pos p.s_pos p.hM) (rpow_pos_of_pos hη _))
    (mul_pos (p.A_pos hη) (p.B_pos hη)))
    (pow_pos (add_pos (p.A_pos hη) (mul_pos (p.lam_pos hη) (p.B_pos hη))) 2)

lemma hasDerivAt_yieldH' {η : ℝ} (hη : 0 < η) :
    HasDerivAt p.yieldH (p.kfac η * p.D η) η := by
  convert p.yieldH_hasDerivAt hη using 1
  unfold kfac D
  ring

lemma continuousAt_D {η : ℝ} (hη : 0 < η) : ContinuousAt p.D η := by
  show ContinuousAt (fun t => p.Q t / p.B t - p.P t / p.A t) η
  exact ((p.hasDerivAt_Q hη).continuousAt.div (p.hasDerivAt_B hη).continuousAt
    (p.B_pos hη).ne').sub ((p.hasDerivAt_P hη).continuousAt.div (p.hasDerivAt_A hη).continuousAt
    (p.A_pos hη).ne')

lemma continuousOn_D {u : ℝ} (hu : 0 < u) (S : Set ℝ) (hS : S ⊆ Ici u) : ContinuousOn p.D S :=
  fun t ht => (p.continuousAt_D (hu.trans_le (hS ht))).continuousWithinAt

lemma continuousOn_yieldH {u v : ℝ} (hu : 0 < u) : ContinuousOn p.yieldH (Icc u v) :=
  fun t ht => (p.hasDerivAt_yieldH' (hu.trans_le ht.1)).continuousAt.continuousWithinAt

lemma hasDerivAt_zero_of_D {x : ℝ} (hx : 0 < x) (hD : p.D x = 0) :
    HasDerivAt p.yieldH 0 x := by
  simpa [hD] using p.hasDerivAt_yieldH' hx

lemma D_zero_unique {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hDx : p.D x = 0) (hDy : p.D y = 0) :
    x = y :=
  p.yieldH_critical_point_unique hx hy (p.hasDerivAt_zero_of_D hx hDx) (p.hasDerivAt_zero_of_D hy hDy)

lemma x₀_pos : 0 < p.μ / p.κ := div_pos (by linarith [p.hμ, p.hσ2]) p.hκ

lemma D_neg_at_x₀ : p.D (p.μ / p.κ) < 0 := by
  obtain ⟨d, hd, hder⟩ := p.yieldH_deriv_neg_at_zero_of_growth
  have he := hder.unique (p.hasDerivAt_yieldH' p.x₀_pos)
  have hk := p.kfac_pos p.x₀_pos
  by_contra h
  have := mul_nonneg hk.le (not_lt.mp h)
  linarith

/-- Mean value step: `D > 0` on `(u, v)` gives `H u < H v`. -/
lemma yieldH_lt_of_D_pos {u v : ℝ} (hu : 0 < u) (huv : u < v) (hD : ∀ t ∈ Ioo u v, 0 < p.D t) :
    p.yieldH u < p.yieldH v := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope p.yieldH (fun t => p.kfac t * p.D t) huv
    (p.continuousOn_yieldH hu) (fun t ht => p.hasDerivAt_yieldH' (hu.trans ht.1))
  have hpos : 0 < p.kfac t * p.D t := mul_pos (p.kfac_pos (hu.trans ht.1)) (hD t ht)
  rw [heq, lt_div_iff₀ (sub_pos.mpr huv), zero_mul] at hpos
  linarith

/-- Mean value step: `D < 0` on `(u, v)` gives `H v < H u`. -/
lemma yieldH_gt_of_D_neg {u v : ℝ} (hu : 0 < u) (huv : u < v) (hD : ∀ t ∈ Ioo u v, p.D t < 0) :
    p.yieldH v < p.yieldH u := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope p.yieldH (fun t => p.kfac t * p.D t) huv
    (p.continuousOn_yieldH hu) (fun t ht => p.hasDerivAt_yieldH' (hu.trans ht.1))
  have hneg : p.kfac t * p.D t < 0 := mul_neg_of_pos_of_neg (p.kfac_pos (hu.trans ht.1)) (hD t ht)
  rw [heq, div_lt_iff₀ (sub_pos.mpr huv), zero_mul] at hneg
  linarith

/-- If the yield increases from `u` to `v`, then `D > 0` somewhere in `(u, v)`. -/
lemma exists_D_pos_of_lt {u v : ℝ} (hu : 0 < u) (huv : u < v) (hH : p.yieldH u < p.yieldH v) :
    ∃ t ∈ Ioo u v, 0 < p.D t := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope p.yieldH (fun t => p.kfac t * p.D t) huv
    (p.continuousOn_yieldH hu) (fun t ht => p.hasDerivAt_yieldH' (hu.trans ht.1))
  refine ⟨t, ht, ?_⟩
  have hs : 0 < (p.yieldH v - p.yieldH u) / (v - u) := div_pos (by linarith) (by linarith)
  rw [← heq] at hs
  exact pos_of_mul_pos_right hs (p.kfac_pos (hu.trans ht.1)).le

/-- From one point with `D > 0` below `μ / κ`: a critical point `x`, with the yield strictly
increasing on `(0, x]` and strictly decreasing on `[x, ∞)`. -/
lemma unimodal_of_D_pos {η₁ : ℝ} (h1 : 0 < η₁) (h1x : η₁ < p.μ / p.κ) (hD1 : 0 < p.D η₁) :
    ∃ x, 0 < x ∧ HasDerivAt p.yieldH 0 x ∧ StrictMonoOn p.yieldH (Ioc 0 x) ∧
      StrictAntiOn p.yieldH (Ici x) := by
  have hD0 := p.D_neg_at_x₀
  obtain ⟨x, hxI, hDx⟩ := intermediate_value_Icc' h1x.le
    (p.continuousOn_D h1 (Icc η₁ (p.μ / p.κ)) fun t ht => ht.1) ⟨hD0.le, hD1.le⟩
  have hx : 0 < x := h1.trans_le hxI.1
  have h1x' : η₁ < x := lt_of_le_of_ne hxI.1 fun h => by rw [h] at hD1; linarith
  have hx0 : x < p.μ / p.κ := lt_of_le_of_ne hxI.2 fun h => by rw [← h] at hD0; linarith
  -- `D > 0` on `(0, x)`
  have hleft : ∀ t, 0 < t → t < x → 0 < p.D t := by
    intro t ht htx
    by_contra hle
    rw [not_lt] at hle
    have hmin : 0 < min t η₁ := lt_min ht h1
    obtain ⟨z, hz, hDz⟩ := intermediate_value_uIcc
      (p.continuousOn_D hmin (uIcc t η₁) fun s hs => hs.1) (mem_uIcc.mpr (Or.inl ⟨hle, hD1.le⟩))
    have hz0 : 0 < z := hmin.trans_le hz.1
    have hzx : z < x := lt_of_le_of_lt hz.2 (max_lt htx h1x')
    exact absurd (p.D_zero_unique hz0 hx hDz hDx) hzx.ne
  -- `D < 0` on `(x, ∞)`
  have hright : ∀ t, x < t → p.D t < 0 := by
    intro t hxt
    by_contra hge
    rw [not_lt] at hge
    have hmin : x < min t (p.μ / p.κ) := lt_min hxt hx0
    obtain ⟨z, hz, hDz⟩ := intermediate_value_uIcc
      (p.continuousOn_D (hx.trans hmin) (uIcc t (p.μ / p.κ)) fun s hs => hs.1)
      (mem_uIcc.mpr (Or.inr ⟨hD0.le, hge⟩))
    have hxz : x < z := hmin.trans_le hz.1
    exact absurd (p.D_zero_unique (hx.trans hxz) hx hDz hDx) hxz.ne'
  refine ⟨x, hx, p.hasDerivAt_zero_of_D hx hDx, ?_, ?_⟩
  · intro u hu v hv huv
    exact p.yieldH_lt_of_D_pos hu.1 huv fun t ht =>
      hleft t (hu.1.trans ht.1) (ht.2.trans_le hv.2)
  · intro u hu v hv huv
    exact p.yieldH_gt_of_D_neg (hx.trans_le hu) huv fun t ht =>
      hright t (lt_of_le_of_lt hu ht.1)

/-! ### Bounds on the integrals -/

lemma A_ge {η : ℝ} (hη : 0 < η) :
    exp (-p.c * η) * (η ^ (p.a - 1) / (p.a - 1)) ≤ p.A η := by
  have ha := p.one_lt_a
  have hint : ∫ y in (0 : ℝ)..η, y ^ (p.a - 2) = η ^ (p.a - 1) / (p.a - 1) := by
    rw [integral_rpow (Or.inl (by linarith)), show p.a - 2 + 1 = p.a - 1 by ring,
      zero_rpow (by linarith : p.a - 1 ≠ 0), sub_zero]
  rw [← hint, ← intervalIntegral.integral_const_mul]
  unfold A
  apply intervalIntegral.integral_mono_on hη.le
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  · exact p.intervalIntegrable_m η
  · intro y hy
    unfold m
    rw [mul_comm (exp _)]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [p.c_pos, hy.2]))
      (rpow_nonneg hy.1 _)

lemma R_nonneg {η : ℝ} (hη : 0 < η) : 0 ≤ p.R η :=
  setIntegral_nonneg measurableSet_Ioi fun y hy =>
    (mul_pos (hη.trans hy) (p.m₀_pos (hη.trans hy))).le

lemma R_pos {η : ℝ} (hη : 0 < η) : 0 < p.R η :=
  setIntegral_Ioi_pos (p.integrableOn_id_mul_m₀ hη) fun y hy =>
    mul_pos (hη.trans hy) (p.m₀_pos (hη.trans hy))

/-- The yield is at most `M` times the mean of `y` under `m₀` on `(η, ∞)`. -/
lemma yieldH_le {η : ℝ} (hη : 0 < η) : p.yieldH η ≤ p.M * (p.R η / p.B η) := by
  have hA := p.A_pos hη
  have hB := p.B_pos hη
  have hl := p.lam_pos hη
  rw [p.yieldH_eq_scaled hη]
  calc p.M * p.lam η * p.R η / (p.A η + p.lam η * p.B η)
      ≤ p.M * p.lam η * p.R η / (p.lam η * p.B η) :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_pos p.hM hl).le (p.R_nonneg hη))
          (mul_pos hl hB) (by linarith)
    _ = p.M * (p.R η / p.B η) := by
        rw [eq_comm, mul_div_assoc', div_eq_div_iff hB.ne' (mul_pos hl hB).ne']
        ring

lemma yieldH_pos {η : ℝ} (hη : 0 < η) : 0 < p.yieldH η := by
  rw [p.yieldH_eq_scaled hη]
  exact div_pos (mul_pos (mul_pos p.hM (p.lam_pos hη)) (p.R_pos hη))
    (add_pos (p.A_pos hη) (mul_pos (p.lam_pos hη) (p.B_pos hη)))

lemma R_le {η ε : ℝ} (hη : 0 < η) (hηε : η < ε) : p.R η ≤ ε * p.B η + p.R ε := by
  have hε : 0 < ε := hη.trans hηε
  have hR := intervalIntegral.integral_interval_add_Ioi (p.integrableOn_id_mul_m₀ hη)
    (p.integrableOn_id_mul_m₀ hε)
  have hB := intervalIntegral.integral_interval_add_Ioi (p.integrableOn_m₀ hη) (p.integrableOn_m₀ hε)
  have hBt : 0 ≤ ∫ y in Ioi ε, p.m₀ y :=
    setIntegral_nonneg measurableSet_Ioi fun y hy => (p.m₀_pos (hε.trans hy)).le
  have hmono : ∫ y in η..ε, y * p.m₀ y ≤ ∫ y in η..ε, ε * p.m₀ y := by
    apply intervalIntegral.integral_mono_on hηε.le
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hηε.le).2
        ((p.integrableOn_id_mul_m₀ hη).mono_set Ioc_subset_Ioi_self)
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hηε.le).2
        ((p.integrableOn_m₀ hη).mono_set Ioc_subset_Ioi_self)).const_mul _
    · intro y hy
      exact mul_le_mul_of_nonneg_right hy.2 (p.m₀_pos (hη.trans_le hy.1)).le
  rw [intervalIntegral.integral_const_mul] at hmono
  unfold R B
  rw [← hR, ← hB]
  nlinarith [mul_nonneg hε.le hBt]

lemma B_ge_log (hal : p.al ≤ 1) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    exp (-p.c) * log (1 / η) ≤ p.B η := by
  have hsplit := intervalIntegral.integral_interval_add_Ioi (p.integrableOn_m₀ hη)
    (p.integrableOn_m₀ one_pos)
  have htail : 0 ≤ ∫ y in Ioi 1, p.m₀ y :=
    setIntegral_nonneg measurableSet_Ioi fun y hy => (p.m₀_pos (one_pos.trans hy)).le
  have hmono : ∫ y in η..1, exp (-p.c) * y⁻¹ ≤ ∫ y in η..1, p.m₀ y := by
    apply intervalIntegral.integral_mono_on hη1.le
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => ?_)
      rw [uIcc_of_le hη1.le] at hy
      exact mem_compl_singleton_iff.mpr (hη.trans_le hy.1).ne'
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hη1.le).2
        ((p.integrableOn_m₀ hη).mono_set Ioc_subset_Ioi_self)
    · intro y hy
      have hy0 : 0 < y := hη.trans_le hy.1
      have h1 : y⁻¹ ≤ y ^ (p.al - 2) := by
        rw [← rpow_neg_one]
        exact rpow_le_rpow_of_exponent_ge hy0 hy.2 (by linarith)
      have h2 : exp (-p.c) ≤ exp (-p.c * y) := exp_le_exp.mpr (by nlinarith [p.c_pos, hy.2])
      calc exp (-p.c) * y⁻¹ ≤ exp (-p.c * y) * y ^ (p.al - 2) :=
            mul_le_mul h2 h1 (inv_nonneg.mpr hy0.le) (exp_pos _).le
        _ = p.m₀ y := by unfold m₀; ring
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hη one_pos] at hmono
  unfold B
  rw [← hsplit]
  linarith

/-! ### A point with `D > 0` -/

lemma exists_D_pos_of_al_le_one (hal : p.al ≤ 1) :
    ∃ η, 0 < η ∧ η < p.μ / p.κ ∧ 0 < p.D η := by
  set x₀ := p.μ / p.κ with hx₀
  have hx : 0 < x₀ := p.x₀_pos
  set V := p.yieldH x₀ / p.M with hV
  have hVpos : 0 < V := div_pos (p.yieldH_pos hx) p.hM
  set ε := min (min (x₀ / 2) (V / 2)) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hεx : ε < x₀ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hεV : ε ≤ V / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  set N := p.R ε with hN
  have hN0 : 0 ≤ N := p.R_nonneg hε0
  set L := 2 * N * exp p.c / V + 1 with hL
  set η := min (ε / 2) (exp (-L)) with hη
  have hη0 : 0 < η := lt_min (by linarith) (exp_pos _)
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  have hη1 : η < 1 := by linarith
  have hlog : L ≤ log (1 / η) := by
    rw [one_div, log_inv, le_neg]
    calc log η ≤ log (exp (-L)) := log_le_log hη0 (min_le_right _ _)
      _ = -L := log_exp _
  have hB := p.B_ge_log hal hη0 hη1
  have hBpos := p.B_pos hη0
  -- `B η > 2 N / V`
  have hBN : 2 * N / V < p.B η := by
    have h1 : exp (-p.c) * L = 2 * N / V + exp (-p.c) := by
      rw [hL, mul_add, mul_one, mul_div_assoc', ← mul_assoc, mul_comm (exp (-p.c)) (2 * N),
        mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    have h2 : exp (-p.c) * L ≤ exp (-p.c) * log (1 / η) :=
      mul_le_mul_of_nonneg_left hlog (exp_pos _).le
    linarith [exp_pos (-p.c)]
  have hRB : p.R η / p.B η < V := by
    rw [div_lt_iff₀ hBpos]
    have := p.R_le hη0 hηε
    have h3 : 2 * N < V * p.B η := by rw [div_lt_iff₀ hVpos] at hBN; linarith
    nlinarith [mul_le_mul_of_nonneg_right hεV hBpos.le]
  have hHη : p.yieldH η < p.yieldH x₀ := by
    have := p.yieldH_le hη0
    have hMV : p.M * V = p.yieldH x₀ := by
      rw [hV, mul_div_assoc', mul_comm, mul_div_assoc, div_self p.hM.ne', mul_one]
    nlinarith [mul_lt_mul_of_pos_left hRB p.hM]
  obtain ⟨t, ht, hDt⟩ := p.exists_D_pos_of_lt hη0 (hηε.trans hεx) hHη
  exact ⟨t, hη0.trans ht.1, ht.2, hDt⟩

lemma exists_D_pos_of_one_lt_al (hal : 1 < p.al) :
    ∃ η, 0 < η ∧ η < p.μ / p.κ ∧ 0 < p.D η := by
  have hx := p.x₀_pos
  have ha := p.one_lt_a
  have hint0 : IntegrableOn p.m₀ (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : (-1 : ℝ) < p.al - 2) one_pos
      p.c_pos
    simp only [rpow_one] at h
    exact h
  set B₀ := ∫ y in Ioi 0, p.m₀ y with hB₀
  have hB₀0 : 0 ≤ B₀ := setIntegral_nonneg measurableSet_Ioi fun y hy => (p.m₀_pos hy).le
  have hBle : ∀ η, 0 < η → p.B η ≤ B₀ := fun η hη =>
    setIntegral_mono_set hint0
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => (p.m₀_pos hy).le)
      (Eventually.of_forall (Ioi_subset_Ioi hη.le))
  have hR1 := p.R_pos one_pos
  have hRge : ∀ η, 0 < η → η ≤ 1 → p.R 1 ≤ p.R η := fun η hη hη1 =>
    setIntegral_mono_set (p.integrableOn_id_mul_m₀ hη)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
        (mul_pos (hη.trans hy) (p.m₀_pos (hη.trans hy))).le)
      (Eventually.of_forall (Ioi_subset_Ioi hη1))
  set be := p.s * p.M with hbe
  have hbe0 : 0 < be := mul_pos p.s_pos p.hM
  set η := min (min 1 (p.μ / p.κ / 2)) (be * p.R 1 / (2 * (1 + (p.a - 1) * B₀))) with hη
  have hden : 0 < 2 * (1 + (p.a - 1) * B₀) := by nlinarith
  have hη0 : 0 < η := lt_min (lt_min one_pos (by linarith)) (div_pos (mul_pos hbe0 hR1) hden)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hηx : η < p.μ / p.κ := (min_le_left _ _).trans_lt
    ((min_le_right _ _).trans_lt (by linarith))
  have hηs : η * (2 * (1 + (p.a - 1) * B₀)) ≤ be * p.R 1 := by
    rw [← le_div_iff₀ hden]; exact min_le_right _ _
  refine ⟨η, hη0, hηx, ?_⟩
  -- `s Q > (a - 1) η B`
  have hpow : η ^ p.al * exp (-p.c * η) ≤ η := by
    have h1 : η ^ p.al ≤ η ^ (1 : ℝ) := rpow_le_rpow_of_exponent_ge hη0 hη1 hal.le
    rw [rpow_one] at h1
    have h2 : exp (-p.c * η) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [p.c_pos])
    nlinarith [rpow_pos_of_pos hη0 p.al, exp_pos (-p.c * η)]
  have hQ : (p.a - 1) * η * p.B η < p.s * p.Q η := by
    have hr := p.integral_right hη0
    have hBη := hBle η hη0
    have hRη := hRge η hη0 hη1
    have : p.s * p.Q η = be * p.R η - η ^ p.al * exp (-p.c * η) := by rw [hbe]; linarith
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hBη (mul_nonneg (by linarith : (0 : ℝ) ≤ p.a - 1) hη0.le),
      mul_le_mul_of_nonneg_left hRη hbe0.le]
  -- `s P B ≤ (a - 1) η A B`
  have hP : p.s * p.P η * p.B η ≤ (p.a - 1) * η * p.B η * p.A η := by
    have hl := p.integral_left hη0
    have hA := p.A_ge hη0
    have hpw : η ^ p.a = η * η ^ (p.a - 1) := by
      rw [show p.a = 1 + (p.a - 1) by ring, rpow_add hη0, rpow_one]; ring_nf
    rw [hl, hpw]
    have hA' : exp (-p.c * η) * η ^ (p.a - 1) ≤ (p.a - 1) * p.A η := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)] at hA; linarith
    have hBη := p.B_pos hη0
    nlinarith [mul_le_mul_of_nonneg_left hA' (mul_nonneg hη0.le hBη.le)]
  have hA := p.A_pos hη0
  have hB := p.B_pos hη0
  unfold D
  rw [sub_pos, div_lt_div_iff₀ hA hB]
  have hs := p.s_pos
  nlinarith [mul_lt_mul_of_pos_right hQ hA]

/-! ### Main results -/

/-- **Existence and shape.** The yield (4.4) of [1] has a critical point `x* > 0`; it is strictly
increasing on `(0, x*]` and strictly decreasing on `[x*, ∞)`, for all `μ > σ² / 2`, `κ > 0`,
`M > 0`. -/
theorem yieldH_unimodal :
    ∃ x, 0 < x ∧ HasDerivAt p.yieldH 0 x ∧ StrictMonoOn p.yieldH (Ioc 0 x) ∧
      StrictAntiOn p.yieldH (Ici x) := by
  obtain ⟨η, hη, hηx, hD⟩ := (le_or_gt p.al 1).elim p.exists_D_pos_of_al_le_one
    p.exists_D_pos_of_one_lt_al
  exact p.unimodal_of_D_pos hη hηx hD

/-- The hypothesis `Theorem21` holds for all parameters. -/
theorem theorem21_holds : p.Theorem21 := by
  obtain ⟨x, hx, -, hmono, hanti⟩ := p.yieldH_unimodal
  refine ⟨x, hx, fun η hη => ?_⟩
  rcases le_total η x with h | h
  · exact hmono.monotoneOn ⟨hη, h⟩ ⟨hx, le_rfl⟩ h
  · exact hanti.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr h) h

/-- **Conjecture 4.1 of [1]** for all `μ > σ² / 2`, `κ > 0`, `M > 0`: there is exactly one
threshold `x* > 0` with `H'(x*) = 0`, and it maximizes the yield (4.4) over all thresholds. -/
theorem conjecture_4_1_unconditional :
    ∃! x, 0 < x ∧ HasDerivAt p.yieldH 0 x ∧ ∀ η, 0 < η → p.yieldH η ≤ p.yieldH x :=
  p.conjecture_4_1 p.theorem21_holds

end Params

end HarvestThreshold
