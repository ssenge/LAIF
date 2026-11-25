import SeasonalEscapement.Bellman

/-!
# Capped constant escapement for hump-shaped recruitment

Recruitment such as the Ricker map `s ↦ ξ s exp (r (1 - s))` is not concave on `[0, ∞)`. It is
nondecreasing and concave on `[0, ĥ]` (here `ĥ = 1 / r`) and never larger beyond `ĥ` than at `ĥ`.
If every population that can occur is at most `ĥ + Q`, one season can bring it back to `[0, ĥ]`, and the
Bellman step of `Bellman.lean` goes through with `[0, ĥ]` in place of `[0, ∞)`: the optimal escapement
is capped constant escapement, and concavity and monotonicity of the value on `[0, ĥ + Q]` propagate.
Without a cap (`Q` at least the largest population) this covers overcompensating recruitment in general.
-/

open Set MeasureTheory

namespace SeasonalEscapement

variable {φ : ℝ → ℝ} {w Q hh : ℝ}

/-- Clamp principle on a convex set `D`: a concave function on `D` with maximizer `w ∈ D` attains its
maximum over `[a, b]` at the clamp of `w`, when `a, b ∈ D`. -/
lemma le_clamp_on {D : Set ℝ} {a b s : ℝ} (hφ : ConcaveOn ℝ D φ) (hwD : w ∈ D)
    (hmax : IsMaxOn φ D w) (ha : a ∈ D) (hb : b ∈ D) (hs : s ∈ Icc a b) :
    φ s ≤ φ (max a (min w b)) := by
  have hsD : s ∈ D := hφ.1.ordConnected.out ha hb hs
  have hws : φ s ≤ φ w := hmax hsD
  rcases le_or_gt w a with hwa | hwa
  · rw [max_eq_left ((min_le_left _ _).trans hwa)]
    have := hφ.min_le_of_mem_Icc hwD hsD ⟨hwa, hs.1⟩
    rwa [min_eq_right hws] at this
  rcases le_or_gt w b with hwb | hwb
  · rw [min_eq_left hwb, max_eq_right hwa.le]; exact hws
  · rw [min_eq_right hwb.le, max_eq_right (hs.1.trans hs.2)]
    have := hφ.min_le_of_mem_Icc hsD hwD ⟨hs.2, hwb.le⟩
    rwa [min_eq_left hws] at this

/-- On the reachable states `[0, ĥ + Q]` the capped escapement lies in `[0, ĥ]`. -/
lemma esc_mem_hump (hQ : 0 ≤ Q) (hw : w ∈ Icc 0 hh) {y : ℝ} (hy : y ∈ Icc 0 (hh + Q)) :
    esc w Q y ∈ Icc 0 hh :=
  ⟨(le_max_left _ _).trans (le_max_left _ _),
    max_le (max_le (hw.1.trans hw.2) (by linarith [hy.2])) ((min_le_left _ _).trans hw.2)⟩

/-- Capped constant escapement is optimal in the Bellman step, for `φ` concave on `[0, ĥ]` with
maximizer `w` there and `φ s ≤ φ ĥ` beyond `ĥ`. -/
theorem esc_optimal_hump (hφ : ConcaveOn ℝ (Icc 0 hh) φ) (hw : w ∈ Icc 0 hh)
    (hmax : IsMaxOn φ (Icc 0 hh) w) (hbey : ∀ s, hh ≤ s → φ s ≤ φ hh) (hQ : 0 ≤ Q)
    {y s : ℝ} (hy : y ∈ Icc 0 (hh + Q)) (hs : s ∈ feasible Q y) : y + φ s ≤ value φ w Q y := by
  have hh0 : 0 ≤ hh := hw.1.trans hw.2
  set a := max 0 (y - Q)
  have ha : a ∈ Icc 0 hh := ⟨le_max_left _ _, max_le hh0 (by linarith [hy.2])⟩
  have hb : min y hh ∈ Icc 0 hh := ⟨le_min hy.1 hh0, min_le_right _ _⟩
  have hesc : esc w Q y = max a (min w (min y hh)) := by
    unfold esc; congr 1
    rw [← min_assoc, min_comm w y, min_assoc, min_eq_left hw.2]
  -- the case `s ≤ ĥ`
  have key : ∀ t ∈ Icc a (min y hh), φ t ≤ φ (esc w Q y) := fun t ht => by
    rw [hesc]; exact le_clamp_on hφ hw hmax ha hb ht
  unfold value
  rcases le_total s hh with h | h
  · linarith [key s ⟨hs.1, le_min hs.2 h⟩]
  · have hhy : hh ≤ y := h.trans hs.2
    have := key hh ⟨ha.2, le_min hhy le_rfl⟩
    linarith [hbey s h]

theorem value_concave_hump (hφ : ConcaveOn ℝ (Icc 0 hh) φ) (hw : w ∈ Icc 0 hh)
    (hmax : IsMaxOn φ (Icc 0 hh) w) (hbey : ∀ s, hh ≤ s → φ s ≤ φ hh) (hQ : 0 ≤ Q) :
    ConcaveOn ℝ (Icc 0 (hh + Q)) (value φ w Q) := by
  refine ⟨convex_Icc 0 _, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
  set e₁ := esc w Q y₁; set e₂ := esc w Q y₂
  have m₁ := esc_mem (w := w) hQ hy₁.1; have m₂ := esc_mem (w := w) hQ hy₂.1
  have d₁ := esc_mem_hump hQ hw hy₁; have d₂ := esc_mem_hump hQ hw hy₂
  have hy : a • y₁ + b • y₂ ∈ Icc 0 (hh + Q) := (convex_Icc 0 _) hy₁ hy₂ ha hb hab
  have hfeas : a • e₁ + b • e₂ ∈ feasible Q (a • y₁ + b • y₂) := by
    simp only [smul_eq_mul]
    refine ⟨max_le (by nlinarith [d₁.1, d₂.1]) ?_, ?_⟩
    · have q₁ : y₁ - Q ≤ e₁ := (le_max_right _ _).trans m₁.1
      have q₂ : y₂ - Q ≤ e₂ := (le_max_right _ _).trans m₂.1
      nlinarith
    · nlinarith [m₁.2, m₂.2]
  have hc := hφ.2 d₁ d₂ ha hb hab
  have ho := esc_optimal_hump hφ hw hmax hbey hQ hy hfeas
  simp only [value, smul_eq_mul] at *
  nlinarith

theorem value_monotone_hump (hφ : ConcaveOn ℝ (Icc 0 hh) φ) (hw : w ∈ Icc 0 hh)
    (hmax : IsMaxOn φ (Icc 0 hh) w) (hbey : ∀ s, hh ≤ s → φ s ≤ φ hh) (hQ : 0 ≤ Q)
    (hmono : MonotoneOn (fun s => s + φ s) (Icc 0 hh)) :
    MonotoneOn (value φ w Q) (Icc 0 (hh + Q)) := by
  intro y₁ hy₁ y₂ hy₂ h12
  set e := esc w Q y₁
  have m := esc_mem (w := w) hQ hy₁.1
  have d := esc_mem_hump hQ hw hy₁
  have heQ : y₁ - Q ≤ e := (le_max_right _ _).trans m.1
  show y₁ + φ e ≤ value φ w Q y₂
  rcases le_total (y₂ - Q) e with h | h
  · have hopt := esc_optimal_hump hφ hw hmax hbey hQ hy₂ ⟨max_le d.1 h, m.2.trans h12⟩
    linarith
  · have h0 : 0 ≤ y₂ - Q := d.1.trans h
    have hopt := esc_optimal_hump hφ hw hmax hbey hQ hy₂ ⟨max_le h0 le_rfl, by linarith⟩
    have hmon := hmono d ⟨h0, by linarith [hy₂.2]⟩ h
    simp only at hmon
    linarith

/-- The next continuation value keeps the hypotheses: concave on `[0, ĥ]`, `s + φ' s` nondecreasing
there, and `φ' s ≤ φ' ĥ` beyond `ĥ`, when `V` is concave and nondecreasing on `[0, ĥ + Q]`, every
`F (·, ξ)` is concave and nondecreasing on `[0, ĥ]`, never larger beyond `ĥ` than at `ĥ`, and takes values
in `[0, ĥ + Q]`. -/
theorem next_hump {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {V : ℝ → ℝ}
    {F : ℝ → Ω → ℝ} {α : ℝ} (hα : 0 ≤ α) (hh0 : 0 ≤ hh) (hV : ConcaveOn ℝ (Icc 0 (hh + Q)) V)
    (hVm : MonotoneOn V (Icc 0 (hh + Q))) (hF : ∀ ξ, ConcaveOn ℝ (Icc 0 hh) (fun s => F s ξ))
    (hFm : ∀ ξ, MonotoneOn (fun s => F s ξ) (Icc 0 hh)) (hFb : ∀ s ξ, F s ξ ∈ Icc 0 (hh + Q))
    (hFh : ∀ s ξ, hh ≤ s → F s ξ ≤ F hh ξ) (hint : ∀ s, 0 ≤ s → Integrable (fun ξ => V (F s ξ)) μ) :
    ConcaveOn ℝ (Icc 0 hh) (fun s => -s + α * ∫ ξ, V (F s ξ) ∂μ) ∧
      MonotoneOn (fun s => s + (-s + α * ∫ ξ, V (F s ξ) ∂μ)) (Icc 0 hh) ∧
      ∀ s, hh ≤ s → -s + α * ∫ ξ, V (F s ξ) ∂μ ≤ -hh + α * ∫ ξ, V (F hh ξ) ∂μ := by
  refine ⟨⟨convex_Icc 0 hh, fun x hx y hy a b ha hb hab => ?_⟩, fun x hx y hy hxy => ?_,
    fun s hs => ?_⟩
  · have hxy : 0 ≤ a * x + b * y := by have := hx.1; have := hy.1; positivity
    have hpt : ∀ ξ, a * V (F x ξ) + b * V (F y ξ) ≤ V (F (a * x + b * y) ξ) := fun ξ => by
      have h1 := hV.2 (hFb x ξ) (hFb y ξ) ha hb hab
      have h2 := (hF ξ).2 hx hy ha hb hab
      simp only [smul_eq_mul] at h1 h2
      have hc : a * F x ξ + b * F y ξ ∈ Icc 0 (hh + Q) := by
        simpa [smul_eq_mul] using (convex_Icc 0 (hh + Q)) (hFb x ξ) (hFb y ξ) ha hb hab
      exact h1.trans (hVm hc (hFb _ ξ) h2)
    have hI := integral_mono (((hint x hx.1).const_mul a).add ((hint y hy.1).const_mul b))
      (hint _ hxy) hpt
    simp only [Pi.add_apply] at hI
    rw [integral_add ((hint x hx.1).const_mul a) ((hint y hy.1).const_mul b), integral_const_mul,
      integral_const_mul] at hI
    simp only [smul_eq_mul]
    have : a * (α * ∫ ξ, V (F x ξ) ∂μ) + b * (α * ∫ ξ, V (F y ξ) ∂μ) ≤
        α * ∫ ξ, V (F (a * x + b * y) ξ) ∂μ := by nlinarith
    nlinarith
  · simp only [add_neg_cancel_left]
    exact mul_le_mul_of_nonneg_left (integral_mono (hint x hx.1) (hint y hy.1)
      fun ξ => hVm (hFb x ξ) (hFb y ξ) (hFm ξ hx hy hxy)) hα
  · have hI := integral_mono (hint s (hh0.trans hs)) (hint hh hh0)
      fun ξ => hVm (hFb s ξ) (hFb hh ξ) (hFh s ξ hs)
    nlinarith [mul_le_mul_of_nonneg_left hI hα]

/-- The hump hypotheses hold together: `φ s = min s (1 - s)` on `[0, 1]` (maximizer `1/2`), with
`φ s ≤ φ 1` beyond `1`. -/
theorem nonvacuous_hump :
    ConcaveOn ℝ (Icc 0 1) (fun s : ℝ => min s (1 - s)) ∧
      IsMaxOn (fun s : ℝ => min s (1 - s)) (Icc 0 1) (1 / 2) ∧
      (∀ s : ℝ, 1 ≤ s → min s (1 - s) ≤ min 1 (1 - 1)) := by
  refine ⟨(concaveOn_id (convex_Icc 0 1)).inf ((concaveOn_const 1 (convex_Icc 0 1)).sub
      (convexOn_id (convex_Icc 0 1))), fun s _ => ?_, fun s hs => ?_⟩
  · show min s (1 - s) ≤ min (1 / 2) (1 - 1 / 2)
    calc min s (1 - s) ≤ 1 / 2 := by
          rcases le_total s (1 / 2) with h | h
          exacts [(min_le_left _ _).trans h, (min_le_right _ _).trans (by linarith)]
      _ = min (1 / 2) (1 - 1 / 2) := by norm_num
  · rw [min_eq_right (by linarith : 1 - s ≤ s)]; norm_num; linarith

end SeasonalEscapement
