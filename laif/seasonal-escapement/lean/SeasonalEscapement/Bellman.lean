import Mathlib

/-!
# Capped constant escapement in one Bellman step

Annual season: the population before the season is `y ≥ 0`, the escapement `s` (what is left after
the season) satisfies `max 0 (y - Q) ≤ s ≤ y`, so the cull `y - s` is at most the quota cap `Q`.
With a continuation value `φ`, the value of escapement `s` at state `y` is `y + φ s`, where
`φ s = -s + α E V(F(s, ξ))`.

If `φ` is concave on `[0, ∞)` with a maximizer `w`, the optimal escapement is the clamp of `w` to the
feasible interval (capped constant escapement), and the new value `V y = y + φ (esc w Q y)` is again
concave and nondecreasing. If `V` is concave and nondecreasing and every `F (·, ξ)` is concave and
nondecreasing, the next `φ` is concave and `s + φ s` is nondecreasing. These are the steps of the
induction that makes capped constant escapement optimal for every horizon and discount factor.
-/

open Set MeasureTheory

namespace SeasonalEscapement

/-- Feasible escapements at population `y` with quota cap `Q`. -/
def feasible (Q y : ℝ) : Set ℝ := Icc (max 0 (y - Q)) y

/-- Capped constant escapement with target `w`: the clamp of `w` to the feasible interval. -/
noncomputable def esc (w Q y : ℝ) : ℝ := max (max 0 (y - Q)) (min w y)

lemma esc_mem {w Q y : ℝ} (hQ : 0 ≤ Q) (hy : 0 ≤ y) : esc w Q y ∈ feasible Q y :=
  ⟨le_max_left _ _, max_le (max_le hy (by linarith)) (min_le_right _ _)⟩

/-- A concave function with maximizer `w` attains its maximum over `[a, b] ⊆ [0, ∞)` at the clamp
of `w`. -/
lemma le_clamp {φ : ℝ → ℝ} {w a b s : ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) (hw : 0 ≤ w)
    (hmax : IsMaxOn φ (Ici 0) w) (ha : 0 ≤ a) (hs : s ∈ Icc a b) :
    φ s ≤ φ (max a (min w b)) := by
  have hs0 : (0 : ℝ) ≤ s := ha.trans hs.1
  have hws : φ s ≤ φ w := hmax (mem_Ici.mpr hs0)
  rcases le_or_gt w a with hwa | hwa
  · have hc : max a (min w b) = a := max_eq_left ((min_le_left _ _).trans hwa)
    rw [hc]
    have := hφ.min_le_of_mem_Icc (mem_Ici.mpr hw) (mem_Ici.mpr hs0) ⟨hwa, hs.1⟩
    rw [min_eq_right hws] at this; exact this
  rcases le_or_gt w b with hwb | hwb
  · rw [min_eq_left hwb, max_eq_right hwa.le]; exact hws
  · have hc : max a (min w b) = b := by rw [min_eq_right hwb.le, max_eq_right (hs.1.trans hs.2)]
    rw [hc]
    have := hφ.min_le_of_mem_Icc (mem_Ici.mpr hs0) (mem_Ici.mpr hw) ⟨hs.2, hwb.le⟩
    rw [min_eq_left hws] at this; exact this

variable {φ : ℝ → ℝ} {w Q : ℝ}

/-- New value after one step with capped constant escapement. -/
noncomputable def value (φ : ℝ → ℝ) (w Q y : ℝ) : ℝ := y + φ (esc w Q y)

/-- Capped constant escapement is optimal in the Bellman step. -/
theorem esc_optimal (hφ : ConcaveOn ℝ (Ici 0) φ) (hw : 0 ≤ w) (hmax : IsMaxOn φ (Ici 0) w)
    {y s : ℝ} (hs : s ∈ feasible Q y) : y + φ s ≤ value φ w Q y := by
  unfold value esc
  linarith [le_clamp hφ hw hmax (le_max_left 0 (y - Q)) hs]

/-- The new value is concave. -/
theorem value_concave (hφ : ConcaveOn ℝ (Ici 0) φ) (hw : 0 ≤ w) (hmax : IsMaxOn φ (Ici 0) w)
    (hQ : 0 ≤ Q) : ConcaveOn ℝ (Ici 0) (value φ w Q) := by
  refine ⟨convex_Ici 0, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
  have hy₁' : (0 : ℝ) ≤ y₁ := hy₁
  have hy₂' : (0 : ℝ) ≤ y₂ := hy₂
  set e₁ := esc w Q y₁; set e₂ := esc w Q y₂
  have m₁ := esc_mem (w := w) hQ hy₁'; have m₂ := esc_mem (w := w) hQ hy₂'
  have h0 : (0 : ℝ) ≤ e₁ := (le_max_left _ _).trans m₁.1
  have h0' : (0 : ℝ) ≤ e₂ := (le_max_left _ _).trans m₂.1
  -- the combination of the two escapements is feasible for the combined state
  have hfeas : a • e₁ + b • e₂ ∈ feasible Q (a • y₁ + b • y₂) := by
    simp only [smul_eq_mul]
    refine ⟨max_le (by positivity) ?_, ?_⟩
    · have q₁ : y₁ - Q ≤ e₁ := (le_max_right _ _).trans m₁.1
      have q₂ : y₂ - Q ≤ e₂ := (le_max_right _ _).trans m₂.1
      nlinarith
    · nlinarith [m₁.2, m₂.2]
  have hc := hφ.2 (mem_Ici.mpr h0) (mem_Ici.mpr h0') ha hb hab
  have ho := esc_optimal hφ hw hmax hfeas
  simp only [value, smul_eq_mul] at *
  nlinarith

/-- The new value is nondecreasing when `s + φ s` is nondecreasing. -/
theorem value_monotone (hφ : ConcaveOn ℝ (Ici 0) φ) (hw : 0 ≤ w) (hmax : IsMaxOn φ (Ici 0) w)
    (hQ : 0 ≤ Q) (hmono : MonotoneOn (fun s => s + φ s) (Ici 0)) :
    MonotoneOn (value φ w Q) (Ici 0) := by
  intro y₁ hy₁ y₂ _ h12
  have hy₁' : (0 : ℝ) ≤ y₁ := hy₁
  set e := esc w Q y₁
  have m := esc_mem (w := w) hQ hy₁'
  have he0 : 0 ≤ e := (le_max_left _ _).trans m.1
  have heQ : y₁ - Q ≤ e := (le_max_right _ _).trans m.1
  show y₁ + φ e ≤ value φ w Q y₂
  rcases le_total (y₂ - Q) e with h | h
  · have hopt := esc_optimal (y := y₂) hφ hw hmax ⟨max_le he0 h, m.2.trans h12⟩
    linarith
  · have h0 : 0 ≤ y₂ - Q := he0.trans h
    have hopt := esc_optimal (y := y₂) hφ hw hmax ⟨max_le h0 le_rfl, by linarith⟩
    have hmon := hmono (mem_Ici.mpr he0) (mem_Ici.mpr h0) h
    simp only at hmon
    linarith

/-- The next continuation value `φ' s = -s + α ∫ V (F s ξ) dμ` is concave, and `s + φ' s` is
nondecreasing, when `V` is concave and nondecreasing and every `F (·, ξ)` is concave and
nondecreasing with values in `[0, ∞)`. -/
theorem next_concave {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {V : ℝ → ℝ}
    {F : ℝ → Ω → ℝ} {α : ℝ} (hα : 0 ≤ α) (hV : ConcaveOn ℝ (Ici 0) V)
    (hVm : MonotoneOn V (Ici 0)) (hF : ∀ ξ, ConcaveOn ℝ (Ici 0) (fun s => F s ξ))
    (hFm : ∀ ξ, MonotoneOn (fun s => F s ξ) (Ici 0)) (hF0 : ∀ s ξ, 0 ≤ F s ξ)
    (hint : ∀ s, 0 ≤ s → Integrable (fun ξ => V (F s ξ)) μ) :
    ConcaveOn ℝ (Ici 0) (fun s => -s + α * ∫ ξ, V (F s ξ) ∂μ) ∧
      MonotoneOn (fun s => s + (-s + α * ∫ ξ, V (F s ξ) ∂μ)) (Ici 0) := by
  refine ⟨⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩, fun x hx y hy hxy => ?_⟩
  · have hx' : (0 : ℝ) ≤ x := hx
    have hy' : (0 : ℝ) ≤ y := hy
    have hxy : 0 ≤ a * x + b * y := by positivity
    have hpt : ∀ ξ, a * V (F x ξ) + b * V (F y ξ) ≤ V (F (a * x + b * y) ξ) := fun ξ => by
      have h1 := hV.2 (mem_Ici.mpr (hF0 x ξ)) (mem_Ici.mpr (hF0 y ξ)) ha hb hab
      have h2 := (hF ξ).2 hx hy ha hb hab
      simp only [smul_eq_mul] at h1 h2
      have hc : 0 ≤ a * F x ξ + b * F y ξ := by have := hF0 x ξ; have := hF0 y ξ; positivity
      exact h1.trans (hVm (mem_Ici.mpr hc) (mem_Ici.mpr (hF0 _ ξ)) h2)
    have hI := integral_mono (((hint x hx).const_mul a).add ((hint y hy).const_mul b))
      (hint _ hxy) hpt
    simp only [Pi.add_apply] at hI
    rw [integral_add ((hint x hx).const_mul a) ((hint y hy).const_mul b), integral_const_mul,
      integral_const_mul] at hI
    simp only [smul_eq_mul]
    have : a * (α * ∫ ξ, V (F x ξ) ∂μ) + b * (α * ∫ ξ, V (F y ξ) ∂μ) ≤
        α * ∫ ξ, V (F (a * x + b * y) ξ) ∂μ := by nlinarith
    nlinarith
  · simp only [add_neg_cancel_left]
    exact mul_le_mul_of_nonneg_left (integral_mono (hint x hx) (hint y hy)
      fun ξ => hVm (mem_Ici.mpr (hF0 x ξ)) (mem_Ici.mpr (hF0 y ξ)) (hFm ξ hx hy hxy)) hα

/-! ### Content -/

/-- With target `1` and cap `1/2`, a population of `3` is culled by the cap, not down to the target:
capped escapement differs from constant escapement. -/
example : esc 1 (1 / 2) 3 = 5 / 2 := by norm_num [esc]

/-- The hypotheses of the Bellman step hold together: `φ s = min s (2 - s)` is concave with
maximizer `1`, and `s + φ s` is nondecreasing. -/
theorem nonvacuous :
    ConcaveOn ℝ (Ici 0) (fun s : ℝ => min s (2 - s)) ∧ IsMaxOn (fun s : ℝ => min s (2 - s)) (Ici 0) 1 ∧
      MonotoneOn (fun s : ℝ => s + min s (2 - s)) (Ici 0) := by
  refine ⟨?_, fun s _ => ?_, fun x _ y _ hxy => ?_⟩
  · exact (concaveOn_id (convex_Ici 0)).inf ((concaveOn_const 2 (convex_Ici 0)).sub
      (convexOn_id (convex_Ici 0)))
  · show min s (2 - s) ≤ min 1 (2 - 1)
    calc min s (2 - s) ≤ 1 := by
          rcases le_total s 1 with h | h
          exacts [(min_le_left _ _).trans h, (min_le_right _ _).trans (by linarith)]
      _ = min 1 (2 - 1) := by norm_num
  · simp only
    rcases le_total x (2 - x) with h | h <;> rcases le_total y (2 - y) with h' | h' <;>
      simp [h, h'] <;> linarith

end SeasonalEscapement
