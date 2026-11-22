import Mathlib

/-!
# No locally slope-bounded encoder is exactly normal in an over-complete embedding

For `N < M`, the range of a locally slope-bounded map `ℝ^N → ℝ^M` (locally `‖h x - h y‖ ≤ C ‖x - y‖`) has
dimension at most `N`, hence volume zero (`volume_range_eq_zero`). So such a map sends no probability measure to a law with a density, in
particular not to the standard normal law `N(0, I_M)` (`not_map_eq`, Proposition 3).
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace OverIdent

/-- The range of a locally slope-bounded map `ℝ^N → ℝ^M` with `N < M` has volume 0. -/
theorem volume_range_eq_zero {N M : ℕ} (hNM : N < M) {h : (Fin N → ℝ) → (Fin M → ℝ)}
    (hh : ∀ x, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith C h s) : volume (range h) = 0 := by
  have hd : dimH (range h) < ((M : ℝ≥0) : ℝ≥0∞) := by
    calc dimH (range h) ≤ dimH (univ : Set (Fin N → ℝ)) := dimH_range_le_of_locally_lipschitzOn hh
      _ = N := Real.dimH_univ_pi_fin N
      _ < ((M : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hNM
  have e : (μH[(M : ℝ≥0)] : Measure (Fin M → ℝ)) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin M))
  rw [← e]; exact hausdorffMeasure_of_dimH_lt hd

/-- **Proposition 3.** For `N < M`, no locally slope-bounded map sends a probability measure on `ℝ^N` to a measure on
`ℝ^M` that is absolutely continuous with respect to volume, such as `N(0, I_M)`. -/
theorem not_map_eq {N M : ℕ} (hNM : N < M) {h : (Fin N → ℝ) → (Fin M → ℝ)}
    (hh : ∀ x, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith C h s) (μ : Measure (Fin N → ℝ))
    [IsProbabilityMeasure μ] (ν : Measure (Fin M → ℝ)) (hν : ν ≪ volume) : μ.map h ≠ ν := by
  intro e
  have hc : Continuous h := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨C, s, hs, hL⟩ := hh x
    exact hL.continuousOn.continuousAt hs
  have hS0 : volume (toMeasurable volume (range h)) = 0 := by
    rw [measure_toMeasurable]; exact volume_range_eq_zero hNM hh
  have h1 : μ.map h (toMeasurable volume (range h)) = 1 := by
    rw [Measure.map_apply hc.measurable (measurableSet_toMeasurable _ _)]
    have : h ⁻¹' toMeasurable volume (range h) = univ :=
      eq_univ_of_forall fun x => subset_toMeasurable _ _ (mem_range_self x)
    rw [this, measure_univ]
  rw [e, hν hS0] at h1
  exact zero_ne_one h1

end OverIdent
