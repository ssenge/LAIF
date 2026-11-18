import SigregDim.Basic

/-!
# Stiffness of a sliced regularizer against anisotropy

For a slice function `h` with a quadratic upper model of curvature `L` on `[0, ∞)`, the sliced value
at spectrum `λ` is at most `h(m) + L v/(K+2)`, where `m` is the mean and `v` the variance of the
spectrum. A quadratic lower model of curvature `ℓ` on an interval containing the spectrum gives
`h(m) + ℓ v/(K+2)` from below. The scale `m` enters at full strength, the shape `v` only with weight
`1/(K+2)`.
-/

open MeasureTheory Finset

namespace SigregDim

variable {K : ℕ} {ν : Measure (Fin K → ℝ)}

/-- Mean of a spectrum. -/
noncomputable def specMean (lam : Fin K → ℝ) : ℝ := (∑ k, lam k) / K

/-- Variance of a spectrum. -/
noncomputable def specVar (lam : Fin K → ℝ) : ℝ := (∑ k, lam k ^ 2) / K - specMean lam ^ 2

lemma integrable_comp_sliceVar (hν : SphereLike K ν) (lam : Fin K → ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) : Integrable (fun x => g (sliceVar lam x)) ν := by
  set R := ∑ k, |lam k|
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hg.continuousOn
  refine integrable_of_bdd hν (hg.measurable.comp (measurable_sliceVar lam)) C ?_
  filter_upwards [abs_sliceVar_le_ae hν lam] with x hx
  have hx' := abs_le.mp hx
  simpa [Real.norm_eq_abs] using hC _ ⟨hx'.1, hx'.2⟩

/-- The integral of the quadratic model `A + B (X - m) + (c/2)(X - m)²` around the mean. -/
lemma integral_quadModel (hν : SphereLike K ν) (hK : 0 < K) (lam : Fin K → ℝ) (A B c : ℝ) :
    ∫ x, (A + B * (sliceVar lam x - specMean lam) + c / 2 * (sliceVar lam x - specMean lam) ^ 2) ∂ν
      = A + c * specVar lam / (K + 2) := by
  have := hν.prob
  set m := specMean lam
  have hX := integrable_sliceVar hν lam
  have hX2 := integrable_sliceVar_sq hν lam
  have hrw : (fun x => A + B * (sliceVar lam x - m) + c / 2 * (sliceVar lam x - m) ^ 2) =
      fun x => (A - B * m + c / 2 * m ^ 2) + ((B - c * m) * sliceVar lam x +
        c / 2 * sliceVar lam x ^ 2) := by
    funext x; ring
  have i1 : Integrable (fun x => (B - c * m) * sliceVar lam x) ν := hX.const_mul _
  have i2 : Integrable (fun x => c / 2 * sliceVar lam x ^ 2) ν := hX2.const_mul _
  have i12 : Integrable (fun x => (B - c * m) * sliceVar lam x + c / 2 * sliceVar lam x ^ 2) ν :=
    i1.add i2
  rw [hrw, integral_add (integrable_const _) i12, integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const, integral_sliceVar hν]
  have hvar := variance_sliceVar hν hK lam
  rw [integral_sliceVar hν] at hvar
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hm : (∑ k, lam k) / K = m := rfl
  rw [hm] at hvar ⊢
  have h2 : ∫ x, sliceVar lam x ^ 2 ∂ν = 2 * specVar lam / (K + 2) + m ^ 2 := by
    rw [specVar]; linarith
  rw [h2]
  ring

/-- **Upper stiffness bound.** If `h y ≤ h x + h' x (y - x) + (L/2)(y - x)²` on `[0, ∞)`, then the
sliced value at a nonnegative spectrum is at most `h(m) + L v/(K+2)`. -/
theorem sliced_le (hν : SphereLike K ν) (hK : 0 < K) {h h' : ℝ → ℝ} {L C : ℝ}
    (hmeas : Measurable h) (hbdd : ∀ x, 0 ≤ x → |h x| ≤ C)
    (hdesc : ∀ x y, 0 ≤ x → 0 ≤ y → h y ≤ h x + h' x * (y - x) + L / 2 * (y - x) ^ 2)
    {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    sliced ν h lam ≤ h (specMean lam) + L * specVar lam / (K + 2) := by
  have hm : 0 ≤ specMean lam :=
    div_nonneg (Finset.sum_nonneg fun k _ => hlam k) (Nat.cast_nonneg _)
  rw [← integral_quadModel hν hK lam (h (specMean lam)) (h' (specMean lam)) L, sliced]
  refine integral_mono ?_ (integrable_comp_sliceVar hν lam (g := fun X =>
      h (specMean lam) + h' (specMean lam) * (X - specMean lam) + L / 2 * (X - specMean lam) ^ 2)
      (by fun_prop)) fun x => hdesc _ _ hm (sliceVar_nonneg hlam x)
  exact integrable_of_bdd hν (hmeas.comp (measurable_sliceVar lam)) C
    (Filter.Eventually.of_forall fun x => hbdd _ (sliceVar_nonneg hlam x))

/-- **Lower stiffness bound.** If `h x + h' x (y - x) + (ℓ/2)(y - x)² ≤ h y` on an interval
`[lo, hi] ⊆ [0, ∞)` that contains the spectrum, then the sliced value is at least
`h(m) + ℓ v/(K+2)`. -/
theorem le_sliced (hν : SphereLike K ν) (hK : 0 < K) {h h' : ℝ → ℝ} {ℓ C lo hi : ℝ}
    (hmeas : Measurable h) (hbdd : ∀ x, 0 ≤ x → |h x| ≤ C) (hlo0 : 0 ≤ lo)
    (hasc : ∀ x y, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi →
      h x + h' x * (y - x) + ℓ / 2 * (y - x) ^ 2 ≤ h y)
    {lam : Fin K → ℝ} (hlo : ∀ k, lo ≤ lam k) (hhi : ∀ k, lam k ≤ hi) :
    h (specMean lam) + ℓ * specVar lam / (K + 2) ≤ sliced ν h lam := by
  have hlam : ∀ k, 0 ≤ lam k := fun k => hlo0.trans (hlo k)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hmlo : lo ≤ specMean lam := by
    rw [specMean, le_div_iff₀ hKpos]
    calc lo * K = ∑ _k : Fin K, lo := by simp [mul_comm]
      _ ≤ ∑ k, lam k := Finset.sum_le_sum fun k _ => hlo k
  have hmhi : specMean lam ≤ hi := by
    rw [specMean, div_le_iff₀ hKpos]
    calc ∑ k, lam k ≤ ∑ _k : Fin K, hi := Finset.sum_le_sum fun k _ => hhi k
      _ = hi * K := by simp [mul_comm]
  rw [← integral_quadModel hν hK lam (h (specMean lam)) (h' (specMean lam)) ℓ, sliced]
  refine integral_mono_ae (integrable_comp_sliceVar hν lam (g := fun X =>
      h (specMean lam) + h' (specMean lam) * (X - specMean lam) + ℓ / 2 * (X - specMean lam) ^ 2)
      (by fun_prop))
    (integrable_of_bdd hν (hmeas.comp (measurable_sliceVar lam)) C
      (Filter.Eventually.of_forall fun x => hbdd _ (sliceVar_nonneg hlam x))) ?_
  filter_upwards [sliceVar_mem_ae hν hlo hhi] with x hx
  exact hasc _ _ hmlo hmhi hx.1 hx.2

end SigregDim
