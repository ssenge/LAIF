import SigregDim.Rank
import SigregDim.SliceD
import SigregDim.Witness

/-!
# Existence of minimizers and the SIGReg slice function

If `h` is continuous and bounded below on `[0, ∞)` and all costs are at least `c₁ > 0`, the reduced
objective has a global minimizer over nonnegative spectra. The objective grows at least like
`c₁ ∑ₖ λₖ`, so a minimizer lies in a compact box, and the sliced term is continuous on that box by
dominated convergence. For the SIGReg slice function `D` this gives minimizers to which the
gap and rank theorems apply, and these hypotheses hold for the discrete law `witness K`.
-/

open MeasureTheory Finset Set

namespace SigregDim

variable {K : ℕ} {ν : Measure (Fin K → ℝ)}

lemma sliceVar_le_of_sphere {lam : Fin K → ℝ} {R : ℝ} (hR : ∀ k, lam k ≤ R) {x : Fin K → ℝ}
    (hx : ∑ k, x k ^ 2 = 1) : sliceVar lam x ≤ R := by
  calc sliceVar lam x ≤ ∑ k, R * x k ^ 2 :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hR k) (sq_nonneg _)
    _ = R := by rw [← Finset.mul_sum, hx, mul_one]

lemma continuous_sliceVar_lam (x : Fin K → ℝ) : Continuous fun lam : Fin K → ℝ => sliceVar lam x := by
  unfold sliceVar; fun_prop

lemma continuous_h_sliceVar {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0)) {lam : Fin K → ℝ}
    (hlam : ∀ k, 0 ≤ lam k) : Continuous fun x => h (sliceVar lam x) :=
  hcont.comp_continuous (by unfold sliceVar; fun_prop) fun x => sliceVar_nonneg hlam x

lemma integrable_h_of_cont (hν : SphereLike K ν) {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0))
    {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) : Integrable (fun x => h (sliceVar lam x)) ν := by
  have := hν.prob
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (∑ k, lam k) ⊆ Ici 0))
  refine Integrable.of_bound (continuous_h_sliceVar hcont hlam).aestronglyMeasurable C ?_
  filter_upwards [hν.sphere] with x hx
  exact hC _ ⟨sliceVar_nonneg hlam x, sliceVar_le_of_sphere
    (fun k => Finset.single_le_sum (f := lam) (fun l _ => hlam l) (Finset.mem_univ k)) hx⟩

lemma le_sliced_of_lower' (hν : SphereLike K ν) {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0))
    {lo : ℝ} (hlow : ∀ s, 0 ≤ s → lo ≤ h s) {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    lo ≤ sliced ν h lam := by
  have := hν.prob
  unfold sliced
  calc lo = ∫ _x, lo ∂ν := by simp
    _ ≤ ∫ x, h (sliceVar lam x) ∂ν :=
        integral_mono (integrable_const _) (integrable_h_of_cont hν hcont hlam)
          fun x => hlow _ (sliceVar_nonneg hlam x)

/-- The sliced value is continuous on every box `[0, R]^K`. -/
lemma continuousOn_sliced (hν : SphereLike K ν) {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0))
    (R : ℝ) : ContinuousOn (sliced ν h) {lam | ∀ k, lam k ∈ Icc 0 R} := by
  have := hν.prob
  have hRc : ContinuousOn h (Icc 0 R) := hcont.mono Icc_subset_Ici_self
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hRc
  have hmaps : ∀ x, MapsTo (fun lam : Fin K → ℝ => sliceVar lam x)
      {lam | ∀ k, lam k ∈ Icc 0 R} (Ici 0) :=
    fun x lam hlam => sliceVar_nonneg (fun k => (hlam k).1) x
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · intro lam hlam
    exact (continuous_h_sliceVar hcont fun k => (hlam k).1).aestronglyMeasurable
  · intro lam hlam
    filter_upwards [hν.sphere] with x hx
    exact hC _ ⟨sliceVar_nonneg (fun k => (hlam k).1) x,
      sliceVar_le_of_sphere (fun k => (hlam k).2) hx⟩
  · exact Filter.Eventually.of_forall fun x =>
      hcont.comp (continuous_sliceVar_lam x).continuousOn (hmaps x)

/-- **Existence of a minimizer.** -/
theorem exists_minimizer (hν : SphereLike K ν) {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0))
    {lo : ℝ} (hlow : ∀ s, 0 ≤ s → lo ≤ h s) {c : Fin K → ℝ} {c₁ μ : ℝ} (hc₁pos : 0 < c₁)
    (hc₁ : ∀ k, c₁ ≤ c k) (hμ : 0 ≤ μ) : ∃ lam, IsMinimizer ν h c μ lam := by
  have := hν.prob
  set F := objective ν h c μ
  -- value at the origin
  have hF0 : F 0 = μ * h 0 := by
    simp only [F, objective, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, sliced]
    simp [sliceVar]
  -- lower bound by the trace
  have hlowF : ∀ lam : Fin K → ℝ, (∀ k, 0 ≤ lam k) → c₁ * ∑ k, lam k + μ * lo ≤ F lam := by
    intro lam hlam
    have h2 := le_sliced_of_lower' hν hcont hlow hlam
    have h3 : c₁ * ∑ k, lam k ≤ ∑ k, c k * lam k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hc₁ k) (hlam k)
    simp only [F, objective]
    nlinarith [mul_le_mul_of_nonneg_left h2 hμ]
  set R := max 0 ((μ * h 0 - μ * lo) / c₁) + 1
  have hR0 : 0 < R := by positivity
  set S : Set (Fin K → ℝ) := {lam | ∀ k, lam k ∈ Icc 0 R}
  have hS : IsCompact S := by
    have : S = Set.pi univ fun _ => Icc 0 R := by ext; simp only [S, Set.mem_pi, Set.mem_univ, true_implies]; rfl
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_Icc
  have h0S : (0 : Fin K → ℝ) ∈ S := fun k => ⟨le_rfl, hR0.le⟩
  have hFc : ContinuousOn F S := by
    have hsum : Continuous fun lam : Fin K → ℝ => ∑ k, c k * lam k := by fun_prop
    exact hsum.continuousOn.add (continuousOn_const.mul (continuousOn_sliced hν hcont R))
  obtain ⟨lam, hlamS, hmin⟩ := hS.exists_isMinOn ⟨0, h0S⟩ hFc
  refine ⟨lam, fun k => (hlamS k).1, fun lam' hlam' => ?_⟩
  by_cases hin : lam' ∈ S
  · exact hmin hin
  · -- outside the box the objective exceeds its value at the origin
    have hk' : ∃ k, ¬ lam' k ≤ R := by
      by_contra hcon
      push Not at hcon
      exact hin fun k => ⟨hlam' k, hcon k⟩
    obtain ⟨k, hk⟩ := hk'
    have hkR : R < lam' k := not_le.1 hk
    have hsum : lam' k ≤ ∑ l, lam' l :=
      Finset.single_le_sum (f := lam') (fun l _ => hlam' l) (Finset.mem_univ k)
    have hbig : μ * h 0 - μ * lo < c₁ * ∑ l, lam' l := by
      have : (μ * h 0 - μ * lo) / c₁ < ∑ l, lam' l := by
        have := le_max_right 0 ((μ * h 0 - μ * lo) / c₁)
        linarith
      rw [div_lt_iff₀ hc₁pos] at this
      linarith
    have := hlowF lam' hlam'
    have hle : F lam ≤ F 0 := hmin h0S
    show F lam ≤ F lam'
    linarith

lemma epD'_one : epD' 1 = 0 := by
  unfold epD'
  rw [show (2 * (1 : ℝ) + 1) = 3 by norm_num, show ((1 : ℝ) + 2) = 3 by norm_num]
  ring

lemma continuousOn_epD : ContinuousOn epD (Ici 0) :=
  fun s hs => (hasDerivAt_epD hs).continuousAt.continuousWithinAt

lemma epD_ge : ∀ s, 0 ≤ s → (-11 : ℝ) ≤ epD s :=
  fun s hs => (abs_le.1 (abs_epD_le hs)).1

/-- **Instance for the SIGReg slice function.** For every law with the sphere moments (for example `witness K`) and
costs `c₁ ≤ cₖ` increasing by at least `δ` per index, the reduced objective with slice function
`D` has a global minimizer. Every such minimizer orders its spectrum against the costs, satisfies
the gap bound with `L = 8`, and has at most `r` active directions with
`r (r - 1) ≤ 32 μ (∑ₖ cₖ + 11 μ) / (c₁ δ K (K+2))`. -/
theorem epD_minimizer (hν : SphereLike K ν) {c : Fin K → ℝ} {c₁ μ δ : ℝ} (hμ : 0 < μ)
    (hc₁pos : 0 < c₁) (hc₁ : ∀ k, c₁ ≤ c k) (hδ : 0 < δ)
    (hcgap : ∀ k l : Fin K, k < l → δ * ((l : ℝ) - (k : ℝ)) ≤ c l - c k) :
    ∃ lam, IsMinimizer ν epD c μ lam ∧
      (∀ i j, c i < c j → lam j ≤ lam i) ∧
      (∀ i j, c i < c j → 0 < lam j → c j - c i ≤ 2 * 8 * μ * (lam i - lam j) / (K * (K + 2))) ∧
      (let r : ℝ := ((univ : Finset (Fin K)).filter fun k => 0 < lam k).card
       r * (r - 1) ≤ 4 * 8 * μ * (∑ k, c k + μ * (epD 1 - (-11))) / (c₁ * δ * (K * (K + 2)))) := by
  obtain ⟨lam, hmin⟩ := exists_minimizer hν continuousOn_epD epD_ge hc₁pos hc₁ hμ.le
  exact ⟨lam, hmin, fun i j hc => ordering hν sliceFn_epD.meas hmin hc,
    fun i j hc hj => gap hν sliceFn_epD hμ.le hmin hc hj,
    rank_bound hν sliceFn_epD (by norm_num) epD_ge hμ hc₁pos hc₁ hδ hcgap hmin⟩

/-- The hypotheses of `epD_minimizer` are satisfiable: the discrete law `witness K` has the sphere
moments in every dimension `K ≥ 1`. -/
example (hK : 0 < K) : SphereLike K (witness K) := sphereLike_witness hK
