import SigregDim.Collapse

/-!
# Rank bound for minimizers of the reduced linear objective

If the invariance costs increase by at least `δ` per index and lie above `c₁ > 0`, every global
minimizer has at most `r` active directions with
`r (r - 1) ≤ 4 L μ (∑ₖ cₖ + μ (h 1 - h_lo)) / (c₁ δ K (K+2))`, where `h_lo` is a lower bound of `h`
on `[0, ∞)`.
-/

open MeasureTheory Finset

namespace SigregDim

variable {K : ℕ} {ν : Measure (Fin K → ℝ)}

/-- Distinct naturals: `|T| (|T| - 1) ≤ 2 ∑_{t ∈ T} t`. -/
lemma card_mul_pred_le_two_sum (T : Finset ℕ) : T.card * (T.card - 1) ≤ 2 * ∑ t ∈ T, t := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (hlt x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rcases Nat.eq_zero_or_pos s.card with h | h
    · simp [h]
    · obtain ⟨d, hd⟩ : ∃ d, s.card = d + 1 := ⟨s.card - 1, by omega⟩
      rw [hd] at ih hcard ⊢
      simp only [Nat.add_sub_cancel] at ih ⊢
      nlinarith

/-- The sliced value of the isotropic spectrum `λ = 1` is `h 1`. -/
lemma sliced_one (hν : SphereLike K ν) (h : ℝ → ℝ) : sliced ν h (fun _ => 1) = h 1 := by
  have := hν.prob
  unfold sliced sliceVar
  rw [integral_congr_ae (g := fun _ => h 1) (by
    filter_upwards [hν.sphere] with x hx
    simp [hx])]
  simp

lemma le_sliced_of_lower (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L lo : ℝ} (hh : SliceFn h h' L)
    (hlow : ∀ s, 0 ≤ s → lo ≤ h s) {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    lo ≤ sliced ν h lam := by
  have := hν.prob
  unfold sliced
  calc lo = ∫ _x, lo ∂ν := by simp
    _ ≤ ∫ x, h (sliceVar lam x) ∂ν :=
        integral_mono (integrable_const _) (integrable_h hν hh hlam)
          fun x => hlow _ (sliceVar_nonneg hlam x)

/-- **Trace bound.** At a minimizer, `c₁ ∑ₖ λₖ ≤ ∑ₖ cₖ + μ (h 1 - h_lo)`. -/
lemma trace_bound (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L lo : ℝ} (hh : SliceFn h h' L)
    (hlow : ∀ s, 0 ≤ s → lo ≤ h s) {c : Fin K → ℝ} {c₁ μ : ℝ} (hμ : 0 ≤ μ)
    (hc₁ : ∀ k, c₁ ≤ c k) {lam : Fin K → ℝ} (hmin : IsMinimizer ν h c μ lam) :
    c₁ * ∑ k, lam k ≤ ∑ k, c k + μ * (h 1 - lo) := by
  have h1 := hmin.2 (fun _ => 1) fun _ => zero_le_one
  unfold objective at h1
  rw [sliced_one hν] at h1
  have h2 := le_sliced_of_lower (ν := ν) hν hh hlow hmin.1
  have h3 : c₁ * ∑ k, lam k ≤ ∑ k, c k * lam k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hc₁ k) (hmin.1 k)
  simp only [mul_one] at h1
  nlinarith [mul_le_mul_of_nonneg_left h2 hμ]

/-- **Rank bound.** -/
theorem rank_bound (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L lo : ℝ} (hh : SliceFn h h' L)
    (hL : 0 < L) (hlow : ∀ s, 0 ≤ s → lo ≤ h s) {c : Fin K → ℝ} {c₁ μ δ : ℝ} (hμ : 0 < μ)
    (hc₁pos : 0 < c₁) (hc₁ : ∀ k, c₁ ≤ c k) (hδ : 0 < δ)
    (hcgap : ∀ k l : Fin K, k < l → δ * ((l : ℝ) - (k : ℝ)) ≤ c l - c k)
    {lam : Fin K → ℝ} (hmin : IsMinimizer ν h c μ lam) :
    let r : ℝ := ((univ : Finset (Fin K)).filter fun k => 0 < lam k).card
    r * (r - 1) ≤ 4 * L * μ * (∑ k, c k + μ * (h 1 - lo)) / (c₁ * δ * (K * (K + 2))) := by
  intro r
  set A := (univ : Finset (Fin K)).filter fun k => 0 < lam k with hA
  have hκ : 0 ≤ ∑ k, c k + μ * (h 1 - lo) := by
    have : 0 ≤ ∑ k, c k := Finset.sum_nonneg fun k _ => hc₁pos.le.trans (hc₁ k)
    have : 0 ≤ h 1 - lo := by linarith [hlow 1 zero_le_one]
    positivity
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have : r = 0 := by simp [r, ← hA, hAe]
    rw [this]; simp only [zero_mul]; positivity
  set lmax := A.max' hAne
  have hlmax : lmax ∈ A := A.max'_mem hAne
  have hlmaxpos : 0 < lam lmax := (Finset.mem_filter.1 hlmax).2
  have hK : 0 < K := Fin.pos lmax
  have hKr : (0 : ℝ) < K * (K + 2) := by
    have : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  set g := δ * (K * (K + 2)) / (2 * L * μ) with hg
  have hgpos : 0 < g := by positivity
  -- every active direction carries at least `g` times its index distance to the last one
  have hstep : ∀ k ∈ A, g * ((lmax : ℝ) - (k : ℝ)) ≤ lam k := by
    intro k hk
    have hkle : k ≤ lmax := A.le_max' k hk
    rcases hkle.lt_or_eq with hlt | heq
    · have hcl := hcgap k lmax hlt
      have hdist : (0 : ℝ) < (lmax : ℝ) - k := by
        have : (k : ℕ) < (lmax : ℕ) := hlt
        have : (k : ℝ) < (lmax : ℝ) := by exact_mod_cast this
        linarith
      have hclt : c k < c lmax := by nlinarith
      have hgap := gap hν hh hμ.le hmin hclt hlmaxpos
      rw [le_div_iff₀ hKr] at hgap
      have : δ * ((lmax : ℝ) - k) * (K * (K + 2)) ≤ 2 * L * μ * (lam k - lam lmax) := by
        nlinarith
      rw [hg, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_pos (mul_pos hL hμ) hlmaxpos]
    · subst heq; simp; exact (Finset.mem_filter.1 hk).2.le
  -- sum over the active directions
  have hsumA : g * (r * (r - 1) / 2) ≤ ∑ k ∈ A, lam k := by
    have hnat : A.card * (A.card - 1) ≤ 2 * ∑ k ∈ A, ((lmax : ℕ) - (k : ℕ)) := by
      have hinj : Set.InjOn (fun k : Fin K => (lmax : ℕ) - (k : ℕ)) A := by
        intro a ha b hb hab
        have h1 : (a : ℕ) ≤ lmax := A.le_max' a ha
        have h2 : (b : ℕ) ≤ lmax := A.le_max' b hb
        exact Fin.ext (by simp only at hab; omega)
      have := card_mul_pred_le_two_sum (A.image fun k : Fin K => (lmax : ℕ) - (k : ℕ))
      rwa [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at this
    have hreal : (r : ℝ) * (r - 1) ≤ 2 * ∑ k ∈ A, ((lmax : ℝ) - (k : ℝ)) := by
      have hcast : ∑ k ∈ A, ((lmax : ℝ) - (k : ℝ)) = ((∑ k ∈ A, ((lmax : ℕ) - (k : ℕ)) : ℕ) : ℝ) := by
        push_cast
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Nat.cast_sub (A.le_max' k hk)]
      rw [hcast]
      rcases Nat.eq_zero_or_pos A.card with h0 | hpos
      · simp only [r, ← hA, h0, Nat.cast_zero, zero_mul]; positivity
      · have : ((A.card * (A.card - 1) : ℕ) : ℝ) ≤ ((2 * ∑ k ∈ A, ((lmax : ℕ) - (k : ℕ)) : ℕ) : ℝ) :=
          by exact_mod_cast hnat
        push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hpos.ne')] at this
        simpa [r, ← hA] using this
    calc g * (r * (r - 1) / 2) ≤ g * ∑ k ∈ A, ((lmax : ℝ) - (k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hgpos.le; linarith
      _ = ∑ k ∈ A, g * ((lmax : ℝ) - (k : ℝ)) := Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ A, lam k := Finset.sum_le_sum hstep
  have hsub : ∑ k ∈ A, lam k ≤ ∑ k, lam k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hmin.1 k
  have htr := trace_bound hν hh hlow hμ.le hc₁ hmin
  -- combine: g r(r-1)/2 ≤ ∑ λ ≤ (∑ c + μ κ)/c₁
  have hfin : c₁ * (g * (r * (r - 1) / 2)) ≤ ∑ k, c k + μ * (h 1 - lo) := by
    nlinarith [mul_le_mul_of_nonneg_left (hsumA.trans hsub) hc₁pos.le]
  rw [le_div_iff₀ (by positivity)]
  rw [hg] at hfin
  have e : c₁ * (δ * (K * (K + 2)) / (2 * L * μ) * (r * (r - 1) / 2)) =
      r * (r - 1) * (c₁ * δ * (K * (K + 2))) / (4 * L * μ) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)] at hfin
  linarith

end SigregDim
