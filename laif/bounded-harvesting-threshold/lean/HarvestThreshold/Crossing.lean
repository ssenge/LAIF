import Mathlib

/-!
# Unique critical point from strict down-crossings

Abstract core of the uniqueness proof for the optimal harvesting threshold.

* `zero_unique_of_deriv_neg`: a function on `(0, ∞)` whose derivative is negative at each of its
  zeros has at most one zero.
* `critical_point_unique`: let `A, B, P, Q, λ` be positive differentiable functions on `(0, ∞)` with
  `A' = m`, `B' = -m₀`, `P' = f m`, `Q' = -f m₀`, `λ' > 0` and `m = λ m₀`. If at every point the mean
  `P / A` or the mean `Q / B` is below `f`, then `H = (P + λ Q) / (A + λ B)` has at most one critical
  point in `(0, ∞)`.
-/

open Set Filter Topology

namespace HarvestThreshold

/-- A function differentiable on `(0, ∞)` whose derivative is negative at every zero has at most
one zero there. -/
theorem zero_unique_of_deriv_neg {D D' : ℝ → ℝ}
    (hD : ∀ x, 0 < x → HasDerivAt D (D' x) x)
    (hneg : ∀ x, 0 < x → D x = 0 → D' x < 0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hDx : D x = 0) (hDy : D y = 0) : x = y := by
  by_contra hne
  -- without loss of generality x < y
  have key : ∀ a b : ℝ, 0 < a → a < b → D a = 0 → D b = 0 → False := by
    intro a b ha hab hDa hDb
    have hb : 0 < b := ha.trans hab
    -- D is negative just right of a
    have hslope : Tendsto (slope D a) (𝓝[>] a) (𝓝 (D' a)) :=
      (hasDerivAt_iff_tendsto_slope.mp (hD a ha)).mono_left
        (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
    obtain ⟨a₁, hneg₁, ha₁⟩ :=
      ((hslope.eventually (gt_mem_nhds (hneg a ha hDa))).and
        (Ioo_mem_nhdsGT hab)).exists
    have hDa₁ : D a₁ < 0 := by
      rw [slope_def_field, hDa, sub_zero] at hneg₁
      by_contra h
      push Not at h
      have := div_nonneg h (sub_pos.mpr ha₁.1).le
      linarith
    -- continuity on [a₁, b]
    have hcont : ContinuousOn D (Icc a₁ b) := fun t ht =>
      (hD t (ha.trans (ha₁.1.trans_le ht.1))).continuousAt.continuousWithinAt
    -- first zero after a₁
    set S := Icc a₁ b ∩ D ⁻¹' {0} with hS
    have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hSne : S.Nonempty := ⟨b, ⟨ha₁.2.le, le_rfl⟩, hDb⟩
    have hSbdd : BddBelow S := ⟨a₁, fun t ht => ht.1.1⟩
    set z := sInf S with hz
    have hzS : z ∈ S := hSc.csInf_mem hSne hSbdd
    have hz0 : D z = 0 := hzS.2
    have ha₁z : a₁ < z := by
      rcases hzS.1.1.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hz0) hDa₁.ne
    have hzpos : 0 < z := ha.trans (ha₁.1.trans ha₁z)
    -- D < 0 on [a₁, z)
    have hbelow : ∀ t ∈ Ico a₁ z, D t < 0 := by
      intro t ht
      by_contra hge
      push Not at hge
      have hsub : Icc a₁ t ⊆ Icc a₁ b := Icc_subset_Icc le_rfl (ht.2.le.trans hzS.1.2)
      obtain ⟨c, hc, hDc⟩ := intermediate_value_Icc ht.1 (hcont.mono hsub) ⟨hDa₁.le, hge⟩
      have : z ≤ c := csInf_le hSbdd ⟨hsub hc, hDc⟩
      exact absurd (this.trans hc.2) (not_le.mpr ht.2)
    -- then D' z ≥ 0 from the left slopes
    have hslopeL : Tendsto (slope D z) (𝓝[<] z) (𝓝 (D' z)) :=
      (hasDerivAt_iff_tendsto_slope.mp (hD z hzpos)).mono_left
        (nhdsWithin_mono _ fun t ht => ne_of_lt ht)
    have hev : ∀ᶠ t in 𝓝[<] z, 0 ≤ slope D z t := by
      filter_upwards [Ioo_mem_nhdsLT ha₁z] with t ht
      rw [slope_def_field, hz0, sub_zero]
      exact div_nonneg_of_nonpos (hbelow t ⟨ht.1.le, ht.2⟩).le (sub_nonpos.mpr ht.2.le)
    have : 0 ≤ D' z := ge_of_tendsto hslopeL hev
    exact absurd (hneg z hzpos hz0) (not_lt.mpr this)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y hx h hDx hDy
  · exact key y x hy h hDy hDx

/-- Derivative of `H = (P + λ Q) / (A + λ B)` when `m = λ m₀`: the terms from the moving endpoint
cancel, and `H' = λ' A B (Q / B - P / A) / (A + λ B)²`. -/
theorem ratio_hasDerivAt {A B P Q lam : ℝ → ℝ} {a b p q l l' mt mt₀ ft t : ℝ}
    (hA : HasDerivAt A mt t) (hB : HasDerivAt B (-mt₀) t)
    (hP : HasDerivAt P (ft * mt) t) (hQ : HasDerivAt Q (-(ft * mt₀)) t)
    (hlam : HasDerivAt lam l' t)
    (ha : A t = a) (hb : B t = b) (hp : P t = p) (hq : Q t = q) (hl : lam t = l)
    (ha0 : 0 < a) (hb0 : 0 < b) (hl0 : 0 < l) (hm : mt = l * mt₀) :
    HasDerivAt (fun t => (P t + lam t * Q t) / (A t + lam t * B t))
      (l' * (a * b * (q / b - p / a)) / (a + l * b) ^ 2) t := by
  have hden : A t + lam t * B t ≠ 0 := by
    rw [ha, hb, hl]; exact (add_pos ha0 (mul_pos hl0 hb0)).ne'
  have hN := hP.add (hlam.mul hQ)
  have hDn := hA.add (hlam.mul hB)
  convert hN.div hDn hden using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [ha, hb, hp, hq, hl, hm]
  field_simp
  ring

/-- Uniqueness of the critical point of `H = (P + λ Q) / (A + λ B)`. -/
theorem critical_point_unique {A B P Q lam lam' m m₀ f : ℝ → ℝ}
    (hA : ∀ x, 0 < x → HasDerivAt A (m x) x)
    (hB : ∀ x, 0 < x → HasDerivAt B (-m₀ x) x)
    (hP : ∀ x, 0 < x → HasDerivAt P (f x * m x) x)
    (hQ : ∀ x, 0 < x → HasDerivAt Q (-(f x * m₀ x)) x)
    (hlam : ∀ x, 0 < x → HasDerivAt lam (lam' x) x)
    (hApos : ∀ x, 0 < x → 0 < A x) (hBpos : ∀ x, 0 < x → 0 < B x)
    (hlampos : ∀ x, 0 < x → 0 < lam x) (hlam'pos : ∀ x, 0 < x → 0 < lam' x)
    (hmpos : ∀ x, 0 < x → 0 < m x) (hm₀pos : ∀ x, 0 < x → 0 < m₀ x)
    (hm : ∀ x, 0 < x → m x = lam x * m₀ x)
    (hmean : ∀ x, 0 < x → P x / A x < f x ∨ Q x / B x < f x)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hHx : HasDerivAt (fun t => (P t + lam t * Q t) / (A t + lam t * B t)) 0 x)
    (hHy : HasDerivAt (fun t => (P t + lam t * Q t) / (A t + lam t * B t)) 0 y) : x = y := by
  set D : ℝ → ℝ := fun t => Q t / B t - P t / A t with hDdef
  set D' : ℝ → ℝ := fun t => m₀ t / B t * (Q t / B t - f t) - m t / A t * (f t - P t / A t)
    with hD'def
  have hDder : ∀ t, 0 < t → HasDerivAt D (D' t) t := by
    intro t ht
    have h1 := (hQ t ht).div (hB t ht) (hBpos t ht).ne'
    have h2 := (hP t ht).div (hA t ht) (hApos t ht).ne'
    convert h1.sub h2 using 1
    simp only [hD'def]
    have hb := (hBpos t ht).ne'
    have ha := (hApos t ht).ne'
    field_simp
    ring
  -- derivative of H in closed form
  have hHder : ∀ t, 0 < t → HasDerivAt (fun t => (P t + lam t * Q t) / (A t + lam t * B t))
      (lam' t * (A t * B t * D t) / (A t + lam t * B t) ^ 2) t := fun t ht =>
    ratio_hasDerivAt (hA t ht) (hB t ht) (hP t ht) (hQ t ht) (hlam t ht) rfl rfl rfl rfl rfl
      (hApos t ht) (hBpos t ht) (hlampos t ht) (hm t ht)
  have hzero : ∀ t, 0 < t → HasDerivAt (fun t => (P t + lam t * Q t) / (A t + lam t * B t)) 0 t →
      D t = 0 := by
    intro t ht h
    have := (hHder t ht).unique h
    have hden : 0 < (A t + lam t * B t) ^ 2 :=
      pow_pos (add_pos (hApos t ht) (mul_pos (hlampos t ht) (hBpos t ht))) 2
    have hc : 0 < lam' t * (A t * B t) :=
      mul_pos (hlam'pos t ht) (mul_pos (hApos t ht) (hBpos t ht))
    rw [div_eq_zero_iff] at this
    rcases this with h0 | h0
    · rw [← mul_assoc] at h0
      exact (mul_eq_zero.mp h0).resolve_left hc.ne'
    · exact absurd h0 hden.ne'
  have hneg : ∀ t, 0 < t → D t = 0 → D' t < 0 := by
    intro t ht hDt
    have hv : Q t / B t = P t / A t := sub_eq_zero.mp hDt
    have hsum : 0 < m₀ t / B t + m t / A t :=
      add_pos (div_pos (hm₀pos t ht) (hBpos t ht)) (div_pos (hmpos t ht) (hApos t ht))
    have hlt : P t / A t < f t := by
      rcases hmean t ht with h | h
      · exact h
      · rwa [hv] at h
    have : D' t = (P t / A t - f t) * (m₀ t / B t + m t / A t) := by
      simp only [hD'def]; rw [hv]; ring
    rw [this]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hsum
  exact zero_unique_of_deriv_neg hDder hneg hx hy (hzero x hx hHx) (hzero y hy hHy)

end HarvestThreshold
