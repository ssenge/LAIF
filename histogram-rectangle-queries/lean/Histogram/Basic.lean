import Mathlib

/-!
# Records and windows for the largest rectangle in a histogram

The heights are `h : ℤ → ℝ`. The rectangle on the interval `[l, r]` has the height of its lowest bar.

* `cover`: an interval of length in `[w, 2w)` contains a multiple `p` of `w`, and lies in
  `[p - 2w + 1, p + 2w - 1]`.
* `min_is_record`: the lowest bar of an interval through `p` can be taken to be a left record or a right record of
  `p`. A left record is a position `j ≤ p` whose height is below every height in `(j, p]`.
* `first_below_isRecL`: the first position left of `p` with height below `v ≤ h p` is a left record, so the runs of
  heights at least `v` through `p` end at records.
* `card_recL_le`: in every finite set of positions, the left records number at most the distinct heights.
* `sum_sqrt_le`: gaps `g_i ≥ 0` with sum `S` satisfy `∑ √g_i ≤ √(R S)` for `R` gaps.
-/

namespace Histogram

open Finset

/-- `j` is a left record of `p`: it lies at or left of `p`, and its height is below all heights in `(j, p]`. -/
def IsRecL (h : ℤ → ℝ) (p j : ℤ) : Prop := j ≤ p ∧ ∀ i, j < i → i ≤ p → h j < h i

/-- `j` is a right record of `p`. -/
def IsRecR (h : ℤ → ℝ) (p j : ℤ) : Prop := p ≤ j ∧ ∀ i, p ≤ i → i < j → h j < h i

/-- An interval of length in `[w, 2w)` contains a multiple of `w` and lies in its window. -/
theorem cover {w l r : ℤ} (hw : 0 < w) (h1 : w ≤ r - l + 1) (h2 : r - l + 1 < 2 * w) :
    ∃ p, w ∣ p ∧ l ≤ p ∧ p ≤ r ∧ p - 2 * w + 1 ≤ l ∧ r ≤ p + 2 * w - 1 := by
  have e1 := Int.emod_add_mul_ediv (-l) w
  have e2 := Int.emod_nonneg (-l) hw.ne'
  have e3 := Int.emod_lt_of_pos (-l) hw
  refine ⟨l + (-l) % w, ⟨-((-l) / w), by linarith⟩, by linarith, by linarith, by linarith, by linarith⟩

/-- On `[l, p]` some lowest position is a left record. -/
theorem exists_recL (h : ℤ → ℝ) {l p : ℤ} (hlp : l ≤ p) :
    ∃ j, l ≤ j ∧ IsRecL h p j ∧ ∀ i, l ≤ i → i ≤ p → h j ≤ h i := by
  set S := Icc l p
  have hS : S.Nonempty := ⟨p, by simp [S, hlp]⟩
  set m := S.inf' hS h
  set T := S.filter (fun i => h i = m)
  have hT : T.Nonempty := by
    obtain ⟨j, hj, e⟩ := S.exists_mem_eq_inf' hS h
    exact ⟨j, by simp [T, hj, e.symm, m]⟩
  set j := T.max' hT
  have hj : j ∈ T := T.max'_mem hT
  simp only [T, mem_filter, S, mem_Icc] at hj
  have hmin : ∀ i, l ≤ i → i ≤ p → h j ≤ h i := fun i h1 h2 => by
    rw [hj.2]; exact S.inf'_le h (by simp [S, h1, h2])
  refine ⟨j, hj.1.1, ⟨hj.1.2, fun i hi hip => ?_⟩, hmin⟩
  rcases (hmin i (by linarith [hj.1.1]) hip).lt_or_eq with e | e
  · exact e
  · have : i ∈ T := by simp [T, S, hip, e.symm, hj.2]; linarith [hj.1.1]
    have := T.le_max' i this
    linarith

/-- On `[p, r]` some lowest position is a right record. -/
theorem exists_recR (h : ℤ → ℝ) {p r : ℤ} (hpr : p ≤ r) :
    ∃ j, j ≤ r ∧ IsRecR h p j ∧ ∀ i, p ≤ i → i ≤ r → h j ≤ h i := by
  obtain ⟨j, h1, ⟨h2, h3⟩, h4⟩ := exists_recL (fun i => h (-i)) (l := -r) (p := -p) (by linarith)
  refine ⟨-j, by linarith, ⟨by linarith, fun i hi hij => ?_⟩, fun i hi hir => ?_⟩
  · have := h3 (-i) (by linarith) (by linarith)
    simpa using this
  · have := h4 (-i) (by linarith) (by linarith)
    simpa using this

/-- **The lowest bar is a record.** Every interval `[l, r]` through `p` has a lowest position in it that is a left
or a right record of `p`. -/
theorem min_is_record (h : ℤ → ℝ) {l p r : ℤ} (hlp : l ≤ p) (hpr : p ≤ r) :
    ∃ j, l ≤ j ∧ j ≤ r ∧ (IsRecL h p j ∨ IsRecR h p j) ∧ ∀ i, l ≤ i → i ≤ r → h j ≤ h i := by
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_recL h hlp
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_recR h hpr
  rcases le_total (h a) (h b) with e | e
  · refine ⟨a, ha1, by linarith [ha2.1], Or.inl ha2, fun i h1 h2 => ?_⟩
    rcases le_total i p with hi | hi
    · exact ha3 i h1 hi
    · exact e.trans (hb3 i hi h2)
  · refine ⟨b, by linarith [hb2.1], hb1, Or.inr hb2, fun i h1 h2 => ?_⟩
    rcases le_total i p with hi | hi
    · exact e.trans (ha3 i h1 hi)
    · exact hb3 i hi h2

/-- The first position left of `p` with height below `v ≤ h p` is a left record. -/
theorem first_below_isRecL (h : ℤ → ℝ) {p q : ℤ} {v : ℝ} (hqp : q < p) (hq : h q < v)
    (hrun : ∀ i, q < i → i ≤ p → v ≤ h i) : IsRecL h p q :=
  ⟨hqp.le, fun i h1 h2 => lt_of_lt_of_le hq (hrun i h1 h2)⟩

/-- The heights of left records strictly increase towards `p`. -/
theorem recL_strict (h : ℤ → ℝ) {p j j' : ℤ} (hj : IsRecL h p j) (hj' : IsRecL h p j') (e : j < j') :
    h j < h j' :=
  hj.2 j' e hj'.1

/-- **Few records.** In a finite set of positions, the left records of `p` number at most the distinct heights. -/
theorem card_recL_le (h : ℤ → ℝ) (p : ℤ) (W : Finset ℤ) [DecidablePred (IsRecL h p)] :
    (W.filter (IsRecL h p)).card ≤ (W.image h).card := by
  have inj : Set.InjOn h ↑(W.filter (IsRecL h p)) := by
    intro j hj j' hj' e
    simp only [coe_filter, Set.mem_ofPred_eq] at hj hj'
    rcases lt_trichotomy j j' with c | c | c
    · exact absurd e (recL_strict h hj.2 hj'.2 c).ne
    · exact c
    · exact absurd e (recL_strict h hj'.2 hj.2 c).ne'
  calc (W.filter (IsRecL h p)).card = ((W.filter (IsRecL h p)).image h).card := (card_image_of_injOn inj).symm
    _ ≤ (W.image h).card := card_le_card (image_subset_image (filter_subset _ _))

/-- **Cauchy-Schwarz for the searches.** `R` searches with gaps of sum `S` cost `∑ √g_i ≤ √(R S)`. -/
theorem sum_sqrt_le {R : ℕ} (g : Fin R → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, Real.sqrt (g i) ≤ Real.sqrt (R * ∑ i, g i) := by
  apply Real.le_sqrt_of_sq_le
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin R)) (fun _ => (1 : ℝ))
    (fun i => Real.sqrt (g i))
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Real.sq_sqrt (hg _)] at cs
  exact cs

end Histogram
