import Mathlib

/-!
# Exponent of quantum all-pairs shortest paths with small integer weights

At the scale `n^l` the cost exponent is `min (l + w (1 - l)) (5/2 - l/2)`, where `w k` bounds the exponent
`ω(1, k, 1)` of rectangular matrix multiplication, and `τ` is the maximum of this over `l ∈ [0, 1]`.
The function `k ↦ ω(1, k, 1)` is convex, so a convex `w` with the published values at three points is the
hypothesis.

* `le_chord`: a convex function on `[a, b]` with `w a ≤ A` and `w b ≤ B` lies below the chord from `(a, A)` to `(b, B)`.
* `tau_published`: with `w` convex on `[4/5, 1]`, `w (4/5) ≤ 2.220639`, `w (9/10) ≤ 2.293941` and
  `w 1 ≤ 2.371177`, every scale costs at most `2.41346`.
* `tau_nine_fourths`: with `w` convex on `[1/2, 1]`, `w (1/2) ≤ 2` and `w 1 ≤ 9/4`, every scale costs at most `19/8`.
* `tau_ge_seven_thirds`: if `w ≥ 2` then the scale `l = 1/3` costs at least `7/3`.
* `published_hyps_hold`, `published_not_trivial`: an affine `w` satisfies the hypotheses of `tau_published`, and for it
  the scale `l = 173/1000` costs more than `2.41`.
* `nine_fourths_hyps_hold`: an affine `w` satisfies the hypotheses of `tau_nine_fourths`.
* `bounds_can_fail`: for `w = 3` both bounds fail, so they depend on the hypotheses.
-/

namespace ApspExponent

theorem le_chord {w : ℝ → ℝ} {a b A B : ℝ} (hab : a < b) (hw : ConvexOn ℝ (Set.Icc a b) w)
    (hA : w a ≤ A) (hB : w b ≤ B) {k : ℝ} (hk : k ∈ Set.Icc a b) :
    w k ≤ A + (k - a) / (b - a) * (B - A) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set t := (k - a) / (b - a) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hk.1]) hba.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hba]; linarith [hk.2]
  have hkey : (1 - t) * a + t * b = k := by
    rw [ht]; field_simp; ring
  have h := hw.2 (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at h
  rw [hkey] at h
  have h1 : (1 - t) * w a ≤ (1 - t) * A := mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : t * w b ≤ t * B := mul_le_mul_of_nonneg_left hB ht0
  nlinarith

theorem tau_published (w : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc (4 / 5) 1) w)
    (h8 : w (4 / 5) ≤ 2.220639) (h9 : w (9 / 10) ≤ 2.293941) (h1 : w 1 ≤ 2.371177) :
    ∀ l ∈ Set.Icc (0 : ℝ) 1, min (l + w (1 - l)) (5 / 2 - l / 2) ≤ 2.41346 := by
  intro l hl
  by_cases hbig : (0.17308 : ℝ) ≤ l
  · exact (min_le_right _ _).trans (by linarith)
  rw [not_le] at hbig
  apply (min_le_left _ _).trans
  by_cases hlow : l ≤ 1 / 10
  · have hc := le_chord (by norm_num : (9 / 10 : ℝ) < 1)
      (hconv.subset (Set.Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc _ _)) h9 h1
      (k := 1 - l) ⟨by linarith, by linarith [hl.1]⟩
    have ht : (1 - l - 9 / 10) / (1 - 9 / 10) = 1 - 10 * l := by ring
    rw [ht] at hc
    nlinarith [hl.1]
  · rw [not_le] at hlow
    have hc := le_chord (by norm_num : (4 / 5 : ℝ) < 9 / 10)
      (hconv.subset (Set.Icc_subset_Icc le_rfl (by norm_num)) (convex_Icc _ _)) h8 h9
      (k := 1 - l) ⟨by linarith, by linarith⟩
    have ht : (1 - l - 4 / 5) / (9 / 10 - 4 / 5) = 2 - 10 * l := by ring
    rw [ht] at hc
    nlinarith

theorem tau_nine_fourths (w : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc (1 / 2) 1) w)
    (h5 : w (1 / 2) ≤ 2) (h1 : w 1 ≤ 9 / 4) :
    ∀ l ∈ Set.Icc (0 : ℝ) 1, min (l + w (1 - l)) (5 / 2 - l / 2) ≤ 19 / 8 := by
  intro l hl
  by_cases hbig : (1 / 4 : ℝ) ≤ l
  · exact (min_le_right _ _).trans (by linarith)
  rw [not_le] at hbig
  apply (min_le_left _ _).trans
  have hc := le_chord (by norm_num : (1 / 2 : ℝ) < 1) hconv h5 h1 (k := 1 - l)
    ⟨by linarith, by linarith [hl.1]⟩
  have ht : (1 - l - 1 / 2) / (1 - 1 / 2) = 1 - 2 * l := by ring
  rw [ht] at hc
  nlinarith

theorem tau_ge_seven_thirds (w : ℝ → ℝ) (hw : ∀ k, 2 ≤ w k) :
    (1 / 3 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ 7 / 3 ≤ min (1 / 3 + w (1 - 1 / 3)) (5 / 2 - (1 / 3) / 2) := by
  refine ⟨⟨by norm_num, by norm_num⟩, le_min ?_ ?_⟩
  · linarith [hw (1 - 1 / 3)]
  · norm_num

/-- The affine function through `(9/10, 2.293941)` and `(1, 2.371177)`. -/
def wAff (k : ℝ) : ℝ := 2.371177 + (k - 1) * 0.77236

theorem convexOn_affine (s : Set ℝ) (hs : Convex ℝ s) (c d : ℝ) :
    ConvexOn ℝ s (fun k => c + (k - 1) * d) := by
  refine ⟨hs, fun x _ y _ a b _ _ hab => ?_⟩
  simp only [smul_eq_mul]
  have hb : b = 1 - a := by linarith
  subst hb
  nlinarith

theorem published_hyps_hold :
    ConvexOn ℝ (Set.Icc (4 / 5) 1) wAff ∧ wAff (4 / 5) ≤ 2.220639 ∧ wAff (9 / 10) ≤ 2.293941 ∧
      wAff 1 ≤ 2.371177 := by
  refine ⟨convexOn_affine _ (convex_Icc _ _) _ _, ?_, ?_, ?_⟩ <;> norm_num [wAff]

theorem published_not_trivial :
    2.41 < min ((173 / 1000 : ℝ) + wAff (1 - 173 / 1000)) (5 / 2 - (173 / 1000) / 2) := by
  norm_num [wAff]

theorem nine_fourths_hyps_hold :
    ConvexOn ℝ (Set.Icc (1 / 2) 1) (fun k : ℝ => 9 / 4 + (k - 1) * (1 / 2)) ∧
      (fun k : ℝ => 9 / 4 + (k - 1) * (1 / 2)) (1 / 2) ≤ 2 ∧
      (fun k : ℝ => 9 / 4 + (k - 1) * (1 / 2)) 1 ≤ 9 / 4 := by
  refine ⟨convexOn_affine _ (convex_Icc _ _) _ _, ?_, ?_⟩ <;> norm_num

/-- Without the bounds on `w`, both conclusions fail: for `w = 3` the scale `l = 1/10` costs more than `2.41346`
and the scale `l = 0` costs more than `19/8`. -/
theorem bounds_can_fail :
    (2.41346 : ℝ) < min ((1 / 10 : ℝ) + (fun _ : ℝ => (3 : ℝ)) (1 - 1 / 10)) (5 / 2 - (1 / 10) / 2) ∧
      (19 / 8 : ℝ) < min ((0 : ℝ) + (fun _ : ℝ => (3 : ℝ)) (1 - 0)) (5 / 2 - 0 / 2) := by
  constructor <;> norm_num

end ApspExponent
