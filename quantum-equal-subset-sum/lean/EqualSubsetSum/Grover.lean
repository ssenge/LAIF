import EqualSubsetSum.Prob
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# A uniform number of iterations

With a fraction `φ = sin² θ` of marked items, `j` Grover iterations return a marked item with
probability `sin² ((2 j + 1) θ)`. That formula is a quantum fact and stays a hypothesis, in
`EqualSubsetSum.Model`. The average of the formula over a uniform `j < J` is plain trigonometry:

`(1 / J) ∑_{j < J} sin² ((2 j + 1) θ) = 1 / 2 - sin (4 J θ) / (4 J sin (2 θ))`.

It is at least `1/4` as soon as `J² φ ≥ 1`, for every `φ ∈ (0, 1]`. So the search needs no upper bound
on the marked fraction and no knowledge of it.
-/

open Finset Real

namespace EqualSubsetSum

/-- The probability `sin² ((2 j + 1) θ)` with `sin² θ = φ`. -/
noncomputable def groverProb (φ : ℝ) (j : ℕ) : ℝ := sin ((2 * (j : ℝ) + 1) * arcsin √φ) ^ 2

/-- The telescoping sum of cosines. -/
theorem two_sin_mul_sum_cos (a : ℝ) (J : ℕ) :
    2 * sin a * ∑ j ∈ range J, cos ((2 * (j : ℝ) + 1) * a) = sin (2 * (J : ℝ) * a) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 : 2 * ((J + 1 : ℕ) : ℝ) * a = (2 * (J : ℝ) + 1) * a + a := by push_cast; ring
    have h2 : 2 * (J : ℝ) * a = (2 * (J : ℝ) + 1) * a - a := by ring
    rw [h1, h2, sin_add, sin_sub]
    ring

/-- `sin (2 J a) ≤ J sin a` on `0 < a < π` under the size condition `J sin (a / 2) ≥ 1`. -/
theorem sin_two_mul_le {a : ℝ} {J : ℕ} (ha0 : 0 < a) (haπ : a < π) (hJ : 1 ≤ (J : ℝ) * sin (a / 2)) :
    sin (2 * (J : ℝ) * a) ≤ (J : ℝ) * sin a := by
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hs0 : 0 ≤ sin a := (sin_pos_of_pos_of_lt_pi ha0 haπ).le
  have hθ0 : 0 < a / 2 := by linarith
  have hθ1 : a / 2 < π / 2 := by linarith
  have hsθ : 0 < sin (a / 2) := sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos])
  by_cases hcase : a ≤ 2 * (π / 3)
  · -- `cos (a / 2) ≥ 1/2`, so `sin a ≥ sin (a / 2)`
    have hcos : 1 / 2 ≤ cos (a / 2) := by
      rw [← cos_pi_div_three]
      exact cos_le_cos_of_nonneg_of_le_pi hθ0.le (by linarith [pi_pos]) (by linarith)
    have hdbl : sin a = 2 * sin (a / 2) * cos (a / 2) := by
      rw [← sin_two_mul]
      congr 1
      ring
    have h1 : sin (a / 2) ≤ sin a := by
      rw [hdbl]
      nlinarith
    calc sin (2 * (J : ℝ) * a) ≤ 1 := sin_le_one _
      _ ≤ (J : ℝ) * sin (a / 2) := hJ
      _ ≤ (J : ℝ) * sin a := mul_le_mul_of_nonneg_left h1 hJ0
  · -- near `π`, write `a = π - η`; then `sin (2 J a) = - sin (2 J η)`
    have hcase' : 2 * (π / 3) < a := not_le.mp hcase
    set η := π - a with hη
    have hη0 : 0 < η := by simp only [hη]; linarith
    have hη1 : η ≤ π / 2 := by simp only [hη]; linarith [pi_pos]
    have hsη : sin a = sin η := by
      simp only [hη]
      rw [sin_pi_sub]
    have hexp : sin (2 * (J : ℝ) * a) = - sin (2 * (J : ℝ) * η) := by
      have : 2 * (J : ℝ) * a = (J : ℝ) * (2 * π) - 2 * (J : ℝ) * η := by
        simp only [hη]
        ring
      have h0 : sin ((J : ℝ) * (2 * π)) = 0 := by
        have : (J : ℝ) * (2 * π) = ((2 * J : ℕ) : ℝ) * π := by push_cast; ring
        rw [this, sin_nat_mul_pi]
      rw [this, sin_sub, h0, cos_nat_mul_two_pi]
      ring
    rw [hexp, hsη]
    by_cases hbig : 1 ≤ (J : ℝ) * sin η
    · linarith [neg_one_le_sin (2 * (J : ℝ) * η)]
    · have hsmall : (J : ℝ) * sin η < 1 := not_le.mp hbig
      have hjordan := mul_le_sin hη0.le hη1
      have hpi : 0 < π := pi_pos
      have hJη : 2 * (J : ℝ) * η ≤ π := by
        have h1 : 2 / π * η * J ≤ sin η * J := mul_le_mul_of_nonneg_right hjordan hJ0
        have h2 : 2 / π * ((J : ℝ) * η) ≤ 1 := by nlinarith
        have h3 : (J : ℝ) * η ≤ π / 2 := by
          have h4 : 2 / π * ((J : ℝ) * η) * (π / 2) ≤ 1 * (π / 2) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          have h5 : 2 / π * ((J : ℝ) * η) * (π / 2) = (J : ℝ) * η := by
            field_simp
          linarith
        linarith
      have hnn : 0 ≤ sin (2 * (J : ℝ) * η) :=
        sin_nonneg_of_nonneg_of_le_pi (by positivity) hJη
      have hsη0 : 0 ≤ sin η := by rw [← hsη]; exact hs0
      have : 0 ≤ (J : ℝ) * sin η := by positivity
      linarith

/-- **A uniform number of iterations.** If `0 < φ ≤ 1` and `J² φ ≥ 1`, the average of
`sin² ((2 j + 1) θ)` over `j < J` is at least `1/4`, where `sin² θ = φ`. -/
theorem grover_average {φ : ℝ} {J : ℕ} (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hJ : 1 ≤ (J : ℝ) ^ 2 * φ) :
    (1 : ℝ) / 4 ≤ mean (range J) (groverProb φ) := by
  have hJpos : (0 : ℝ) < J := by
    rcases Nat.eq_zero_or_pos J with rfl | h
    · norm_num at hJ
    · exact_mod_cast h
  have hsq0 : 0 < √φ := sqrt_pos.mpr hφ0
  have hsq1 : √φ ≤ 1 := sqrt_le_one.mpr hφ1
  set θ := arcsin √φ with hθ
  have hsinθ : sin θ = √φ := sin_arcsin (by linarith) hsq1
  have hθ0 : 0 < θ := arcsin_pos.mpr hsq0
  have hθ1 : θ ≤ π / 2 := arcsin_le_pi_div_two _
  have hsum : ∑ j ∈ range J, groverProb φ j
      = (J : ℝ) / 2 - (∑ j ∈ range J, cos ((2 * (j : ℝ) + 1) * (2 * θ))) / 2 := by
    have : ∀ j ∈ range J, groverProb φ j = 1 / 2 - cos ((2 * (j : ℝ) + 1) * (2 * θ)) / 2 := by
      intro j _
      unfold groverProb
      rw [← hθ, sin_sq_eq_half_sub]
      congr 3
      ring
    rw [sum_congr rfl this, sum_sub_distrib, sum_const, sum_div, card_range, nsmul_eq_mul]
    ring
  have hcard : (#(range J) : ℝ) = J := by simp
  unfold mean
  rw [hcard, le_div_iff₀ hJpos, hsum]
  by_cases hend : θ = π / 2
  · -- all marked: every term of the sum of cosines is `-1`
    have hc : ∀ j ∈ range J, cos ((2 * (j : ℝ) + 1) * (2 * θ)) = -1 := by
      intro j _
      rw [hend]
      have : (2 * (j : ℝ) + 1) * (2 * (π / 2)) = (j : ℝ) * (2 * π) + π := by ring
      rw [this, cos_add_pi, cos_nat_mul_two_pi]
    rw [sum_congr rfl hc, sum_const, nsmul_eq_mul, card_range]
    nlinarith
  · have hlt : θ < π / 2 := lt_of_le_of_ne hθ1 hend
    have hsin : 0 < sin (2 * θ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hJs : 1 ≤ (J : ℝ) * sin (2 * θ / 2) := by
      have h1 : 2 * θ / 2 = θ := by ring
      rw [h1, hsinθ]
      have h2 : ((J : ℝ) * √φ) ^ 2 = (J : ℝ) ^ 2 * φ := by
        rw [mul_pow, sq_sqrt hφ0.le]
      have h3 : 0 ≤ (J : ℝ) * √φ := by positivity
      nlinarith
    have hkey := sin_two_mul_le (a := 2 * θ) (J := J) (by linarith) (by linarith) hJs
    have htel := two_sin_mul_sum_cos (2 * θ) J
    set S := ∑ j ∈ range J, cos ((2 * (j : ℝ) + 1) * (2 * θ)) with hS
    have hle : S ≤ (J : ℝ) / 2 := by
      have h1 : 2 * sin (2 * θ) * S ≤ (J : ℝ) * sin (2 * θ) := by rw [htel]; exact hkey
      have h2 : sin (2 * θ) * (2 * S) ≤ sin (2 * θ) * (J : ℝ) := by linarith
      have h3 := le_of_mul_le_mul_left h2 hsin
      linarith
    nlinarith

end EqualSubsetSum
