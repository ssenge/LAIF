import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Elementary steps of the noise-model test

Scalar and inner-product facts used in the test that decides between dephasing in an unknown
basis and its depolarizing model with `O(d/p)` calls, and in the lower bound for parallel
strategies.
-/

open Real

namespace NoiseTest

/-- `E X² ≤ 2 (E X)²` for the moments of `X = Σ w_k² - 1/d`, for every `d ≥ 2`. -/
theorem second_moment_le (d : ℝ) (hd : 2 ≤ d) :
    (d - 1) * (d ^ 2 + 7 * d - 6) / (d ^ 2 * (d + 1) * (d + 2) * (d + 3)) ≤
      2 * ((d - 1) / (d * (d + 1))) ^ 2 := by
  have h0 : 0 < d := by linarith
  have key : 2 * ((d - 1) / (d * (d + 1))) ^ 2 -
      (d - 1) * (d ^ 2 + 7 * d - 6) / (d ^ 2 * (d + 1) * (d + 2) * (d + 3)) =
      (d - 1) * (d ^ 3 + d - 6) / (d ^ 2 * (d + 1) ^ 2 * (d + 2) * (d + 3)) := by
    field_simp
    ring
  have hnum : 0 ≤ (d - 1) * (d ^ 3 + d - 6) := by
    apply mul_nonneg <;> nlinarith
  have : 0 ≤ (d - 1) * (d ^ 3 + d - 6) / (d ^ 2 * (d + 1) ^ 2 * (d + 2) * (d + 3)) :=
    div_nonneg hnum (by positivity)
  linarith

/-- `E X / 2 ≥ 1/(6d)` for `d ≥ 2`. -/
theorem half_mean_ge (d : ℝ) (hd : 2 ≤ d) : 1 / (6 * d) ≤ (d - 1) / (d * (d + 1)) / 2 := by
  have h0 : 0 < d := by linarith
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The second-moment constant: if `0 < m` and `s ≤ 2 m²` then `m² / (4 s) ≥ 1/8`. -/
theorem second_moment_constant (m s : ℝ) (hm : 0 < m) (hs : s ≤ 2 * m ^ 2) (hs0 : 0 < s) :
    1 / 8 ≤ m ^ 2 / (4 * s) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- The distance identity: if `⟪A, B⟫ = ‖A‖²`, then
`‖(1 - q) A + (q - q') B‖² = (1 - q')² ‖A‖² + (q - q')² (‖B‖² - ‖A‖²)`. -/
theorem dist_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : E)
    (q q' : ℝ) (hAB : inner ℝ A B = ‖A‖ ^ 2) :
    ‖(1 - q) • A + (q - q') • B‖ ^ 2 =
      (1 - q') ^ 2 * ‖A‖ ^ 2 + (q - q') ^ 2 * (‖B‖ ^ 2 - ‖A‖ ^ 2) := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hAB]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, starRingEnd_apply, star_trivial]
  ring

/-- The gap: with `q' ≤ 1/2` and `‖A‖² ≤ ‖B‖²`, the squared distance is at least `‖A‖²/4`. -/
theorem dist_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : E)
    (q q' : ℝ) (hAB : inner ℝ A B = ‖A‖ ^ 2) (hq' : 0 ≤ q') (hq'2 : q' ≤ 1 / 2)
    (hX : ‖A‖ ^ 2 ≤ ‖B‖ ^ 2) :
    ‖A‖ ^ 2 / 4 ≤ ‖(1 - q) • A + (q - q') • B‖ ^ 2 := by
  rw [dist_identity A B q q' hAB]
  have h1 : 1 / 4 ≤ (1 - q') ^ 2 := by nlinarith
  have h2 : 0 ≤ (q - q') ^ 2 * (‖B‖ ^ 2 - ‖A‖ ^ 2) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [sq_nonneg ‖A‖]

/-- The block length: `a = 1 - p d/(d+1)` satisfies `a^m ≤ 1/2` once `m ≥ 3 ln 2/(2p)`. -/
theorem block_pow_le (d p : ℝ) (m : ℕ) (hd : 2 ≤ d) (hp : 0 < p) (hp1 : p ≤ 1)
    (hm : 3 * Real.log 2 / (2 * p) ≤ m) :
    (1 - p * d / (d + 1)) ^ m ≤ 1 / 2 := by
  have hd0 : 0 < d + 1 := by linarith
  have ha0 : 0 ≤ 1 - p * d / (d + 1) := by
    rw [sub_nonneg, div_le_one hd0]; nlinarith
  have ha : 1 - p * d / (d + 1) ≤ Real.exp (-(2 * p / 3)) := by
    have : 2 * p / 3 ≤ p * d / (d + 1) := by
      rw [div_le_div_iff₀ (by norm_num) hd0]; nlinarith
    linarith [Real.add_one_le_exp (-(2 * p / 3))]
  calc (1 - p * d / (d + 1)) ^ m ≤ Real.exp (-(2 * p / 3)) ^ m := pow_le_pow_left₀ ha0 ha m
    _ = Real.exp (-(2 * p / 3) * m) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have : 3 * Real.log 2 ≤ 2 * p * m := by
          rw [div_le_iff₀ (by positivity)] at hm; linarith
        nlinarith
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- Nine rounds: the error under the model is at most `9/27`, and under dephasing at most
`(1 - 26/216)^9 < 1/3`. -/
theorem rounds : (9 : ℝ) * (1 / 27) ≤ 1 / 3 ∧ (1 - (26 : ℝ) / 216) ^ 9 < 1 / 3 := by
  constructor <;> norm_num

/-- Products: `∏_{i<s} (1 - i/d) ≥ 1 - s(s-1)/(2d)` when `s ≤ d`. -/
theorem prod_ge (d : ℝ) (s : ℕ) (hd : 0 < d) (hs : (s : ℝ) ≤ d) :
    1 - (s : ℝ) * (s - 1) / (2 * d) ≤ ∏ i ∈ Finset.range s, (1 - (i : ℝ) / d) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hs' : (s : ℝ) ≤ d := by push_cast at hs; linarith
    rw [Finset.prod_range_succ]
    have ih' := ih hs'
    have hf : 0 ≤ 1 - (s : ℝ) / d := by rw [sub_nonneg, div_le_one hd]; exact hs'
    have hP : 0 ≤ ∏ i ∈ Finset.range s, (1 - (i : ℝ) / d) :=
      Finset.prod_nonneg fun i hi => by
        rw [sub_nonneg, div_le_one hd]
        have := Finset.mem_range.mp hi
        have : (i : ℝ) ≤ s := by exact_mod_cast this.le
        linarith
    have hsd : (s : ℝ) / d ≥ 0 := div_nonneg (Nat.cast_nonneg s) hd.le
    have : (1 - (s : ℝ) * (s - 1) / (2 * d)) * (1 - (s : ℝ) / d) ≥
        1 - ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) - 1) / (2 * d) := by
      push_cast
      have e : (1 - (s : ℝ) * (s - 1) / (2 * d)) * (1 - (s : ℝ) / d) =
          1 - (s + 1) * s / (2 * d) + (s : ℝ) * (s - 1) / (2 * d) * (s / d) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ (s : ℝ) * (s - 1) / (2 * d) * (s / d) := by
        rcases Nat.eq_zero_or_pos s with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ s := by exact_mod_cast h
          apply mul_nonneg _ hsd
          apply div_nonneg _ (by positivity)
          nlinarith
      have e2 : (s : ℝ) + 1 - 1 = s := by ring
      rw [e2]; linarith
    calc 1 - ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) - 1) / (2 * d)
        ≤ (1 - (s : ℝ) * (s - 1) / (2 * d)) * (1 - (s : ℝ) / d) := this
      _ ≤ (∏ i ∈ Finset.range s, (1 - (i : ℝ) / d)) * (1 - (s : ℝ) / d) :=
          mul_le_mul_of_nonneg_right ih' hf

/-- If `x ≥ 1 - t` with `0 ≤ t ≤ 1/2`, then `γ = 1/x` satisfies `γ ≤ 2` and `γ - 1 ≤ 2t`. -/
theorem gamma_bounds (x t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) (hx : 1 - t ≤ x) :
    1 / x ≤ 2 ∧ 1 / x - 1 ≤ 2 * t := by
  have hx0 : 0 < x := by linarith
  constructor
  · rw [div_le_iff₀ hx0]; linarith
  · have : 1 / x - 1 = (1 - x) / x := by field_simp
    rw [this, div_le_iff₀ hx0]; nlinarith

/-- The constants of the parallel bound: with `1 ≤ γ ≤ 2`, `γ - 1 ≤ s²/d` and `0 ≤ s`, the two
eigenvalue bounds are at most `4s²/d` and `2s²/d`. -/
theorem parallel_constants (s d γ : ℝ) (hs : 0 ≤ s) (hd : 0 < d) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 2)
    (hγ : γ - 1 ≤ s ^ 2 / d) :
    2 * s * (s - 1) / (d + 1) + γ * s * (s - 1) / d ≤ 4 * s ^ 2 / d ∧
      (γ - 1) + (2 - γ) * s * (s - 1) / (d + 1) ≤ 2 * s ^ 2 / d := by
  have h1 : s * (s - 1) ≤ s ^ 2 := by nlinarith
  have h2 : s * (s - 1) / (d + 1) ≤ s ^ 2 / d := by
    rcases le_or_gt (s * (s - 1)) 0 with h | h
    · exact (div_nonpos_of_nonpos_of_nonneg h (by linarith)).trans (by positivity)
    · calc s * (s - 1) / (d + 1) ≤ s * (s - 1) / d :=
            div_le_div_of_nonneg_left h.le hd (by linarith)
        _ ≤ s ^ 2 / d := div_le_div_of_nonneg_right h1 hd.le
  have h3 : γ * s * (s - 1) / d ≤ 2 * s ^ 2 / d := by
    apply div_le_div_of_nonneg_right _ hd.le
    rcases le_or_gt (s * (s - 1)) 0 with h | h
    · nlinarith
    · nlinarith
  constructor
  · have e1 : 2 * s * (s - 1) / (d + 1) = 2 * (s * (s - 1) / (d + 1)) := by ring
    have e2 : 4 * s ^ 2 / d = 2 * (s ^ 2 / d) + 2 * s ^ 2 / d := by ring
    rw [e1, e2]
    exact add_le_add (by linarith) h3
  · have : (2 - γ) * s * (s - 1) / (d + 1) ≤ s ^ 2 / d := by
      rcases le_or_gt (s * (s - 1)) 0 with h | h
      · have : (2 - γ) * s * (s - 1) / (d + 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
        exact this.trans (by positivity)
      · have e : (2 - γ) * s * (s - 1) / (d + 1) = (2 - γ) * (s * (s - 1) / (d + 1)) := by ring
        rw [e]
        calc (2 - γ) * (s * (s - 1) / (d + 1)) ≤ 1 * (s * (s - 1) / (d + 1)) :=
              mul_le_mul_of_nonneg_right (by linarith) (div_nonneg h.le (by linarith))
          _ ≤ s ^ 2 / d := by rw [one_mul]; exact h2
    have : s ^ 2 / d + s ^ 2 / d = 2 * s ^ 2 / d := by ring
    linarith

/-- `2 + √2 ≤ 3.42` and `3 · 3.42 ≤ 11`. -/
theorem final_constant : 2 + Real.sqrt 2 ≤ 3.42 ∧ (3 : ℝ) * 3.42 ≤ 11 := by
  refine ⟨?_, by norm_num⟩
  have : Real.sqrt 2 ≤ 1.42 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

end NoiseTest
