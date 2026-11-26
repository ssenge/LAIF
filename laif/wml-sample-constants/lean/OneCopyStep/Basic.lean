import Mathlib

/-!
# Scalar steps of the one-copy step with leading constant (d+1)/4 + 1/d, and (d−1)/4 for rank one

The step Λ_Δ(ρ ⊗ π_L) = ρ + Δℒ(ρ) + Δ² E_L(ρ) with E_L(ρ) = ¼ Tr(ρK) I − (d/4) LρL† has per-step leading error
e_L = ½‖E_L − ℒ²/2‖⋄. This file proves the scalar steps of the bounds on e_L and of the copy counts.

* `form_nonneg`: for d ≥ 3 and 0 ≤ m ≤ 1, the quadratic form of the coefficient matrix
  [[(d−1)/4 + (m² − 1)/2, −m/4, 0], [−m/4, 1/2, 1/8], [0, 1/8, (d−1)/4]] is nonnegative; with m = |⟨b|a⟩| this is
  the matrix of the rank-one certificate (a Hermitian form with off-diagonal entries of these moduli is bounded below
  by this form at the moduli of its arguments). `form_fails_d2` shows that d ≥ 3 is needed.
* `square_coeffs`, `square_coeffs_id`: the completions of squares (aL − bZ) and (√y I + βK²) of the general bound.
* `pstar_bound`: (d/4)k + y + z²/(4d) + k⁴/(64y) ≤ d/4 + 1/4 + 1/d for y = 1/8, 0 ≤ k ≤ 1, 0 ≤ z ≤ 2.
* `copies_suffice`: n ≥ e t²/ε + c t with c ≥ 2 and (2/3)e^1 ≤ c e gives t² e_L/n + (2/3) t³ e^{2t/n}/n² ≤ ε;
  `copies_general` (e = (d+1)/4 + 1/d, c = 2) and `copies_rank_one` (e = (d−1)/4, d ≥ 3, c = 4) instantiate it.

The diamond-norm and complete-positivity arguments are not part of this file.
-/

namespace OneCopyStep

open Real

/-- The quadratic form of the rank-one certificate. -/
noncomputable def form (d m a b c : ℝ) : ℝ :=
  ((d - 1) / 4 + (m ^ 2 - 1) / 2) * a ^ 2 + 1 / 2 * b ^ 2 + (d - 1) / 4 * c ^ 2 - m / 2 * a * b + 1 / 4 * b * c

/-- The coefficient matrix of the rank-one certificate is positive semidefinite for d ≥ 3. -/
theorem form_nonneg {d m : ℝ} (hd : 3 ≤ d) (a b c : ℝ) : 0 ≤ form d m a b c := by
  unfold form
  have h1 : 0 ≤ (d - 3) * c ^ 2 := mul_nonneg (by linarith) (sq_nonneg c)
  have h2 : 0 ≤ (d - 3) * a ^ 2 := mul_nonneg (by linarith) (sq_nonneg a)
  nlinarith [sq_nonneg (4 * c + b), sq_nonneg (m * a - b / 2), sq_nonneg b]

/-- At d = 2 the form can be negative: the condition d ≥ 3 of the rank-one certificate is needed. -/
theorem form_fails_d2 : form 2 0 1 0 0 < 0 := by
  unfold form; norm_num

/-- Completion of the square (aL − bZ): a² = d/4 and ab = 1/4 force b² = 1/(4d). -/
theorem square_coeffs {d : ℝ} (hd : 0 < d) :
    (Real.sqrt d / 2) ^ 2 = d / 4 ∧ (Real.sqrt d / 2) * (1 / (2 * Real.sqrt d)) = 1 / 4 ∧
      (1 / (2 * Real.sqrt d)) ^ 2 = 1 / (4 * d) := by
  have hs : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hp : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  refine ⟨by rw [div_pow, hs]; ring, by field_simp; ring, ?_⟩
  rw [div_pow, mul_pow, hs]; ring

/-- Completion of the square (√y I + βK²): √y β = 1/8 with β = 1/(8√y) and β² = 1/(64y). -/
theorem square_coeffs_id {y : ℝ} (hy : 0 < y) :
    Real.sqrt y * (1 / (8 * Real.sqrt y)) = 1 / 8 ∧ (1 / (8 * Real.sqrt y)) ^ 2 = 1 / (64 * y) := by
  have hs : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hp : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  refine ⟨by field_simp, ?_⟩
  rw [div_pow, mul_pow, hs]; ring

/-- The adjoint value P*(I) of the general certificate, with y = 1/8, ‖K‖ = k ≤ 1 and ‖Z‖ = z ≤ 2. -/
theorem pstar_bound {d k z : ℝ} (hd : 2 ≤ d) (hk0 : 0 ≤ k) (hk : k ≤ 1) (hz0 : 0 ≤ z) (hz : z ≤ 2) :
    d / 4 * k + 1 / 8 + z ^ 2 / (4 * d) + k ^ 4 / (64 * (1 / 8)) ≤ d / 4 + 1 / 4 + 1 / d := by
  have hdp : 0 < d := by linarith
  have h1 : d / 4 * k ≤ d / 4 := by nlinarith
  have h2 : z ^ 2 / (4 * d) ≤ 1 / d := by
    have hz2 : z ^ 2 ≤ 4 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hdp]; nlinarith [mul_le_mul_of_nonneg_right hz2 hdp.le]
  have h3 : k ^ 4 ≤ 1 := pow_le_one₀ hk0 hk
  have h4 : k ^ 4 / (64 * (1 / 8)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  linarith

/-- The copy count: n ≥ e t²/ε + c t copies, with c ≥ 2 and (2/3) e¹ ≤ c e, give total error at most ε. -/
theorem copies_suffice {e eL t ε n c : ℝ} (ht : 0 < t) (hε : 0 < ε) (heL : eL ≤ e) (he : 0 < e)
    (hc : 2 ≤ c) (hce : 2 / 3 * Real.exp 1 ≤ c * e) (hn : e * t ^ 2 / ε + c * t ≤ n) :
    t ^ 2 * eL / n + 2 / 3 * t ^ 3 * Real.exp (2 * t / n) / n ^ 2 ≤ ε := by
  have hA : 0 < e * t ^ 2 / ε := by positivity
  have hnp : 0 < n := by nlinarith
  have hn2 : 2 * t ≤ n := by nlinarith
  have hexp : Real.exp (2 * t / n) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 ((div_le_one hnp).2 hn2)
  have hen : e * t ^ 2 ≤ ε * n := by
    have : e * t ^ 2 / ε ≤ n := by nlinarith
    rwa [div_le_iff₀ hε, mul_comm n] at this
  -- the remainder is at most c t ε / n
  have hrem : 2 / 3 * t ^ 3 * Real.exp (2 * t / n) / n ^ 2 ≤ c * t * ε / n := by
    rw [div_le_div_iff₀ (by positivity) hnp]
    have h1 : 2 / 3 * t ^ 3 * Real.exp (2 * t / n) ≤ c * e * t ^ 3 := by
      have : 2 / 3 * Real.exp (2 * t / n) ≤ c * e := by linarith
      nlinarith [pow_pos ht 3]
    have h2 : c * e * t ^ 3 * n ≤ c * t * ε * n ^ 2 := by
      have hct : 0 ≤ c * t * n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hen hct]
    nlinarith [hnp]
  have hfirst : t ^ 2 * eL / n ≤ e * t ^ 2 / n := by
    apply div_le_div_of_nonneg_right _ hnp.le; nlinarith [sq_nonneg t]
  have hsum : e * t ^ 2 / n + c * t * ε / n ≤ ε := by
    rw [← add_div, div_le_iff₀ hnp]
    have : e * t ^ 2 / ε * ε = e * t ^ 2 := by field_simp
    nlinarith
  linarith

/-- e¹ < 2.7182818286. -/
theorem exp_one_le : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le

/-- Theorem 9: n ≥ ((d+1)/4 + 1/d) t²/ε + 2t copies suffice when e_L ≤ (d+1)/4 + 1/d. -/
theorem copies_general {d eL t ε n : ℝ} (hd : 2 ≤ d) (ht : 0 < t) (hε : 0 < ε)
    (heL : eL ≤ (d + 1) / 4 + 1 / d) (hn : ((d + 1) / 4 + 1 / d) * t ^ 2 / ε + 2 * t ≤ n) :
    t ^ 2 * eL / n + 2 / 3 * t ^ 3 * Real.exp (2 * t / n) / n ^ 2 ≤ ε := by
  have hdp : 0 < d := by linarith
  have he : (5 : ℝ) / 4 ≤ (d + 1) / 4 + 1 / d := by
    rw [← sub_nonneg]
    have : (d + 1) / 4 + 1 / d - 5 / 4 = (d - 2) ^ 2 / (4 * d) := by field_simp; ring
    rw [this]; positivity
  exact copies_suffice ht hε heL (by linarith) le_rfl (by nlinarith [exp_one_le]) hn

/-- Theorem 10: for d ≥ 3, n ≥ ((d−1)/4) t²/ε + 4t copies suffice when e_L ≤ (d−1)/4. -/
theorem copies_rank_one {d eL t ε n : ℝ} (hd : 3 ≤ d) (ht : 0 < t) (hε : 0 < ε)
    (heL : eL ≤ (d - 1) / 4) (hn : (d - 1) / 4 * t ^ 2 / ε + 4 * t ≤ n) :
    t ^ 2 * eL / n + 2 / 3 * t ^ 3 * Real.exp (2 * t / n) / n ^ 2 ≤ ε :=
  copies_suffice ht hε heL (by linarith) (by norm_num) (by nlinarith [exp_one_le]) hn

/-- The hypotheses of `copies_rank_one` hold, with a positive error budget. -/
theorem copies_rank_one_satisfiable :
    ∃ d eL t ε n : ℝ, 3 ≤ d ∧ 0 < t ∧ 0 < ε ∧ eL ≤ (d - 1) / 4 ∧ (d - 1) / 4 * t ^ 2 / ε + 4 * t ≤ n ∧ 0 < eL :=
  ⟨3, 1 / 2, 1, 1 / 10, 9, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The conclusion of `copies_suffice` is not automatic: with too few copies the leading term alone exceeds ε. -/
theorem copies_conclusion_can_fail :
    ¬ ((1 : ℝ) ^ 2 * (1 / 2) / 1 + 2 / 3 * 1 ^ 3 * Real.exp (2 * 1 / 1) / 1 ^ 2 ≤ 1 / 10) := by
  have : 0 < Real.exp (2 * 1 / 1) := Real.exp_pos _
  intro h; nlinarith

end OneCopyStep
