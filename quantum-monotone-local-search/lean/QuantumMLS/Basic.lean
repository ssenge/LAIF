import Mathlib

/-!
# Quantum monotone local search: the averaging lemma and the bases

`amp_avg` is the averaging step of amplitude amplification with a random number of rounds: if the start state
has success amplitude sin θ, then j rounds give success probability sin²((2j+1)θ), and for m ≥ 1/sin 2θ the mean
over j = 0, …, m-1 is at least 1/4. The other theorems check the rounded bases √(2 − 1/c) of the README.
-/

open Finset Real

/-- Telescoping: 2 sin x · Σ_{j<m} cos((2j+1)x) = sin(2mx). -/
theorem two_sin_mul_sum_cos (x : ℝ) (m : ℕ) :
    2 * sin x * ∑ j ∈ range m, cos ((2 * (j : ℝ) + 1) * x) = sin (2 * m * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih, two_mul_sin_mul_cos]
    push_cast
    rw [show x - (2 * (m : ℝ) + 1) * x = -(2 * m * x) by ring,
      show x + (2 * (m : ℝ) + 1) * x = 2 * (m + 1) * x by ring, sin_neg]
    ring

/-- Averaging lemma: for sin 2θ > 0 and m · sin 2θ ≥ 1, Σ_{j<m} sin²((2j+1)θ) ≥ m/4. -/
theorem amp_avg (θ : ℝ) (m : ℕ) (hs : 0 < sin (2 * θ)) (hm : 1 ≤ m * sin (2 * θ)) :
    (m : ℝ) / 4 ≤ ∑ j ∈ range m, sin ((2 * (j : ℝ) + 1) * θ) ^ 2 := by
  have hsq : ∀ j : ℕ, sin ((2 * (j : ℝ) + 1) * θ) ^ 2
      = 1 / 2 - cos ((2 * (j : ℝ) + 1) * (2 * θ)) / 2 := by
    intro j
    rw [sin_sq_eq_half_sub, show 2 * ((2 * (j : ℝ) + 1) * θ) = (2 * j + 1) * (2 * θ) by ring]
  simp_rw [hsq]
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div]
  have key := two_sin_mul_sum_cos (2 * θ) m
  have h1 : sin (2 * m * (2 * θ)) ≤ 1 := sin_le_one _
  set S := ∑ j ∈ range m, cos ((2 * (j : ℝ) + 1) * (2 * θ))
  have hS : 2 * S ≤ m := by
    by_contra h
    push_neg at h
    have := mul_lt_mul_of_pos_left h hs
    linarith
  linarith

/-- Feedback Vertex Set, extension base 3.460: √(2 − 1/3.460) ≤ 1.3081. -/
theorem fvs_base : sqrt (2 - 1 / 3.460) ≤ 1.3081 :=
  sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Cluster Vertex Deletion, extension base 1.811: √(2 − 1/1.811) ≤ 1.2033. -/
theorem cvd_base : sqrt (2 - 1 / 1.811) ≤ 1.2033 :=
  sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- 3-Hitting Set and its weighted version, extension base 2.168: √(2 − 1/2.168) ≤ 1.2405. -/
theorem hs3_base : sqrt (2 - 1 / 2.168) ≤ 1.2405 :=
  sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Min-Ones 3-SAT, base 3: √(5/3) ≤ 1.2910. -/
theorem d3_base : sqrt (2 - 1 / 3) ≤ 1.2910 :=
  sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- d = 4, base 4: √(7/4) ≤ 1.3229. -/
theorem d4_base : sqrt (2 - 1 / 4) ≤ 1.3229 :=
  sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- d = 5, base 5: √(9/5) ≤ 1.3417. -/
theorem d5_base : sqrt (2 - 1 / 5) ≤ 1.3417 :=
  sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Multicut on Trees, extension base ρ = √(√2 + 1): √(2 − 1/ρ) ≤ 1.1647. -/
theorem mct_base : sqrt (2 - 1 / sqrt (sqrt 2 + 1)) ≤ 1.1647 := by
  have h2 : sqrt 2 ≤ 1.41422 := sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hρ : sqrt (sqrt 2 + 1) ≤ 1.5538 := sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hpos : 0 < sqrt (sqrt 2 + 1) := sqrt_pos.mpr (by positivity)
  have hinv : 1 / 1.5538 ≤ 1 / sqrt (sqrt 2 + 1) := one_div_le_one_div_of_le hpos hρ
  exact sqrt_le_iff.mpr ⟨by norm_num, by norm_num at hinv ⊢; linarith⟩
