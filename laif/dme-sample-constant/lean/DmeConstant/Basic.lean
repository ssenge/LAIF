import Mathlib

/-!
# Scalar steps of the leading constant 1 of sample-based Hamiltonian simulation

Theorem 1 (density matrix exponentiation): one step of time Δ has error at most Δ² + 2.65 Δ³, and
⌈t²/ε + 3t⌉ steps give error at most ε. Theorem 2 (every protocol with n copies): n ε ≥ t² (1 − 10 t)² for t ≤ 1/10.

* `pstar_eig`: the eigenvalues (1 − λ²/2)² of P*(I) = (I − σ²/2)² lie in [0, 1] for 0 ≤ λ ≤ 1.
* `sin_sq_sub`, `half_sin_two`, `exp_tail`: the scalar remainders of the step.
* `step_remainder`: Δ² + |sin²Δ − Δ²| + |sin(2Δ)/2 − Δ| + ½(e^{2Δ} − 1 − 2Δ − 2Δ²) ≤ Δ² + 2.65 Δ³ for 0 ≤ Δ ≤ 1/2.
* `copies_dme`: n ≥ t²/ε + 3t gives t/n ≤ 1/2 and n ((t/n)² + 2.65 (t/n)³) ≤ ε.
* `q_target`, `q_target_norm`: (e^{−it} − 1)(d − 1 + e^{it}) = −(d − 2)(1 − cos t) − i d sin t, of modulus ≥ d sin t.
* `delta_le`: δ_n = (2n + 2) Σ_{k ≥ n+2} (2t)^k/k! + Σ_{k ≥ n+2} (2t)^k/(k − 1)! ≤ 14 t³ for n ≥ 1, 0 ≤ t ≤ 1/10,
  with the tails written as e^{2t} minus a partial sum.
* `final_bound`: from sin t − 4(n + 1)ε − δ ≤ a, a² ≤ n ε and δ ≤ 14 t³ follows n ε ≥ t² (1 − 10 t)².
* `final_bound_satisfiable`, `final_conclusion_can_fail`: the hypotheses of `final_bound` hold for some values, and
  its conclusion fails at ε = 0.

The diamond-norm, Choi-matrix and Bernstein arguments are not part of this file.
-/

namespace DmeConstant

open Real Finset

/-- The eigenvalues of P*(I) = (I − σ²/2)² lie in [0, 1]. -/
theorem pstar_eig {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) : 0 ≤ (1 - l ^ 2 / 2) ^ 2 ∧ (1 - l ^ 2 / 2) ^ 2 ≤ 1 := by
  have ha : 0 ≤ 1 - l ^ 2 / 2 := by nlinarith
  have hb : 1 - l ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg l]
  exact ⟨by positivity, by nlinarith⟩

/-- |sin²Δ − Δ²| ≤ Δ⁴/3 for 0 ≤ Δ ≤ 1/2. -/
theorem sin_sq_sub {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2) : |sin D ^ 2 - D ^ 2| ≤ D ^ 4 / 3 := by
  have h1 := sin_ge_sub_cube hD0
  have h2 := sin_le hD0
  have h3 : 0 ≤ D - D ^ 3 / 6 := by nlinarith [pow_nonneg hD0 2]
  have hs : 0 ≤ sin D := h3.trans h1
  have lo : (D - D ^ 3 / 6) ^ 2 ≤ sin D ^ 2 := pow_le_pow_left₀ h3 h1 2
  have hi : sin D ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hs h2 2
  rw [abs_le]; constructor
  · nlinarith [pow_nonneg hD0 6]
  · nlinarith [pow_nonneg hD0 4]

/-- |sin(2Δ)/2 − Δ| ≤ 2Δ³/3 for Δ ≥ 0. -/
theorem half_sin_two {D : ℝ} (hD0 : 0 ≤ D) : |sin (2 * D) / 2 - D| ≤ 2 * D ^ 3 / 3 := by
  have h0 : 0 ≤ 2 * D := by linarith
  have h1 := sin_ge_sub_cube h0
  have h2 := sin_le h0
  have h8 : (2 * D) ^ 3 = 8 * D ^ 3 := by ring
  rw [abs_le]; constructor <;> nlinarith [pow_nonneg hD0 3]

/-- e^y − 1 − y − y²/2 ≤ 2y³/9 for 0 ≤ y ≤ 1. -/
theorem exp_tail {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) : exp y - (1 + y + y ^ 2 / 2) ≤ 2 * y ^ 3 / 9 := by
  have h := exp_bound' hy0 hy (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The error of one step of time Δ ≤ 1/2 is at most Δ² + 2.65 Δ³. -/
theorem step_remainder {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2) :
    D ^ 2 + |sin D ^ 2 - D ^ 2| + |sin (2 * D) / 2 - D| + (exp (2 * D) - (1 + 2 * D + (2 * D) ^ 2 / 2)) / 2
      ≤ D ^ 2 + 2.65 * D ^ 3 := by
  have h1 := sin_sq_sub hD0 hD
  have h2 := half_sin_two hD0
  have h3 := exp_tail (by linarith : 0 ≤ 2 * D) (by linarith : 2 * D ≤ 1)
  have h4 : D ^ 4 ≤ D ^ 3 / 2 := by nlinarith [pow_nonneg hD0 3]
  have h8 : (2 * D) ^ 3 = 8 * D ^ 3 := by ring
  nlinarith [pow_nonneg hD0 3]

/-- n ≥ t²/ε + 3t steps: the step time is at most 1/2 and the total error is at most ε. -/
theorem copies_dme {t ε n : ℝ} (ht : 0 < t) (hε : 0 < ε) (hn : t ^ 2 / ε + 3 * t ≤ n) :
    t / n ≤ 1 / 2 ∧ n * ((t / n) ^ 2 + 2.65 * (t / n) ^ 3) ≤ ε := by
  have hA : 0 < t ^ 2 / ε := by positivity
  have hnp : 0 < n := by linarith
  have hεn : t ^ 2 ≤ n * ε := (div_le_iff₀ hε).1 (by linarith)
  have hεA : ε * (t ^ 2 / ε) = t ^ 2 := by field_simp
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hnp]; nlinarith
  · have key : t ^ 2 * n + 2.65 * t ^ 3 ≤ ε * n ^ 2 := by
      have e1 : ε * n * (t ^ 2 / ε + 3 * t) ≤ ε * n * n :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      nlinarith [pow_pos ht 3, mul_le_mul_of_nonneg_left hεn (by positivity : (0 : ℝ) ≤ 3 * t)]
    have hrw : n * ((t / n) ^ 2 + 2.65 * (t / n) ^ 3) = (t ^ 2 * n + 2.65 * t ^ 3) / n ^ 2 := by
      field_simp
    rw [hrw, div_le_iff₀ (by positivity)]; linarith

/-- The value of Q at the target: (e^{−it} − 1)(d − 1 + e^{it}) = −(d − 2)(1 − cos t) − i d sin t. -/
theorem q_target (d t : ℝ) :
    (Complex.exp (-(t : ℂ) * Complex.I) - 1) * ((d : ℂ) - 1 + Complex.exp ((t : ℂ) * Complex.I)) =
      (((-(d - 2) * (1 - Real.cos t)) : ℝ) : ℂ) - ((d * Real.sin t : ℝ) : ℂ) * Complex.I := by
  have e1 : Complex.exp (-(t : ℂ) * Complex.I) = Complex.cos t - Complex.sin t * Complex.I := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
  have e2 : Complex.exp ((t : ℂ) * Complex.I) = Complex.cos t + Complex.sin t * Complex.I := Complex.exp_mul_I _
  rw [e1, e2]; push_cast
  linear_combination Complex.cos_sq_add_sin_sq (t : ℂ) - Complex.sin (t : ℂ) ^ 2 * Complex.I_sq

/-- |Q(Y)| ≥ d sin t when d ≥ 0 and sin t ≥ 0. -/
theorem q_target_norm {d t : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ Real.sin t) :
    d * Real.sin t ≤ ‖(Complex.exp (-(t : ℂ) * Complex.I) - 1) * ((d : ℂ) - 1 + Complex.exp ((t : ℂ) * Complex.I))‖ := by
  rw [q_target]
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  simp [Complex.sin_ofReal_re, abs_of_nonneg hd, abs_of_nonneg hs]

/-- The tail e^y − Σ_{k<m} y^k/k! = Σ_{k ≥ m} y^k/k!. -/
noncomputable def tail (y : ℝ) (m : ℕ) : ℝ := exp y - ∑ k ∈ range m, y ^ k / k.factorial

/-- δ_n = (2n + 2) R + R′ with R = Σ_{k ≥ n+2} (2t)^k/k! and R′ = Σ_{k ≥ n+2} (2t)^k/(k − 1)! = 2t Σ_{j ≥ n+1} (2t)^j/j!. -/
noncomputable def delta (n : ℕ) (t : ℝ) : ℝ := (2 * n + 2) * tail (2 * t) (n + 2) + 2 * t * tail (2 * t) (n + 1)

theorem tail_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) {m : ℕ} (hm : 0 < m) :
    tail y m ≤ y ^ m * (m + 1) / (m.factorial * m) := by
  have h := exp_bound' hy0 hy hm; unfold tail; linarith

/-- δ_n ≤ 14 t³ for n ≥ 1 and 0 ≤ t ≤ 1/10. -/
theorem delta_le {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10) : delta n t ≤ 14 * t ^ 3 := by
  set y := 2 * t with hy
  have hy0 : 0 ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT1 := tail_le hy0 hy1 (m := n + 2) (by omega)
  have hT0 := tail_le hy0 hy1 (m := n + 1) (by omega)
  have hF0 : ((n : ℝ) + 1) ≤ ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial (n + 1)
  have hF1 : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  push_cast at hT1 hT0
  rw [hF1] at hT1
  have hp : y ^ (n + 2) ≤ y ^ 3 := pow_le_pow_of_le_one hy0 hy1 (by omega)
  have hp1 : y * y ^ (n + 1) = y ^ (n + 2) := by ring
  have hF0p : 0 < ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  -- coefficient bounds
  have c1 : (2 * (n : ℝ) + 2) * ((n + 2 + 1) / (((n : ℝ) + 2) * ((n + 1).factorial : ℝ) * ((n : ℝ) + 2))) ≤ 8 / 9 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hF0 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 2))]
  have c0 : ((n : ℝ) + 1 + 1) / (((n + 1).factorial : ℝ) * ((n : ℝ) + 1)) ≤ 3 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hF0 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1))]
  have hT1' : (2 * (n : ℝ) + 2) * tail y (n + 2) ≤ y ^ (n + 2) * (8 / 9) := by
    have := mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 2)
    calc (2 * (n : ℝ) + 2) * tail y (n + 2)
        ≤ (2 * (n : ℝ) + 2) * (y ^ (n + 2) * (n + 2 + 1) / (((n : ℝ) + 2) * ((n + 1).factorial : ℝ) * ((n : ℝ) + 2))) := this
      _ = y ^ (n + 2) * ((2 * (n : ℝ) + 2) * ((n + 2 + 1) / (((n : ℝ) + 2) * ((n + 1).factorial : ℝ) * ((n : ℝ) + 2)))) := by ring
      _ ≤ y ^ (n + 2) * (8 / 9) := mul_le_mul_of_nonneg_left c1 (by positivity)
  have hT0' : y * tail y (n + 1) ≤ y ^ (n + 2) * (3 / 4) := by
    have := mul_le_mul_of_nonneg_left hT0 hy0
    calc y * tail y (n + 1) ≤ y * (y ^ (n + 1) * (n + 1 + 1) / (((n + 1).factorial : ℝ) * ((n : ℝ) + 1))) := this
      _ = (y * y ^ (n + 1)) * (((n : ℝ) + 1 + 1) / (((n + 1).factorial : ℝ) * ((n : ℝ) + 1))) := by ring
      _ ≤ y ^ (n + 2) * (3 / 4) := by rw [hp1]; exact mul_le_mul_of_nonneg_left c0 (by positivity)
  unfold delta
  rw [← hy]
  have h3 : y ^ 3 = 8 * t ^ 3 := by rw [hy]; ring
  nlinarith [pow_nonneg hy0 (n + 2)]

/-- From sin t − 4(n + 1)ε − δ ≤ a, a² ≤ nε and δ ≤ 14t³ (0 < t ≤ 1/10, n ≥ 1) follows nε ≥ t²(1 − 10t)². -/
theorem final_bound {n : ℕ} (hn : 1 ≤ n) {t ε a δ : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 10)
    (hδ : δ ≤ 14 * t ^ 3) (ha : Real.sin t - 4 * ((n : ℝ) + 1) * ε - δ ≤ a)
    (hsq : a ^ 2 ≤ n * ε) : t ^ 2 * (1 - 10 * t) ^ 2 ≤ n * ε := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu0 : 0 ≤ 1 - 10 * t := by linarith
  have hu1 : (1 - 10 * t) ^ 2 ≤ 1 := by nlinarith
  by_cases h : t ^ 2 ≤ n * ε
  · nlinarith [pow_pos ht0 2]
  · push Not at h
    have hε : 0 ≤ ε := by nlinarith [sq_nonneg a]
    have hs := sin_ge_sub_cube ht0.le
    have h8 : 4 * ((n : ℝ) + 1) * ε ≤ 8 * t ^ 2 := by nlinarith
    have ht3 : t ^ 3 ≤ t ^ 2 / 10 := by nlinarith [pow_pos ht0 2]
    have hb : t * (1 - 10 * t) ≤ a := by nlinarith
    have hb0 : 0 ≤ t * (1 - 10 * t) := mul_nonneg ht0.le hu0
    have := pow_le_pow_left₀ hb0 hb 2
    nlinarith

/-- The hypotheses of `final_bound` hold for some values. -/
theorem final_bound_satisfiable :
    ∃ t ε a δ : ℝ, 0 < t ∧ t ≤ 1 / 10 ∧ δ ≤ 14 * t ^ 3 ∧
      Real.sin t - 4 * ((1 : ℕ) + 1 : ℝ) * ε - δ ≤ a ∧ a ^ 2 ≤ (1 : ℕ) * ε := by
  refine ⟨1 / 20, (1 / 20) ^ 2, 1 / 20, 0, by norm_num, by norm_num, by positivity, ?_, by norm_num⟩
  have := sin_le (by norm_num : (0 : ℝ) ≤ 1 / 20)
  nlinarith

/-- The conclusion of `final_bound` is not automatic: it fails at ε = 0 for t = 1/20. -/
theorem final_conclusion_can_fail : ¬ ((1 / 20 : ℝ) ^ 2 * (1 - 10 * (1 / 20)) ^ 2 ≤ (1 : ℕ) * (0 : ℝ)) := by
  norm_num

end DmeConstant
