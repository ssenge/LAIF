import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Combinatorial and scalar steps of optimal anti-symmetrization

The completion constant, the comparison of the completion fidelities with `1/(d - r + 1)`, the
bound `Σ 1/λ_i ≥ r²`, and the constants of the copy bounds `max{Σ 1/λ_i / 2, ln(1/(2δ))/(2λ_min)}`
and `max{2 Σ 1/λ_i, 7 ln(2/δ)/λ_min}`.
-/

open Real

namespace AntiSym

/-- The completion fidelity: `C(d, r) C(r, k) = C(d, k) C(d - k, r - k)`, so
`C(d, k)/(C(r, k) C(d, r)) = 1/C(d - k, r - k)`. -/
theorem completion_identity (d r k : ℕ) (hk : k ≤ r) :
    d.choose r * r.choose k = d.choose k * (d - k).choose (r - k) :=
  Nat.choose_mul hk

/-- `C(d - k, r - k) ≥ d - r + 1` for `k < r ≤ d`. -/
theorem choose_ge (d r k : ℕ) (hk : k < r) (hr : r ≤ d) :
    d - r + 1 ≤ (d - k).choose (r - k) := by
  set a := d - k
  set b := r - k
  have hb : 1 ≤ b := by omega
  have hba : b ≤ a := by omega
  have e : d - r + 1 = a - b + 1 := by omega
  rw [e, ← Nat.choose_symm hba]
  calc a - b + 1 = (a - b + 1).choose (a - b) := (Nat.choose_succ_self_right (a - b)).symm
    _ ≤ a.choose (a - b) := Nat.choose_le_choose (a - b) (by omega)

/-- `Σ 1/λ_i ≥ r²` for positive weights with sum 1. -/
theorem sum_inv_ge {r : ℕ} (l : Fin r → ℝ) (hl : ∀ i, 0 < l i) (hs : ∑ i, l i = 1) :
    (r : ℝ) ^ 2 ≤ ∑ i, 1 / l i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (l i))
    (fun i => 1 / Real.sqrt (l i))
  have e1 : ∀ i, Real.sqrt (l i) * (1 / Real.sqrt (l i)) = 1 := fun i => by
    have := Real.sqrt_pos.mpr (hl i); field_simp
  have e2 : ∀ i, Real.sqrt (l i) ^ 2 = l i := fun i => Real.sq_sqrt (hl i).le
  have e3 : ∀ i, (1 / Real.sqrt (l i)) ^ 2 = 1 / l i := fun i => by
    rw [div_pow, one_pow, Real.sq_sqrt (hl i).le]
  simp only [e1, e2, e3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, hs, one_mul] at h
  exact h

/-- `t - 1 - ln t ≥ t/7` for `t ≥ 2`. -/
theorem rate_ge (t : ℝ) (ht : 2 ≤ t) : t / 7 ≤ t - 1 - Real.log t := by
  have h2 : Real.log t - Real.log 2 ≤ t / 2 - 1 := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show 0 < t / 2 by linarith)
    linarith
  have := Real.log_two_lt_d9
  nlinarith

/-- `exp(-(ln 2 - 1/2)) < 5/6`. -/
theorem lower_tail_constant : Real.exp (-(Real.log 2 - 1 / 2)) < 5 / 6 := by
  have e : Real.exp (-(Real.log 2 - 1 / 2)) = Real.exp (1 / 2) / 2 := by
    rw [show -(Real.log 2 - 1 / 2) = 1 / 2 - Real.log 2 by ring, Real.exp_sub,
      Real.exp_log (by norm_num)]
  rw [e]
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith

/-- `-ln(1 - x) ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem neg_log_le (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) : -Real.log (1 - x) ≤ 2 * x := by
  have h1 : 0 < 1 - x := by linarith
  rw [← Real.log_inv]
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  have e : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  have : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith

/-- From the upper bound of the optimal fidelity: success `1 - δ` forces `P ≥ 1 - 2δ`, where
`P = P(L_n = r)` and `D = d - r + 1 ≥ 2`. -/
theorem success_forces (P δ D : ℝ) (hD : 2 ≤ D) (hP : P ≤ 1)
    (h : 1 - δ ≤ P + (1 - P) / D) : 1 - 2 * δ ≤ P := by
  have hD0 : 0 < D := by linarith
  have : (1 - P) / D ≤ (1 - P) / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hD
  linarith

/-- Two failure chances of `δ/2` each: `(1 - δ/2)² ≥ 1 - δ`. -/
theorem two_halves (δ : ℝ) : 1 - δ ≤ (1 - δ / 2) ^ 2 := by nlinarith [sq_nonneg δ]

end AntiSym
