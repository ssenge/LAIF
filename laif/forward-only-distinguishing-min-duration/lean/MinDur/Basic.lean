import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Complex.Basic

/-!
# Algebra and constants of the swap-and-project distinguishing algorithm

On span{|0⟩, |1⟩} one step has the matrix `A`, and one cycle is `C = X A X A` with the swap `X`.
In the YES case `A = diag(1, δ)` and `C = δ I`. In the NO case `A` is symmetric and
`C = p I + N` with `N² = q² I`. The file also checks the numerical constants of the bound
`t / P ≤ 46 max{1/ε, τ/ε²}`.
-/

open Matrix

namespace MinDur

/-- The swap of `|0⟩` and `|1⟩`. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- YES case: the cycle is a multiple of the identity. -/
theorem cycle_yes (δ : ℂ) : X * !![1, 0; 0, δ] * X * !![1, 0; 0, δ] = δ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]

/-- NO case: the cycle of a symmetric step matrix. -/
theorem cycle_no (α β δ : ℂ) :
    X * !![α, β; β, δ] * X * !![α, β; β, δ] = !![α * δ + β ^ 2, 2 * β * δ; 2 * α * β, α * δ + β ^ 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The off-diagonal part `N` of the cycle squares to `q² I` with `q² = 4 α β² δ`. -/
theorem offdiag_sq (α β δ : ℂ) :
    !![0, 2 * β * δ; 2 * α * β, 0] * !![0, 2 * β * δ; 2 * α * β, 0] =
      (4 * α * β ^ 2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `exp(-1/2) > 0.6065`. -/
theorem exp_neg_half_gt : (0.6065 : ℝ) < Real.exp (-(1 / 2)) := by
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have hlt : Real.exp (1 / 2) < 1.6488 := by nlinarith
  rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) h0]
  calc Real.exp (1 / 2) < 1.6488 := hlt
    _ ≤ (0.6065 : ℝ)⁻¹ := by norm_num

/-- `sinh 1 < 1.1753`, so `2 - sinh 1 > 0.824`. -/
theorem sinh_one_lt : Real.sinh 1 < 1.1753 := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [this]
  have hinv : (2.7182818286 : ℝ)⁻¹ < (Real.exp 1)⁻¹ := (inv_lt_inv₀ (by norm_num) h0).mpr h1
  have : (Real.exp 1)⁻¹ < (2.7182818283 : ℝ)⁻¹ := (inv_lt_inv₀ h0 (by norm_num)).mpr h2
  have : (2.7182818286 : ℝ)⁻¹ > 0.3678 := by norm_num
  nlinarith

/-- The amplitude constant: `2 · (7/8) · 0.958 · e^{-1/2} · (2 - sinh 1) ≥ 0.837`. -/
theorem amplitude_constant :
    (0.837 : ℝ) ≤ 2 * (7 / 8) * 0.958 * Real.exp (-(1 / 2)) * (2 - Real.sinh 1) := by
  have h1 := exp_neg_half_gt
  have h2 := sinh_one_lt
  have : (0.824 : ℝ) < 2 - Real.sinh 1 := by linarith
  have hpos : 0 < Real.exp (-(1 / 2)) := Real.exp_pos _
  nlinarith

/-- `sin s ≥ 0.958 s` for `0 ≤ s ≤ 1/2`, from `sin s ≥ s - s³/6`. -/
theorem sin_ge (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : 0.958 * s ≤ Real.sin s := by
  have := Real.sin_ge_sub_cube h0
  nlinarith [sq_nonneg s]

/-- The final constants: `2 / 0.70 ≤ 2.86`, `2 · 2.86 · 8 ≤ 46`, and the `m = 1` and long-step cases. -/
theorem final_constants :
    (2 : ℝ) / 0.70 ≤ 2.86 ∧ 2 * 2.86 * 8 ≤ (46 : ℝ) ∧ (0.837 : ℝ) ^ 2 ≥ 0.70 ∧
      (2 : ℝ) / (2 * (7 / 8) * 0.958) ^ 2 ≤ 0.72 ∧ 0.72 * 8 ≤ (5.8 : ℝ) := by
  norm_num

end MinDur
