import Mathlib

/-!
# Scalar and matrix steps of the lower bound for PAC learning on near-parallel states

The states are `ψ_i = √(1 − λ) u + √λ e_i`. Their matrix of inner products is
`(1 − λ) J + λ I`, with eigenvalue `λ` on vectors of sum zero and `λ + (1 − λ) d` on the
all-ones vector. The average of `s` of the projections is rank one on the span of `u` and the
normalized sum of the `e_i`, with vector `(a, b/√s)`. The entropy difference `Δ(f)` splits into
three parts; the identities for the first two parts and the bound `−(1 − x) ln(1 − x) ≤ x` for
the third are proved here (natural logarithms; the base only rescales).
-/

namespace PacGram

open Real Matrix Finset

/-- The inner products of `ψ_i = √(1 − λ) u + √λ e_i` for orthonormal `u, e_1, …, e_d`. -/
theorem inner_psi {d : ℕ} (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i j : Fin d) :
    (√(1 - lam)) ^ 2 + (√lam) ^ 2 * (if i = j then 1 else 0) = (1 - lam) + lam * (if i = j then 1 else 0) := by
  rw [sq_sqrt (by linarith), sq_sqrt h0]

/-- The matrix `(1 − λ) J + λ I` maps a vector of sum zero to `λ` times itself. -/
theorem gram_sum_zero {d : ℕ} (lam : ℝ) (v : Fin d → ℝ) (hv : ∑ j, v j = 0) :
    ((1 - lam) • Matrix.of (fun _ _ : Fin d => (1 : ℝ)) + lam • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v
      = lam • v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Matrix.one_apply, Pi.smul_apply]
  have h : ∀ x, ((1 - lam) * 1 + lam * (if i = x then (1 : ℝ) else 0)) * v x
      = (1 - lam) * v x + (if i = x then lam * v i else 0) := by
    intro x; split_ifs with hx
    · subst hx; ring
    · ring
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib, ← Finset.mul_sum, hv]
  simp

/-- The matrix `(1 − λ) J + λ I` maps the all-ones vector to `λ + (1 − λ) d` times itself. -/
theorem gram_ones {d : ℕ} (lam : ℝ) :
    ((1 - lam) • Matrix.of (fun _ _ : Fin d => (1 : ℝ)) + lam • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ
      (fun _ => 1) = (lam + (1 - lam) * d) • (fun _ => (1 : ℝ)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Matrix.one_apply, Pi.smul_apply, mul_one]
  have h : ∀ x : Fin d, (1 - lam + lam * (if i = x then (1 : ℝ) else 0))
      = (1 - lam) + (if i = x then lam else 0) := by
    intro x; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib]
  simp
  ring

/-- On the span of `u` and the normalized sum of `s` vectors `e_i`, the average projection is
the rank-one matrix of the vector `(a, b/√s)`. -/
theorem block_rank_one (a b s : ℝ) (hs : 0 < s) :
    !![a ^ 2, a * b / √s; a * b / √s, b ^ 2 / s] = Matrix.vecMulVec ![a, b / √s] ![a, b / √s] := by
  have h : (√s) ^ 2 = s := sq_sqrt hs.le
  have hne : √s ≠ 0 := (sqrt_pos.mpr hs).ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply] <;> field_simp <;> rw [h] <;> ring

/-- First part of `Δ(f)`: the terms `log s` give the binary entropy. -/
theorem log_part (d f : ℝ) (hd : 0 < d) (hf0 : 0 < f) (hf1 : f < 1) :
    log d - f * log (f * d) - (1 - f) * log ((1 - f) * d)
      = -f * log f - (1 - f) * log (1 - f) := by
  rw [log_mul hf0.ne' hd.ne', log_mul (by linarith) hd.ne']
  ring

/-- Second part of `Δ(f)`: the terms `(1/s) log s`. -/
theorem inv_log_part (d f : ℝ) (hd : 0 < d) (hf0 : 0 < f) (hf1 : f < 1) :
    -(1 / d) * log d + f * (1 / (f * d)) * log (f * d) + (1 - f) * (1 / ((1 - f) * d)) * log ((1 - f) * d)
      = (1 / d) * log (f * (1 - f) * d) := by
  have h1 : (1 - f) ≠ 0 := by linarith
  rw [log_mul hf0.ne' hd.ne', log_mul h1 hd.ne', log_mul (mul_ne_zero hf0.ne' h1) hd.ne',
    log_mul hf0.ne' h1]
  field_simp
  ring

/-- The terms `1/s` give `Δ[x_s] = λ/d` for `x_s = λ(1 − 1/s)`. -/
theorem inv_part (lam d f : ℝ) (hd : 0 < d) (hf0 : 0 < f) (hf1 : f < 1) :
    lam * (1 - 1 / d) - f * (lam * (1 - 1 / (f * d))) - (1 - f) * (lam * (1 - 1 / ((1 - f) * d)))
      = lam / d := by
  have h1 : (1 - f) ≠ 0 := by linarith
  field_simp
  ring

/-- Third part of `Δ(f)`: `−(1 − x) log(1 − x) ≤ x` for `0 ≤ x < 1`. -/
theorem eta_one_sub_le (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x < 1) : -(1 - x) * log (1 - x) ≤ x := by
  have hy : 0 < 1 - x := by linarith
  have h := one_sub_inv_le_log_of_pos hy
  have h2 : 1 - (1 - x)⁻¹ = -x / (1 - x) := by field_simp; ring
  rw [h2, div_le_iff₀ hy] at h
  nlinarith

/-- `η(y) = −y log y ≥ 0` on `[0, 1]`. -/
theorem eta_nonneg (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ -y * log y := by
  have := log_nonpos h0 h1
  nlinarith

end PacGram
