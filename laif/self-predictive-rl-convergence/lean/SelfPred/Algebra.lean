import Mathlib

/-!
# Linear self-predictive learning: the algebra of the dynamics

For a symmetric `T : n × n` and `Φ : n × k`, the latent predictor is `Q = Φᵀ T Φ`, the projection
`P = 1 - Φ Φᵀ`, the vector field of the dynamics `V(Φ) = P T Φ Q`, and `G = (T Φ)ᵀ P (T Φ)`.
This file proves the identities behind the conservation of the sign pattern of `Q`:
* `qdot_eq`: `V(Φ)ᵀ T Φ + Φᵀ T V(Φ) = Q G + G Q`, so `Q' = Q G + G Q` along the dynamics;
* `tangent_eq`: `V(Φ)ᵀ Φ + Φᵀ V(Φ) = 0` when `Φᵀ Φ = 1`, so the constraint `Φᵀ Φ = 1` is preserved;
* `G_posSemidef`: `G` is positive semidefinite when `Φᵀ Φ = 1`;
* `crit_invariant`: if `V(Φ) = 0` and `Q` is invertible, then `T Φ = Φ Q`, so the span of `Φ` is `T`-invariant;
* `conj_deriv_zero`: the identity that makes `W⁻¹ Q W⁻ᵀ` constant when `W' = G W`.
-/

set_option linter.unusedSectionVars false

open Matrix

namespace SelfPred

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- The latent predictor `Q = Φᵀ T Φ`. -/
def Qm (T : Matrix n n ℝ) (Φ : Matrix n k ℝ) : Matrix k k ℝ := Φᵀ * T * Φ

/-- The projection `P = 1 - Φ Φᵀ`. -/
def Pm (Φ : Matrix n k ℝ) : Matrix n n ℝ := 1 - Φ * Φᵀ

/-- The vector field of the dynamics, `V(Φ) = (1 - Φ Φᵀ) T Φ Q`. -/
def vf (T : Matrix n n ℝ) (Φ : Matrix n k ℝ) : Matrix n k ℝ := Pm Φ * T * Φ * Qm T Φ

/-- `G = (T Φ)ᵀ (1 - Φ Φᵀ) (T Φ)`. -/
def Gm (T : Matrix n n ℝ) (Φ : Matrix n k ℝ) : Matrix k k ℝ := (T * Φ)ᵀ * Pm Φ * (T * Φ)

lemma Pm_transpose (Φ : Matrix n k ℝ) : (Pm Φ)ᵀ = Pm Φ := by
  simp [Pm, transpose_sub, transpose_mul]

lemma Qm_transpose {T : Matrix n n ℝ} (hT : Tᵀ = T) (Φ : Matrix n k ℝ) : (Qm T Φ)ᵀ = Qm T Φ := by
  simp [Qm, transpose_mul, hT, Matrix.mul_assoc]

lemma Gm_transpose (T : Matrix n n ℝ) (Φ : Matrix n k ℝ) : (Gm T Φ)ᵀ = Gm T Φ := by
  simp [Gm, transpose_mul, Pm_transpose, Matrix.mul_assoc]

/-- The derivative identity `V(Φ)ᵀ T Φ + Φᵀ T V(Φ) = Q G + G Q`. -/
theorem qdot_eq {T : Matrix n n ℝ} (hT : Tᵀ = T) (Φ : Matrix n k ℝ) :
    (vf T Φ)ᵀ * T * Φ + Φᵀ * T * vf T Φ = Qm T Φ * Gm T Φ + Gm T Φ * Qm T Φ := by
  have h1 : (vf T Φ)ᵀ = Qm T Φ * Φᵀ * T * Pm Φ := by
    simp only [vf, transpose_mul, Qm_transpose hT, Pm_transpose, hT, Matrix.mul_assoc]
  rw [h1]
  simp only [vf, Gm, transpose_mul, hT, Matrix.mul_assoc]

lemma Pm_mul_self {Φ : Matrix n k ℝ} (h : Φᵀ * Φ = 1) : Pm Φ * Φ = 0 := by
  simp [Pm, Matrix.sub_mul, Matrix.mul_assoc, h]

lemma transpose_mul_Pm {Φ : Matrix n k ℝ} (h : Φᵀ * Φ = 1) : Φᵀ * Pm Φ = 0 := by
  simp [Pm, Matrix.mul_sub, ← Matrix.mul_assoc, h]

/-- The constraint `Φᵀ Φ = 1` is preserved: `V(Φ)` is tangent to the manifold of orthonormal frames. -/
theorem tangent_eq {T : Matrix n n ℝ} (hT : Tᵀ = T) {Φ : Matrix n k ℝ} (h : Φᵀ * Φ = 1) :
    (vf T Φ)ᵀ * Φ + Φᵀ * vf T Φ = 0 := by
  have h1 : (vf T Φ)ᵀ = Qm T Φ * Φᵀ * T * Pm Φ := by
    simp only [vf, transpose_mul, Qm_transpose hT, Pm_transpose, hT, Matrix.mul_assoc]
  rw [h1]
  have a : Qm T Φ * Φᵀ * T * Pm Φ * Φ = 0 := by
    rw [Matrix.mul_assoc, Pm_mul_self h, Matrix.mul_zero]
  have b : Φᵀ * vf T Φ = 0 := by
    simp only [vf, ← Matrix.mul_assoc, transpose_mul_Pm h, Matrix.zero_mul]
  rw [a, b, add_zero]

lemma Pm_idem {Φ : Matrix n k ℝ} (h : Φᵀ * Φ = 1) : Pm Φ * Pm Φ = Pm Φ := by
  have : Φ * Φᵀ * (Φ * Φᵀ) = Φ * Φᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, h, Matrix.one_mul]
  simp only [Pm, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, this]
  abel

/-- `G` is positive semidefinite on the manifold of orthonormal frames. -/
theorem G_posSemidef (T : Matrix n n ℝ) {Φ : Matrix n k ℝ} (h : Φᵀ * Φ = 1) : (Gm T Φ).PosSemidef := by
  have hG : Gm T Φ = (Pm Φ * (T * Φ))ᴴ * (Pm Φ * (T * Φ)) := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, Pm_transpose]
    simp only [Gm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Pm Φ) (Pm Φ), Pm_idem h]
  rw [hG]; exact posSemidef_conjTranspose_mul_self _

/-- At a critical point with invertible predictor, `T Φ = Φ Q`: the span of `Φ` is `T`-invariant. -/
theorem crit_invariant {T : Matrix n n ℝ} {Φ : Matrix n k ℝ} (hQ : IsUnit (Qm T Φ)) (h : vf T Φ = 0) :
    T * Φ = Φ * Qm T Φ := by
  have h0 : Pm Φ * T * Φ = 0 := by
    have := congrArg (· * (Qm T Φ)⁻¹) h
    simpa [vf, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hQ)] using this
  have : T * Φ - Φ * (Φᵀ * T * Φ) = 0 := by
    simpa [Pm, Matrix.sub_mul, Matrix.mul_assoc] using h0
  simpa [Qm, sub_eq_zero] using this

/-- With `V' = -V G` (so `V = W⁻¹` for `W' = G W`), `Gᵀ = G` and `Q' = Q G + G Q`, the derivative of
`V Q Vᵀ` vanishes: `V' Q Vᵀ + V Q' Vᵀ + V Q V'ᵀ = 0`. -/
theorem conj_deriv_zero (V Q G : Matrix k k ℝ) (hG : Gᵀ = G) :
    (-(V * G)) * Q * Vᵀ + V * (Q * G + G * Q) * Vᵀ + V * Q * (-(V * G))ᵀ = 0 := by
  rw [transpose_neg, transpose_mul, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

end SelfPred
