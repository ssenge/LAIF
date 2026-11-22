import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Two-qubit identities behind the fixed states of the partial-trace reservoir

Basis order `|00⟩, |01⟩, |10⟩, |11⟩`. The antisymmetric state `s = |01⟩ − |10⟩` of two qubits is an
eigenvector of `X⊗X + Y⊗Y` with eigenvalue `−2`, and it is annihilated by `X⊗I + I⊗X`,
`Y⊗I + I⊗Y` and `Z⊗I + I⊗Z`. With equal couplings every term of the coupling operator that
joins qubit 1 or 2 to another qubit contains one of these sums, so `s ⊗ (rest)` is an invariant
subspace.
-/

open Matrix Complex

namespace ReservoirSinglet

/-- `X⊗X + Y⊗Y`. -/
def XXYY : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 0]
/-- `X⊗I + I⊗X`. -/
def Xsum : Matrix (Fin 4) (Fin 4) ℂ := !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 0]
/-- `Y⊗I + I⊗Y`. -/
def Ysum : Matrix (Fin 4) (Fin 4) ℂ := !![0, -I, -I, 0; I, 0, 0, -I; I, 0, 0, -I; 0, I, I, 0]
/-- `Z⊗I + I⊗Z`. -/
def Zsum : Matrix (Fin 4) (Fin 4) ℂ := !![2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -2]
/-- The antisymmetric state, unnormalized. -/
def s : Fin 4 → ℂ := ![0, 1, -1, 0]

/-- The single-qubit factors whose products give the matrices above. -/
def X1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def Z1 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Index map `(a, b) ↦ 2a + b`. -/
def idx (a b : Fin 2) : Fin 4 := ⟨2 * a.val + b.val, by omega⟩

/-- The matrices are the stated tensor products. -/
theorem XXYY_eq (a b c d : Fin 2) :
    XXYY (idx a b) (idx c d) = X1 a c * X1 b d + Y1 a c * Y1 b d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [XXYY, X1, Y1, idx] <;> norm_num [Complex.ext_iff]

theorem Xsum_eq (a b c d : Fin 2) :
    Xsum (idx a b) (idx c d) = X1 a c * (if b = d then 1 else 0) + (if a = c then 1 else 0) * X1 b d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [Xsum, X1, idx]

theorem Ysum_eq (a b c d : Fin 2) :
    Ysum (idx a b) (idx c d) = Y1 a c * (if b = d then 1 else 0) + (if a = c then 1 else 0) * Y1 b d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [Ysum, Y1, idx]

theorem Zsum_eq (a b c d : Fin 2) :
    Zsum (idx a b) (idx c d) = Z1 a c * (if b = d then 1 else 0) + (if a = c then 1 else 0) * Z1 b d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [Zsum, Z1, idx] <;> norm_num

theorem XXYY_s : XXYY *ᵥ s = (-2 : ℂ) • s := by
  ext i; fin_cases i <;> simp [XXYY, s, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem Xsum_s : Xsum *ᵥ s = 0 := by
  ext i; fin_cases i <;> simp [Xsum, s, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem Ysum_s : Ysum *ᵥ s = 0 := by
  ext i; fin_cases i <;> simp [Ysum, s, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem Zsum_s : Zsum *ᵥ s = 0 := by
  ext i; fin_cases i <;> simp [Zsum, s, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

end ReservoirSinglet
