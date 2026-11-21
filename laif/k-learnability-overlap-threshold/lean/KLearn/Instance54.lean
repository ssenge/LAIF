import KLearn.Data54

/-!
# Five states with overlaps at most 0.612528754 that are not 4-learnable

The witness `Y` is 4-locally positive semidefinite: for each `j`, the matrix `Y` with row and
column `j` removed equals `L j * diagonal (d j) * (L j)ᴴ` with `d j ≥ 0`, checked entrywise in exact
rational arithmetic. `Re Tr(Y G) < 0` for the Gram matrix `G` of `psi`, so `psi` is not 4-learnable.
After normalization the five states have all pairwise overlaps at most `t0 = 0.612528754`.
-/

open Matrix Complex
open scoped ComplexOrder

namespace KLearn.Instance54

lemma fac0 : mask (Finset.univ.erase 0) Y = L0 * diagonal d0 * L0ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Fin.sum_univ_five]
  fin_cases a <;> fin_cases b <;> simp [mask, Y, L0, d0, Complex.ext_iff] <;> norm_num

lemma fac1 : mask (Finset.univ.erase 1) Y = L1 * diagonal d1 * L1ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Fin.sum_univ_five]
  fin_cases a <;> fin_cases b <;> simp [mask, Y, L1, d1, Complex.ext_iff] <;> norm_num

lemma fac2 : mask (Finset.univ.erase 2) Y = L2 * diagonal d2 * L2ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Fin.sum_univ_five]
  fin_cases a <;> fin_cases b <;> simp [mask, Y, L2, d2, Complex.ext_iff] <;> norm_num

lemma fac3 : mask (Finset.univ.erase 3) Y = L3 * diagonal d3 * L3ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Fin.sum_univ_five]
  fin_cases a <;> fin_cases b <;> simp [mask, Y, L3, d3, Complex.ext_iff] <;> norm_num

lemma fac4 : mask (Finset.univ.erase 4) Y = L4 * diagonal d4 * L4ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Fin.sum_univ_five]
  fin_cases a <;> fin_cases b <;> simp [mask, Y, L4, d4, Complex.ext_iff] <;> norm_num

lemma d0_nonneg : 0 ≤ d0 := by intro i; fin_cases i <;> simp [d0, Complex.le_def] <;> norm_num
lemma d1_nonneg : 0 ≤ d1 := by intro i; fin_cases i <;> simp [d1, Complex.le_def] <;> norm_num
lemma d2_nonneg : 0 ≤ d2 := by intro i; fin_cases i <;> simp [d2, Complex.le_def] <;> norm_num
lemma d3_nonneg : 0 ≤ d3 := by intro i; fin_cases i <;> simp [d3, Complex.le_def] <;> norm_num
lemma d4_nonneg : 0 ≤ d4 := by intro i; fin_cases i <;> simp [d4, Complex.le_def] <;> norm_num

theorem locallyPSD_Y : LocallyPSD 4 Y := by
  intro S hS
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra h
    simp only [not_exists, not_not] at h
    rw [Finset.eq_univ_iff_forall.mpr h] at hS
    simp at hS
  have hSe : S = Finset.univ.erase j := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact hj hx
    · simp [Finset.card_erase_of_mem, hS]
  subst hSe
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    fin_cases j <;> decide
  · rw [fac0]; exact (PosSemidef.diagonal d0_nonneg).mul_mul_conjTranspose_same L0
  · rw [fac1]; exact (PosSemidef.diagonal d1_nonneg).mul_mul_conjTranspose_same L1
  · rw [fac2]; exact (PosSemidef.diagonal d2_nonneg).mul_mul_conjTranspose_same L2
  · rw [fac3]; exact (PosSemidef.diagonal d3_nonneg).mul_mul_conjTranspose_same L3
  · rw [fac4]; exact (PosSemidef.diagonal d4_nonneg).mul_mul_conjTranspose_same L4

theorem trace_neg : (Y * gramMat psi).trace.re < 0 := by
  simp only [trace, diag, Matrix.mul_apply, Fin.sum_univ_five]
  simp [gramMat, dotProduct, Fin.sum_univ_three, Y, psi]
  norm_num

theorem not_kLearnable_psi : ¬ KLearnable 4 psi := not_kLearnable locallyPSD_Y trace_neg

theorem gram_diag_im (i : Fin 5) : (gramMat psi i i).im = 0 := by
  fin_cases i <;> simp [gramMat, dotProduct, Fin.sum_univ_three, psi] <;> ring

theorem gram_diag_pos (i : Fin 5) : 0 < (gramMat psi i i).re := by
  fin_cases i <;> simp [gramMat, dotProduct, Fin.sum_univ_three, psi] <;> norm_num

theorem overlap (i j : Fin 5) (h : i ≠ j) :
    Complex.normSq (gramMat psi i j) ≤ t0 ^ 2 * ((gramMat psi i i).re * (gramMat psi j j).re) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl h
    | (simp [gramMat, dotProduct, Fin.sum_univ_three, psi, t0, Complex.normSq_apply]; norm_num)

/-- Five unit vectors in `ℂ³` whose pairwise overlaps have modulus at most `t0 = 0.612528754` and
which are not 4-learnable (not antidistinguishable). -/
theorem main : ∃ φ : Fin 5 → Fin 3 → ℂ, (∀ i, gramMat φ i i = 1) ∧
    (∀ i j, i ≠ j → ‖gramMat φ i j‖ ≤ t0) ∧ ¬ KLearnable 4 φ :=
  exists_unit_not_kLearnable (by norm_num [t0]) gram_diag_pos gram_diag_im overlap not_kLearnable_psi

end KLearn.Instance54
