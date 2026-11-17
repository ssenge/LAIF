import SigregDim.Kernel

/-!
# The cross-polytope is an isotropic finite law

The `2K` points `±√K eᵢ` with equal weights satisfy `IsoAtoms`, so the hypotheses of `energy_near`,
`sigreg_energy_near` and `unif_energy_near` are met by a law with `2K` atoms in every dimension `K ≥ 1`.
-/

open Finset Real

namespace SigregDim

/-- The vertices `√K eₖ` followed by `-√K eₖ`. -/
noncomputable def cross (K : ℕ) : Fin (K + K) → Fin K → ℝ :=
  Fin.append (fun k i => if k = i then √(K : ℝ) else 0) (fun k i => if k = i then -√(K : ℝ) else 0)

@[simp] lemma cross_castAdd {K : ℕ} (k : Fin K) :
    cross K (Fin.castAdd K k) = fun i => if k = i then √(K : ℝ) else 0 := by
  simp [cross, Fin.append_left]

@[simp] lemma cross_addNat {K : ℕ} (k : Fin K) :
    cross K (k.addNat K) = fun i => if k = i then -√(K : ℝ) else 0 := by
  have : k.addNat K = Fin.natAdd K k := Fin.ext (by simp [Nat.add_comm])
  rw [this, cross, Fin.append_right]

theorem isoAtoms_cross {K : ℕ} (hK : 0 < K) :
    IsoAtoms K (K + K) (cross K) (fun _ => 1 / (2 * K)) where
  nonneg _ := by positivity
  sum_one := by
    have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add]
    field_simp; ring
  sphere j := by
    have hs : √(K : ℝ) ^ 2 = K := Real.sq_sqrt (Nat.cast_nonneg K)
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp [ite_pow, hs]
  mean i := by
    rw [Fin.sum_univ_add]
    simp [mul_ite]
  cov i l := by
    have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hs : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt (Nat.cast_nonneg K)
    rw [Fin.sum_univ_add]
    by_cases hil : i = l
    · subst hil
      simp [mul_ite, ite_mul, hs]
      field_simp; ring
    · simp [mul_ite, ite_mul, hil]
      split_ifs with h; exacts [absurd h.symm hil, by ring]

end SigregDim
