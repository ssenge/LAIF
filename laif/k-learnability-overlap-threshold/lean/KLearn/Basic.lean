import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# k-learnability of pure states and incoherence witnesses

A multiset of vectors `ψ : Fin n → Fin d → ℂ` is k-learnable if a POVM `{M I}`, indexed by the
subsets `I` of size `k`, never shows a subset that misses the true index:
`⟨ψ i| M I |ψ i⟩ = 0` for `i ∉ I`.

If every `k × k` principal submatrix of `Y` is positive semidefinite and `ψ` is k-learnable, then
`0 ≤ Tr(Y G)` for the Gram matrix `G`. So a witness with `Re Tr(Y G) < 0` shows that `ψ` is not
k-learnable.
-/

open Matrix
open scoped ComplexOrder

namespace KLearn

variable {n d : ℕ}

/-- The Gram matrix, with entries `⟨ψ i | ψ j⟩`. -/
def gramMat (ψ : Fin n → Fin d → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => star (ψ i) ⬝ᵥ ψ j

/-- k-learnability: a POVM indexed by the subsets of size `k` whose outcome always contains the
index of the state. -/
def KLearnable (k : ℕ) (ψ : Fin n → Fin d → ℂ) : Prop :=
  ∃ M : Finset (Fin n) → Matrix (Fin d) (Fin d) ℂ,
    (∀ I, (M I).PosSemidef) ∧ (∀ I, I.card ≠ k → M I = 0) ∧ (∑ I, M I = 1) ∧
    ∀ I i, i ∉ I → star (ψ i) ⬝ᵥ (M I *ᵥ ψ i) = 0

/-- The matrix `Y` with all entries outside `S × S` set to zero. -/
def mask (S : Finset (Fin n)) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ S ∧ b ∈ S then Y a b else 0

/-- Every `k × k` principal submatrix of `Y` is positive semidefinite. -/
def LocallyPSD (k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → (mask S Y).PosSemidef

/-- The columns of `colMat ψ` are the vectors `ψ i`. -/
def colMat (ψ : Fin n → Fin d → ℂ) : Matrix (Fin d) (Fin n) ℂ := Matrix.of fun c i => ψ i c

lemma conj_mul_mul_apply (ψ : Fin n → Fin d → ℂ) (M : Matrix (Fin d) (Fin d) ℂ) (a b : Fin n) :
    ((colMat ψ)ᴴ * M * colMat ψ) a b = star (ψ a) ⬝ᵥ (M *ᵥ ψ b) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, colMat, of_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma gram_eq (ψ : Fin n → Fin d → ℂ) :
    gramMat ψ = (colMat ψ)ᴴ * (1 : Matrix (Fin d) (Fin d) ℂ) * colMat ψ := by
  ext a b
  rw [conj_mul_mul_apply, one_mulVec]
  rfl

/-- For positive semidefinite `A` and `H`, `0 ≤ Tr(A H)`, since the entrywise product of positive
semidefinite matrices is positive semidefinite. -/
lemma trace_mul_nonneg {A H : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  have h := (hA.hadamard hH.transpose).dotProduct_mulVec_nonneg (fun _ => 1)
  convert h using 1
  simp [trace, Matrix.mul_apply, dotProduct, mulVec, hadamard, transpose_apply]

/-- Soundness of the witness: if `ψ` is k-learnable and `Y` is k-locally positive semidefinite,
then `0 ≤ Tr(Y G)`. -/
theorem trace_nonneg_of_kLearnable {k : ℕ} {ψ : Fin n → Fin d → ℂ}
    {Y : Matrix (Fin n) (Fin n) ℂ} (hL : KLearnable k ψ) (hY : LocallyPSD k Y) :
    0 ≤ (Y * gramMat ψ).trace := by
  obtain ⟨M, hM, hcard, hsum, hzero⟩ := hL
  rw [gram_eq, ← hsum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun I _ => ?_
  by_cases hI : I.card = k
  · set H := (colMat ψ)ᴴ * M I * colMat ψ with hHdef
    have hH : H.PosSemidef := (hM I).conjTranspose_mul_mul_same _
    have hkill : ∀ i, i ∉ I → M I *ᵥ ψ i = 0 := fun i hi =>
      ((hM I).dotProduct_mulVec_zero_iff).mp (hzero I i hi)
    have hcol : ∀ a b, b ∉ I → H a b = 0 := fun a b hb => by
      rw [hHdef, conj_mul_mul_apply, hkill b hb, dotProduct_zero]
    have hrow : ∀ a b, a ∉ I → H a b = 0 := fun a b ha => by
      rw [← hH.isHermitian.apply a b, hcol b a ha, star_zero]
    have heq : (Y * H).trace = (mask I Y * H).trace := by
      simp only [trace, diag, Matrix.mul_apply, mask]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases ha : a ∈ I
      · by_cases hb : b ∈ I
        · simp [ha, hb]
        · simp [hrow b a hb]
      · simp [ha, hcol b a ha]
    rw [heq]
    exact trace_mul_nonneg (hY I hI) hH
  · simp [hcard I hI]

/-- A witness with `Re Tr(Y G) < 0` shows that `ψ` is not k-learnable. -/
theorem not_kLearnable {k : ℕ} {ψ : Fin n → Fin d → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : LocallyPSD k Y) (htr : (Y * gramMat ψ).trace.re < 0) : ¬ KLearnable k ψ := fun hL =>
  absurd (Complex.nonneg_iff.mp (trace_nonneg_of_kLearnable hL hY)).1 (not_le.mpr htr)

/-- k-learnability does not depend on the normalization of the vectors. -/
theorem kLearnable_of_smul {k : ℕ} {ψ : Fin n → Fin d → ℂ} (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (h : KLearnable k fun i => c i • ψ i) : KLearnable k ψ := by
  obtain ⟨M, hM, hcard, hsum, hzero⟩ := h
  refine ⟨M, hM, hcard, hsum, fun I i hi => ?_⟩
  have h0 := hzero I i hi
  simp only [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h0
  simpa [hc i] using h0

lemma gram_smul (ψ : Fin n → Fin d → ℂ) (c : Fin n → ℝ) (i j : Fin n) :
    gramMat (fun i => (c i : ℂ) • ψ i) i j = ((c i * c j : ℝ) : ℂ) * gramMat ψ i j := by
  simp only [gramMat, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]
  push_cast
  ring

/-- Normalization: if the Gram matrix of `ψ` has positive real diagonal, normalized overlaps at most
`t`, and `ψ` is not k-learnable, then there are unit vectors with overlaps of modulus at most `t`
that are not k-learnable. -/
theorem exists_unit_not_kLearnable {k : ℕ} {ψ : Fin n → Fin d → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ i, 0 < (gramMat ψ i i).re) (him : ∀ i, (gramMat ψ i i).im = 0)
    (hov : ∀ i j, i ≠ j → Complex.normSq (gramMat ψ i j) ≤ t ^ 2 * ((gramMat ψ i i).re * (gramMat ψ j j).re))
    (hnot : ¬ KLearnable k ψ) :
    ∃ φ : Fin n → Fin d → ℂ, (∀ i, gramMat φ i i = 1) ∧ (∀ i j, i ≠ j → ‖gramMat φ i j‖ ≤ t) ∧
      ¬ KLearnable k φ := by
  set s : Fin n → ℝ := fun i => Real.sqrt (gramMat ψ i i).re with hs
  have spos : ∀ i, 0 < s i := fun i => Real.sqrt_pos.mpr (hpos i)
  have ssq : ∀ i, s i * s i = (gramMat ψ i i).re := fun i => Real.mul_self_sqrt (hpos i).le
  have hdiag : ∀ i, gramMat ψ i i = ((gramMat ψ i i).re : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [him i])
  refine ⟨fun i => (((s i)⁻¹ : ℝ) : ℂ) • ψ i, fun i => ?_, fun i j hij => ?_, fun hL => ?_⟩
  · rw [gram_smul, hdiag i, ← Complex.ofReal_mul, ← ssq i]
    have := (spos i).ne'
    rw [Complex.ofReal_eq_one]
    field_simp
  · have key : ‖gramMat ψ i j‖ ≤ t * (s i * s j) := by
      have h1 : ‖gramMat ψ i j‖ ^ 2 ≤ (t * (s i * s j)) ^ 2 := by
        rw [Complex.sq_norm]
        have : (t * (s i * s j)) ^ 2 = t ^ 2 * ((s i * s i) * (s j * s j)) := by ring
        rw [this, ssq, ssq]
        exact hov i j hij
      have h2 : 0 ≤ t * (s i * s j) := mul_nonneg ht (mul_nonneg (spos i).le (spos j).le)
      nlinarith [norm_nonneg (gramMat ψ i j)]
    rw [gram_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr (spos i)) (inv_pos.mpr (spos j)))]
    calc (s i)⁻¹ * (s j)⁻¹ * ‖gramMat ψ i j‖ ≤ (s i)⁻¹ * (s j)⁻¹ * (t * (s i * s j)) := by
          gcongr
      _ = t := by
          have := (spos i).ne'; have := (spos j).ne'
          field_simp
  · exact hnot (kLearnable_of_smul (fun i => (((s i)⁻¹ : ℝ) : ℂ))
      (fun i => Complex.ofReal_ne_zero.mpr (inv_ne_zero (spos i).ne')) hL)

end KLearn
