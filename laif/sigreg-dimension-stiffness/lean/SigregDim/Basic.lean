import Mathlib

/-!
# Sliced regularizers on normal embeddings: setting and slice moments

A sliced regularizer with slice function `h` evaluates, for an embedding law `N(0, Σ)` on `ℝ^K`, the
quantity `E_a h(aᵀ Σ a)` over a random unit direction `a`. It depends on `Σ` only through the
spectrum `λ`, and equals `E h(X_λ)` with `X_λ = ∑ₖ λₖ aₖ²`.

The direction law enters only through the properties collected in `SphereLike`: support on the unit
sphere, the second and fourth moments of the uniform law on the sphere, and invariance under
transpositions of coordinates.
-/

open MeasureTheory Finset

namespace SigregDim

variable {K : ℕ}

/-- The slice variance `X_λ(a) = ∑ₖ λₖ aₖ²`. -/
def sliceVar (lam : Fin K → ℝ) (x : Fin K → ℝ) : ℝ := ∑ k, lam k * x k ^ 2

/-- Population value of the sliced regularizer with slice function `h` at spectrum `λ`. -/
noncomputable def sliced (ν : Measure (Fin K → ℝ)) (h : ℝ → ℝ) (lam : Fin K → ℝ) : ℝ :=
  ∫ x, h (sliceVar lam x) ∂ν

/-- Properties of the uniform law on the unit sphere of `ℝ^K`: support on the sphere, the moments
`E aₖ² = 1/K`, `E aₖ⁴ = 3/(K(K+2))`, `E aₖ² aₗ² = 1/(K(K+2))` for `k ≠ l`, and invariance under
every transposition of coordinates. -/
structure SphereLike (K : ℕ) (ν : Measure (Fin K → ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  sphere : ∀ᵐ x ∂ν, ∑ k, x k ^ 2 = 1
  m2 : ∀ k, ∫ x, x k ^ 2 ∂ν = 1 / K
  m4 : ∀ k, ∫ x, x k ^ 4 ∂ν = 3 / (K * (K + 2))
  m22 : ∀ k l, k ≠ l → ∫ x, x k ^ 2 * x l ^ 2 ∂ν = 1 / (K * (K + 2))
  swap : ∀ i j : Fin K, ν.map (fun x => x ∘ Equiv.swap i j) = ν

variable {ν : Measure (Fin K → ℝ)}

lemma measurable_sliceVar (lam : Fin K → ℝ) : Measurable (sliceVar lam) := by
  unfold sliceVar
  fun_prop

lemma sq_le_one_ae (hν : SphereLike K ν) : ∀ᵐ x ∂ν, ∀ k, x k ^ 2 ≤ 1 := by
  filter_upwards [hν.sphere] with x hx k
  rw [← hx]
  exact Finset.single_le_sum (f := fun k => x k ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)

lemma integrable_of_bdd (hν : SphereLike K ν) {f : (Fin K → ℝ) → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ᵐ x ∂ν, |f x| ≤ C) : Integrable f ν := by
  have := hν.prob
  exact Integrable.of_bound hf.aestronglyMeasurable C (by simpa [Real.norm_eq_abs] using hC)

lemma sliceVar_nonneg {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) (x : Fin K → ℝ) :
    0 ≤ sliceVar lam x :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hlam k) (sq_nonneg _)

/-- On the sphere, `X_λ` lies between the smallest and the largest entry of `λ`. -/
lemma sliceVar_mem_ae (hν : SphereLike K ν) {lam : Fin K → ℝ} {lo hi : ℝ}
    (hlo : ∀ k, lo ≤ lam k) (hhi : ∀ k, lam k ≤ hi) :
    ∀ᵐ x ∂ν, lo ≤ sliceVar lam x ∧ sliceVar lam x ≤ hi := by
  filter_upwards [hν.sphere] with x hx
  constructor
  · calc lo = ∑ k, lo * x k ^ 2 := by rw [← Finset.mul_sum, hx, mul_one]
      _ ≤ sliceVar lam x :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hlo k) (sq_nonneg _)
  · calc sliceVar lam x ≤ ∑ k, hi * x k ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hhi k) (sq_nonneg _)
      _ = hi := by rw [← Finset.mul_sum, hx, mul_one]

lemma abs_sliceVar_le_ae (hν : SphereLike K ν) (lam : Fin K → ℝ) :
    ∀ᵐ x ∂ν, |sliceVar lam x| ≤ ∑ k, |lam k| := by
  filter_upwards [sq_le_one_ae hν] with x hx
  unfold sliceVar
  calc |∑ k, lam k * x k ^ 2| ≤ ∑ k, |lam k * x k ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |lam k| := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (x k))]
        exact mul_le_of_le_one_right (abs_nonneg _) (hx k)

lemma integrable_sq (hν : SphereLike K ν) (k : Fin K) : Integrable (fun x => x k ^ 2) ν :=
  integrable_of_bdd hν (by fun_prop) 1 (by
    filter_upwards [sq_le_one_ae hν] with x hx
    rw [abs_of_nonneg (sq_nonneg _)]; exact hx k)

lemma integrable_sq_mul_sq (hν : SphereLike K ν) (k l : Fin K) :
    Integrable (fun x => x k ^ 2 * x l ^ 2) ν :=
  integrable_of_bdd hν (by fun_prop) 1 (by
    filter_upwards [sq_le_one_ae hν] with x hx
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_one₀ (hx k) (sq_nonneg _) (hx l))

lemma integrable_sliceVar (hν : SphereLike K ν) (lam : Fin K → ℝ) :
    Integrable (sliceVar lam) ν :=
  integrable_of_bdd hν (measurable_sliceVar lam) _ (abs_sliceVar_le_ae hν lam)

lemma integrable_sliceVar_sq (hν : SphereLike K ν) (lam : Fin K → ℝ) :
    Integrable (fun x => sliceVar lam x ^ 2) ν :=
  integrable_of_bdd hν ((measurable_sliceVar lam).pow_const 2) ((∑ k, |lam k|) ^ 2) (by
    filter_upwards [abs_sliceVar_le_ae hν lam] with x hx
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2)

/-- First moment of the slice variance: `E X_λ = (∑ₖ λₖ)/K`. -/
theorem integral_sliceVar (hν : SphereLike K ν) (lam : Fin K → ℝ) :
    ∫ x, sliceVar lam x ∂ν = (∑ k, lam k) / K := by
  unfold sliceVar
  rw [integral_finsetSum _ (fun k _ => (integrable_sq hν k).const_mul (lam k))]
  simp_rw [integral_const_mul, hν.m2]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Mixed fourth moments in one formula: `E aₖ² aₗ² = (1 + 2·[k = l])/(K(K+2))`. -/
lemma integral_sq_mul_sq (hν : SphereLike K ν) (k l : Fin K) :
    ∫ x, x k ^ 2 * x l ^ 2 ∂ν =
      (1 + 2 * (if k = l then (1 : ℝ) else 0)) / (K * (K + 2)) := by
  by_cases hkl : k = l
  · subst hkl
    have : (fun x : Fin K → ℝ => x k ^ 2 * x k ^ 2) = fun x => x k ^ 4 := by
      funext x; ring
    rw [this, hν.m4]; norm_num
  · rw [hν.m22 k l hkl]; simp [hkl]

/-- Second moment of the slice variance:
`E X_λ² = ((∑ₖ λₖ)² + 2 ∑ₖ λₖ²)/(K(K+2))`. -/
theorem integral_sliceVar_sq (hν : SphereLike K ν) (lam : Fin K → ℝ) :
    ∫ x, sliceVar lam x ^ 2 ∂ν =
      ((∑ k, lam k) ^ 2 + 2 * ∑ k, lam k ^ 2) / (K * (K + 2)) := by
  have expand : ∀ x, sliceVar lam x ^ 2 =
      ∑ k, ∑ l, lam k * lam l * (x k ^ 2 * x l ^ 2) := by
    intro x
    unfold sliceVar
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _
    (fun l _ => (integrable_sq_mul_sq hν k l).const_mul _))]
  simp_rw [integral_finsetSum _ (fun l _ => (integrable_sq_mul_sq hν _ l).const_mul _)]
  simp_rw [integral_const_mul, integral_sq_mul_sq hν]
  have hsplit : ∀ k l : Fin K, lam k * lam l * ((1 + 2 * (if k = l then (1 : ℝ) else 0)) /
      (K * (K + 2))) = (lam k * lam l + 2 * (if k = l then lam k ^ 2 else 0)) / (K * (K + 2)) := by
    intro k l
    by_cases h : k = l
    · subst h; simp; ring
    · simp only [h, if_false]; ring
  simp_rw [hsplit, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sq (∑ k, lam k), Finset.sum_mul_sum]
  simp only [Finset.mul_sum]

/-- Variance of the slice variance: `Var X_λ = 2 v/(K+2)` with `v` the variance of the spectrum. -/
theorem variance_sliceVar (hν : SphereLike K ν) (hK : 0 < K) (lam : Fin K → ℝ) :
    ∫ x, sliceVar lam x ^ 2 ∂ν - (∫ x, sliceVar lam x ∂ν) ^ 2 =
      2 * ((∑ k, lam k ^ 2) / K - ((∑ k, lam k) / K) ^ 2) / (K + 2) := by
  rw [integral_sliceVar_sq hν, integral_sliceVar hν]
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hK2 : (K : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

end SigregDim
