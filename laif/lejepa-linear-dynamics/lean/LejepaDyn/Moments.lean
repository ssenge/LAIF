import Mathlib

/-!
# Second and fourth moments of a direction law on the sphere

The hypothesis `Iso4` records the moments of the uniform law on the unit sphere of `ℝ^K` up to order four, in
the form `E (uᵀa)² = ‖u‖² / K` and `E (uᵀa)² (vᵀa)² = (‖u‖² ‖v‖² + 2 (uᵀv)²) / (K (K + 2))` for all `u, v`.
-/

open MeasureTheory Finset

namespace LejepaDyn

variable {K : ℕ}

/-- Inner product on `ℝ^K`. -/
noncomputable def dot (u a : Fin K → ℝ) : ℝ := ∑ j, u j * a j

/-- Squared norm on `ℝ^K`. -/
noncomputable def nsq (u : Fin K → ℝ) : ℝ := ∑ j, u j ^ 2

/-- Moments of the uniform law on the unit sphere of `ℝ^K`, up to order four (classical). -/
structure Iso4 (K : ℕ) (ν : Measure (Fin K → ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  sphere : ∀ᵐ a ∂ν, nsq a = 1
  m2 : ∀ u, ∫ a, dot u a ^ 2 ∂ν = nsq u / K
  m4 : ∀ u v, ∫ a, dot u a ^ 2 * dot v a ^ 2 ∂ν = (nsq u * nsq v + 2 * dot u v ^ 2) / (K * (K + 2))

lemma nsq_nonneg (u : Fin K → ℝ) : 0 ≤ nsq u := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Inner-product inequality: `(uᵀa)² ≤ ‖u‖² ‖a‖²`. -/
lemma dot_sq_le (u a : Fin K → ℝ) : dot u a ^ 2 ≤ nsq u * nsq a :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma integrable_of_sphere {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) {f : (Fin K → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f ν) (C : ℝ) (hC : ∀ a, nsq a = 1 → |f a| ≤ C) : Integrable f ν := by
  have := h.prob
  exact Integrable.of_bound hf C (h.sphere.mono fun a ha => by rw [Real.norm_eq_abs]; exact hC a ha)

lemma continuous_dot (u : Fin K → ℝ) : Continuous (fun a : Fin K → ℝ => dot u a) := by
  unfold dot; fun_prop

lemma integrable_dot_sq {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (u : Fin K → ℝ) :
    Integrable (fun a => dot u a ^ 2) ν :=
  integrable_of_sphere h ((continuous_dot u).pow 2).aestronglyMeasurable (nsq u) fun a ha => by
    rw [abs_of_nonneg (sq_nonneg _)]; simpa [ha] using dot_sq_le u a

lemma integrable_dot_sq_mul {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (u v : Fin K → ℝ) :
    Integrable (fun a => dot u a ^ 2 * dot v a ^ 2) ν :=
  integrable_of_sphere h (((continuous_dot u).pow 2).mul ((continuous_dot v).pow 2)).aestronglyMeasurable
    (nsq u * nsq v) fun a ha => by
      rw [abs_of_nonneg (by positivity)]
      have h1 := dot_sq_le u a; have h2 := dot_sq_le v a
      rw [ha, mul_one] at h1 h2
      exact mul_le_mul h1 h2 (sq_nonneg _) (nsq_nonneg u)

end LejepaDyn
