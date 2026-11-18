import LejepaDyn.Moments

/-!
# Bounds on the SIGReg gradient matrix

The embedding covariance is `M = Σᵣ bᵣ bᵣᵀ` with rows `bᵣ = B r ∈ ℝ^K` (for a linear encoder `W` and data
covariance `Σ`, `B = (W Σ^{1/2})ᵀ` column by column), so `aᵀ M a = Σᵣ (bᵣᵀ a)²` and `tr M = Σᵣ ‖bᵣ‖²`.
The SIGReg gradient matrix is `G = E h'(aᵀ M a) a aᵀ`, and `gq h' B v = vᵀ G v`.
-/

open MeasureTheory Finset

namespace LejepaDyn

variable {K d : ℕ}

/-- `aᵀ M a` for `M = Σᵣ bᵣ bᵣᵀ`. -/
noncomputable def qf (B : Fin d → Fin K → ℝ) (a : Fin K → ℝ) : ℝ := ∑ r, dot (B r) a ^ 2

/-- `tr M`. -/
noncomputable def trM (B : Fin d → Fin K → ℝ) : ℝ := ∑ r, nsq (B r)

/-- `vᵀ G v` with `G = E h'(aᵀ M a) a aᵀ`. -/
noncomputable def gq (ν : Measure (Fin K → ℝ)) (hp : ℝ → ℝ) (B : Fin d → Fin K → ℝ)
    (v : Fin K → ℝ) : ℝ :=
  ∫ a, hp (qf B a) * dot v a ^ 2 ∂ν

lemma qf_nonneg (B : Fin d → Fin K → ℝ) (a : Fin K → ℝ) : 0 ≤ qf B a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma qf_le (B : Fin d → Fin K → ℝ) {a : Fin K → ℝ} (ha : nsq a = 1) : qf B a ≤ trM B :=
  Finset.sum_le_sum fun r _ => by simpa [ha] using dot_sq_le (B r) a

lemma continuous_qf (B : Fin d → Fin K → ℝ) : Continuous (qf B) := by
  unfold qf; exact continuous_finsetSum _ fun r _ => (continuous_dot (B r)).pow 2

lemma integrable_gq {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) {hp : ℝ → ℝ} (hm : Measurable hp)
    {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (B : Fin d → Fin K → ℝ) (v : Fin K → ℝ) :
    Integrable (fun a => hp (qf B a) * dot v a ^ 2) ν := by
  refine integrable_of_sphere h ((hm.comp_aemeasurable (continuous_qf B).aemeasurable).aestronglyMeasurable.mul
    ((continuous_dot v).pow 2).aestronglyMeasurable) (C * nsq v) fun a ha => ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg (dot v a))]
  have h1 := dot_sq_le v a
  rw [ha, mul_one] at h1
  exact mul_le_mul (hC _ (qf_nonneg B a)) h1 (sq_nonneg _) ((abs_nonneg _).trans (hC _ (qf_nonneg B a)))

/-- **Lower bound.** If `h' ≥ h'(0)` on `[0, ∞)`, then `vᵀ G v ≥ h'(0) ‖v‖² / K`. -/
theorem gq_ge {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) {hp : ℝ → ℝ} (hm : Measurable hp) {C : ℝ}
    (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {h0 : ℝ} (hlow : ∀ x, 0 ≤ x → h0 ≤ hp x)
    (B : Fin d → Fin K → ℝ) (v : Fin K → ℝ) :
    h0 * nsq v / K ≤ gq ν hp B v := by
  rw [mul_div_assoc, ← h.m2 v, ← integral_const_mul]
  exact integral_mono (((integrable_dot_sq h v)).const_mul _) (integrable_gq h hm hC B v) fun a =>
    mul_le_mul_of_nonneg_right (hlow _ (qf_nonneg B a)) (sq_nonneg _)

/-- `E (aᵀ M a) (vᵀ a)² = (tr M ‖v‖² + 2 Σᵣ (bᵣᵀ v)²) / (K (K + 2))`. -/
lemma integral_qf_mul {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (B : Fin d → Fin K → ℝ)
    (v : Fin K → ℝ) :
    ∫ a, qf B a * dot v a ^ 2 ∂ν = (trM B * nsq v + 2 * ∑ r, dot (B r) v ^ 2) / (K * (K + 2)) := by
  simp_rw [qf, Finset.sum_mul]
  rw [integral_finsetSum _ fun r _ => integrable_dot_sq_mul h (B r) v]
  simp_rw [h.m4, trM, ← Finset.sum_div, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **Upper bound.** If `h'(x) ≤ h'(0) + L₂ x` on `[0, ∞)`, then
`vᵀ G v ≤ h'(0) ‖v‖² / K + 3 L₂ tr M ‖v‖² / (K (K + 2))`. -/
theorem gq_le {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (hK : 0 < K) {hp : ℝ → ℝ} (hm : Measurable hp)
    {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {h0 L₂ : ℝ} (hL : 0 ≤ L₂)
    (hup : ∀ x, 0 ≤ x → hp x ≤ h0 + L₂ * x) (B : Fin d → Fin K → ℝ) (v : Fin K → ℝ) :
    gq ν hp B v ≤ h0 * nsq v / K + 3 * L₂ * trM B * nsq v / (K * (K + 2)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hden : (0 : ℝ) < K * (K + 2) := by positivity
  have I1 := integrable_dot_sq h v
  have I2 : Integrable (fun a => qf B a * dot v a ^ 2) ν := by
    simp_rw [qf, Finset.sum_mul]
    exact integrable_finsetSum _ fun r _ => integrable_dot_sq_mul h (B r) v
  calc gq ν hp B v ≤ ∫ a, (h0 * dot v a ^ 2 + L₂ * (qf B a * dot v a ^ 2)) ∂ν := by
        refine integral_mono (integrable_gq h hm hC B v) ((I1.const_mul _).add (I2.const_mul _)) fun a => ?_
        have := hup _ (qf_nonneg B a)
        nlinarith [sq_nonneg (dot v a)]
    _ = h0 * nsq v / K + L₂ * ((trM B * nsq v + 2 * ∑ r, dot (B r) v ^ 2) / (K * (K + 2))) := by
        rw [integral_add (I1.const_mul _) (I2.const_mul _), integral_const_mul, integral_const_mul,
          h.m2, integral_qf_mul h]
        ring
    _ ≤ h0 * nsq v / K + 3 * L₂ * trM B * nsq v / (K * (K + 2)) := by
        have hcs : ∑ r, dot (B r) v ^ 2 ≤ trM B * nsq v := by
          rw [trM, Finset.sum_mul]; exact Finset.sum_le_sum fun r _ => dot_sq_le (B r) v
        have : L₂ * ((trM B * nsq v + 2 * ∑ r, dot (B r) v ^ 2) / (K * (K + 2))) ≤
            3 * L₂ * trM B * nsq v / (K * (K + 2)) := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hden]; nlinarith
        linarith

end LejepaDyn
