import LejepaDyn.Gram
import LejepaDyn.Growth
import SigregDim.SliceD

/-!
# Feature growth under the gradient flow of linear LeJEPA

Commuting case: the data covariance `Σ` and the covariance `Δ` of the difference of two views share an eigenbasis,
`Σ eᵢ = σ eᵢ` and `Δ eᵢ = δ eᵢ` for the feature `i` considered. Along the gradient flow
`Ẇ = -2 W Δ - 2 μ G(M) W Σ`, the column `v = W eᵢ` and the learned variance `n = σ ‖v‖²` satisfy
`ṅ = -4 δ n - 4 μ σ² vᵀ G v`; this identity is the hypothesis `hode` below (proved in `LejepaDyn.Flow`).
With `κ = -μ h'(0) / K` and the
invariance cost `c = δ / σ`, the rate of feature `i` is `4 σ (κ - c)`:

* `never_learned`: `n(t) ≤ n(0) e^{4 (σ κ - δ) t}` for all `t ≥ 0`, so features with `c ≥ κ` never grow.
* `early_phase`: while `tr M ≤ ε`, `n(t) ≥ n(0) e^{4 (σ κ - δ - 3 μ σ L₂ ε / (K (K + 2))) t}`.
-/

open MeasureTheory Set Real

namespace LejepaDyn

variable {K d : ℕ}

/-- **Features above the threshold are never learned.** -/
theorem never_learned {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (hK : 0 < K) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C)
    (hlow : ∀ x, 0 ≤ x → hp 0 ≤ hp x) {σ δ μ T : ℝ} (hμ : 0 ≤ μ)
    {n : ℝ → ℝ} {v : ℝ → Fin K → ℝ} {B : ℝ → Fin d → Fin K → ℝ}
    (hn : ∀ t, n t = σ * nsq (v t))
    (hode : ∀ t, HasDerivAt n (-4 * δ * n t - 4 * μ * σ ^ 2 * gq ν hp (B t) (v t)) t) :
    ∀ t ∈ Icc 0 T, n t ≤ n 0 * exp (4 * (σ * (-(μ * hp 0) / K) - δ) * t) := by
  refine growth_le hode fun t _ => ?_
  have hg := gq_ge h hm hC hlow (B t) (v t)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hmσ : 0 ≤ μ * σ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hg hmσ
  rw [hn t]
  have e : μ * σ ^ 2 * (hp 0 * nsq (v t) / K) = σ * (μ * hp 0 / K) * (σ * nsq (v t)) := by
    field_simp
  rw [e] at this
  have e2 : 4 * (σ * (-(μ * hp 0) / K) - δ) * (σ * nsq (v t)) =
      -4 * δ * (σ * nsq (v t)) - 4 * (σ * (μ * hp 0 / K) * (σ * nsq (v t))) := by ring
  rw [e2]
  linarith

/-- **Early phase.** While `tr M ≤ ε`, feature `i` grows at least at rate `4 (σ κ - δ - 3 μ σ L₂ ε / (K (K + 2)))`. -/
theorem early_phase {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (hK : 0 < K) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {L₂ : ℝ} (hL : 0 ≤ L₂)
    (hup : ∀ x, 0 ≤ x → hp x ≤ hp 0 + L₂ * x) {σ δ μ ε T : ℝ} (hμ : 0 ≤ μ)
    {n : ℝ → ℝ} {v : ℝ → Fin K → ℝ} {B : ℝ → Fin d → Fin K → ℝ}
    (hn : ∀ t, n t = σ * nsq (v t))
    (hode : ∀ t, HasDerivAt n (-4 * δ * n t - 4 * μ * σ ^ 2 * gq ν hp (B t) (v t)) t)
    (hsmall : ∀ t ∈ Icc 0 T, trM (B t) ≤ ε) :
    ∀ t ∈ Icc 0 T, n 0 * exp (4 * (σ * (-(μ * hp 0) / K) - δ -
      3 * μ * σ * L₂ * ε / (K * (K + 2))) * t) ≤ n t := by
  refine growth_ge hode fun t ht => ?_
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hden : (0 : ℝ) < K * (K + 2) := by positivity
  have hg := gq_le h hK hm hC hL hup (B t) (v t)
  have hnv := nsq_nonneg (v t)
  have htr : 3 * L₂ * trM (B t) * nsq (v t) / (K * (K + 2)) ≤ 3 * L₂ * ε * nsq (v t) / (K * (K + 2)) := by
    gcongr; exact hsmall t ht
  have hmσ : 0 ≤ μ * σ ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left (hg.trans (add_le_add le_rfl htr)) hmσ
  rw [hn t]
  have e1 : μ * σ ^ 2 * (hp 0 * nsq (v t) / K + 3 * L₂ * ε * nsq (v t) / (K * (K + 2))) =
      (σ * (μ * hp 0 / K) + 3 * μ * σ * L₂ * ε / (K * (K + 2))) * (σ * nsq (v t)) := by
    field_simp
  rw [e1] at h2
  have e2 : 4 * (σ * (-(μ * hp 0) / K) - δ - 3 * μ * σ * L₂ * ε / (K * (K + 2))) * (σ * nsq (v t)) =
      -4 * δ * (σ * nsq (v t)) - 4 * ((σ * (μ * hp 0 / K) + 3 * μ * σ * L₂ * ε / (K * (K + 2))) *
        (σ * nsq (v t))) := by
    ring
  rw [e2]
  linarith

/-! ## The SIGReg slice function -/

open SigregDim in
/-- `D'(s) ≥ D'(0)` on `[0, ∞)`: with `x = (2s+1)^{-3/2}`, `(s+2)^{-3/2} ≥ 2^{-3/2} x`. -/
theorem epD'_ge {s : ℝ} (hs : 0 ≤ s) : epD' 0 ≤ epD' s := by
  unfold epD'
  have hp := Real.sqrt_nonneg (2 * π)
  refine mul_le_mul_of_nonneg_left ?_ hp
  have h1 : (s + 2) ^ (-(3 / 2 : ℝ)) ≥ (2 * (2 * s + 1)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have hx : (2 * s + 1) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hx0 : 0 ≤ (2 * s + 1) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have h2 : (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h20 : 0 ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  norm_num at *
  nlinarith [mul_le_mul_of_nonneg_left hx h20]

open SigregDim in
lemma epD'_le_lin {s : ℝ} (hs : 0 ≤ s) : epD' s ≤ epD' 0 + 8 * s := by
  have := epD'_lip hs le_rfl
  rw [sub_zero, abs_of_nonneg hs] at this
  linarith [le_abs_self (epD' s - epD' 0)]

open SigregDim in
lemma measurable_epD' : Measurable epD' := by
  unfold epD'; fun_prop

open SigregDim in
/-- `never_learned` for the SIGReg slice function `D`. -/
theorem never_learned_D {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (hK : 0 < K) {σ δ μ T : ℝ}
    (hμ : 0 ≤ μ) {n : ℝ → ℝ} {v : ℝ → Fin K → ℝ} {B : ℝ → Fin d → Fin K → ℝ}
    (hn : ∀ t, n t = σ * nsq (v t))
    (hode : ∀ t, HasDerivAt n (-4 * δ * n t - 4 * μ * σ ^ 2 * gq ν epD' (B t) (v t)) t) :
    ∀ t ∈ Icc 0 T, n t ≤ n 0 * exp (4 * (σ * (-(μ * epD' 0) / K) - δ) * t) :=
  never_learned h hK measurable_epD' (fun _ hx => abs_epD'_le hx) (fun _ hx => epD'_ge hx) hμ hn hode

open SigregDim in
/-- `early_phase` for the SIGReg slice function `D`, with `L₂ = 8`. -/
theorem early_phase_D {ν : Measure (Fin K → ℝ)} (h : Iso4 K ν) (hK : 0 < K) {σ δ μ ε T : ℝ}
    (hμ : 0 ≤ μ) {n : ℝ → ℝ} {v : ℝ → Fin K → ℝ} {B : ℝ → Fin d → Fin K → ℝ}
    (hn : ∀ t, n t = σ * nsq (v t))
    (hode : ∀ t, HasDerivAt n (-4 * δ * n t - 4 * μ * σ ^ 2 * gq ν epD' (B t) (v t)) t)
    (hsmall : ∀ t ∈ Icc 0 T, trM (B t) ≤ ε) :
    ∀ t ∈ Icc 0 T, n 0 * exp (4 * (σ * (-(μ * epD' 0) / K) - δ -
      3 * μ * σ * 8 * ε / (K * (K + 2))) * t) ≤ n t :=
  early_phase h hK measurable_epD' (fun _ hx => abs_epD'_le hx) (by norm_num)
    (fun _ hx => epD'_le_lin hx) hμ hn hode hsmall

end LejepaDyn
