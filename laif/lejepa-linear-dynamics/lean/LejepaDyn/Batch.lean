import LejepaDyn.Flow

/-!
# Linear LeJEPA with the minibatch statistic

The statistic of LeJEPA is `N` times the squared distance of the empirical characteristic function of a batch of
`N` samples to the normal one. For a normal slice of variance `s`, its expectation is `N D(s) + B(s)` with the
null bias `B(s) = √(2π) (1 - (2s+1)^{-1/2})`. With `h_N = N D + B` as slice function:

* `loss_hN`: the loss is the loss with slice function `D` and weight `μ N`, plus `μ ∫ B`.
* `hN'_ge`, `hN'_le_lin`: `h_N'` satisfies the two conditions of the growth bounds for `N ≥ 2`, with `L₂ = 8 N`.
* `never_learned_flow_batch`, `early_phase_flow_batch`: Theorems 1 and 2 for the gradient flow of this loss, with
  the threshold `κ_N = -μ h_N'(0) / K = μ (N (1 - 2^{-3/2}) - 1) √(2π) / K` (`hN'_zero`).
-/

open MeasureTheory Set Real

namespace LejepaDyn

open SigregDim

variable {K d : ℕ}

/-- The null bias `B(s) = √(2π) (1 - (2s+1)^{-1/2})`. -/
noncomputable def epB (s : ℝ) : ℝ := √(2 * π) * (1 - (2 * s + 1) ^ (-(1 / 2 : ℝ)))

/-- Its derivative. -/
noncomputable def epB' (s : ℝ) : ℝ := √(2 * π) * (2 * s + 1) ^ (-(3 / 2 : ℝ))

/-- The slice function `N D + B` of the expected minibatch statistic. -/
noncomputable def hN (N s : ℝ) : ℝ := N * epD s + epB s

/-- Its derivative. -/
noncomputable def hN' (N s : ℝ) : ℝ := N * epD' s + epB' s

lemma hasDerivAt_epB {s : ℝ} (hs : 0 ≤ s) : HasDerivAt epB (epB' s) s := by
  have h1 := hasDerivAt_affine_rpow 2 1 (-(1 / 2)) s (by linarith)
  have := (h1.const_sub 1).const_mul √(2 * π)
  convert this using 1
  · funext x; simp [epB]
  · unfold epB'
    have e1 : (2 * s + 1) ^ (-(1 / 2 : ℝ) - 1) = (2 * s + 1) ^ (-(3 / 2 : ℝ)) := by norm_num
    rw [e1]; ring

lemma hasDerivAt_hN (N : ℝ) {s : ℝ} (hs : 0 ≤ s) : HasDerivAt (hN N) (hN' N s) s := by
  unfold hN hN'
  exact ((hasDerivAt_epD hs).const_mul N).add (hasDerivAt_epB hs)

lemma abs_epB_le {s : ℝ} (hs : 0 ≤ s) : |epB s| ≤ 3 := by
  obtain ⟨a0, a1⟩ := rpow_neg_mem (a := 2) (b := 1) (q := 1 / 2) (by norm_num) le_rfl (by norm_num) hs
  unfold epB
  rw [abs_mul, abs_of_nonneg sqrt_two_pi_nonneg]
  calc √(2 * π) * |1 - (2 * s + 1) ^ (-(1 / 2 : ℝ))| ≤ 2.51 * 1 :=
        mul_le_mul sqrt_two_pi_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) (by norm_num)
    _ ≤ 3 := by norm_num

lemma abs_epB'_le {s : ℝ} (hs : 0 ≤ s) : |epB' s| ≤ 3 := by
  obtain ⟨a0, a1⟩ := rpow_neg_mem (a := 2) (b := 1) (q := 3 / 2) (by norm_num) le_rfl (by norm_num) hs
  unfold epB'
  rw [abs_mul, abs_of_nonneg sqrt_two_pi_nonneg, abs_of_nonneg a0]
  calc √(2 * π) * (2 * s + 1) ^ (-(3 / 2 : ℝ)) ≤ 2.51 * 1 := mul_le_mul sqrt_two_pi_le a1 a0 (by norm_num)
    _ ≤ 3 := by norm_num

lemma abs_hN_le {N : ℝ} (hNn : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) : |hN N s| ≤ 11 * N + 3 := by
  unfold hN
  calc |N * epD s + epB s| ≤ |N * epD s| + |epB s| := abs_add_le _ _
    _ ≤ N * 11 + 3 := by
        rw [abs_mul, abs_of_nonneg hNn]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_epD_le hs) hNn) (abs_epB_le hs)
    _ = 11 * N + 3 := by ring

lemma abs_hN'_le {N : ℝ} (hNn : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) : |hN' N s| ≤ 3 * N + 3 := by
  unfold hN'
  calc |N * epD' s + epB' s| ≤ |N * epD' s| + |epB' s| := abs_add_le _ _
    _ ≤ N * 3 + 3 := by
        rw [abs_mul, abs_of_nonneg hNn]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_epD'_le hs) hNn) (abs_epB'_le hs)
    _ = 3 * N + 3 := by ring

lemma measurable_hN' (N : ℝ) : Measurable (hN' N) := by
  unfold hN' epD' epB'; fun_prop

/-- `h_N'(0) = √(2π) (1 - N (1 - 2^{-3/2}))`. -/
lemma hN'_zero (N : ℝ) : hN' N 0 = √(2 * π) * (1 - N * (1 - 2 ^ (-(3 / 2 : ℝ)))) := by
  unfold hN' epD' epB'
  simp only [mul_zero, zero_add, Real.one_rpow]
  ring

/-- `h_N' ≥ h_N'(0)` on `[0, ∞)` for `N ≥ 2`. -/
lemma hN'_ge {N : ℝ} (hN2 : 2 ≤ N) {s : ℝ} (hs : 0 ≤ s) : hN' N 0 ≤ hN' N s := by
  have h1 : (s + 2) ^ (-(3 / 2 : ℝ)) ≥ (2 * (2 * s + 1)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have hx : (2 * s + 1) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hc : (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (show (-(3 / 2 : ℝ)) ≤ -1 by norm_num)
    rw [Real.rpow_neg_one] at this; linarith
  have hc0 : 0 ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hp := sqrt_two_pi_nonneg
  have e0 : hN' N 0 = N * (√(2 * π) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) - 1)) + √(2 * π) := by
    unfold hN' epD' epB'; simp only [mul_zero, zero_add, Real.one_rpow]; ring
  rw [e0]
  unfold hN' epD' epB'
  set x := (2 * s + 1) ^ (-(3 / 2 : ℝ))
  set y := (s + 2) ^ (-(3 / 2 : ℝ))
  set c := (2 : ℝ) ^ (-(3 / 2 : ℝ))
  have key : 0 ≤ N * (y - x - c + 1) + x - 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : 0 ≤ y - c * x),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by nlinarith : (0 : ℝ) ≤ N * (1 - c) - 1)]
  nlinarith [mul_nonneg hp key]

lemma epB'_le {s : ℝ} (hs : 0 ≤ s) : epB' s ≤ epB' 0 := by
  unfold epB'
  simp only [mul_zero, zero_add, Real.one_rpow, mul_one]
  have hx : (2 * s + 1) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  nlinarith [sqrt_two_pi_nonneg]

/-- `h_N'(s) ≤ h_N'(0) + 8 N s` on `[0, ∞)`. -/
lemma hN'_le_lin {N : ℝ} (hNn : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) : hN' N s ≤ hN' N 0 + 8 * N * s := by
  unfold hN'
  have := mul_le_mul_of_nonneg_left (epD'_le_lin hs) hNn
  have := epB'_le hs
  nlinarith

/-- The loss with slice function `N D + B` is the loss with slice function `D` and weight `μ N`, plus `μ ∫ B`. -/
lemma loss_hN {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) (N μ : ℝ)
    (Δ S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) :
    loss ν (hN N) μ Δ S W = loss ν epD (μ * N) Δ S W + μ * ∫ a, epB (qf (bW S W) a) ∂ν := by
  have cD : Continuous fun a => epD (qf (bW S W) a) :=
    continuous_iff_continuousAt.2 fun a =>
      (hasDerivAt_epD (qf_nonneg _ a)).continuousAt.comp (f := fun a => qf (bW S W) a) (continuous_qf _).continuousAt
  have cB : Continuous fun a => epB (qf (bW S W) a) :=
    continuous_iff_continuousAt.2 fun a =>
      (hasDerivAt_epB (qf_nonneg _ a)).continuousAt.comp (f := fun a => qf (bW S W) a) (continuous_qf _).continuousAt
  unfold loss hN
  rw [integral_add ((integrable_cont hs cD).const_mul N) (integrable_cont hs cB), integral_const_mul]
  ring

/-- **Theorem 1 at batch size `N`.** -/
theorem never_learned_flow_batch {ν : Measure (Fin K → ℝ)} (hiso : Iso4 K ν) (hK : 0 < K) {N μ σ δ T : ℝ}
    (hN2 : 2 ≤ N) (hμ : 0 ≤ μ) {Δ S : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) {e : Fin d → ℝ}
    (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q) (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q)
    {W W' : ℝ → Fin K → Fin d → ℝ} (hW : ∀ t, HasDerivAt W (W' t) t)
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν (hN N) μ Δ S (W t + s • H)) (-frob (W' t) H) 0) :
    ∀ t ∈ Icc 0 T, σ * nsq (col (W t) e) ≤
      σ * nsq (col (W 0) e) * exp (4 * (σ * (-(μ * hN' N 0) / K) - δ) * t) := by
  have hN0 : (0 : ℝ) ≤ N := by linarith [hN2]
  exact never_learned_flow hiso hK (fun _ hx => hasDerivAt_hN N hx) (measurable_hN' N)
    (fun _ hx => abs_hN'_le hN0 hx) (fun _ hx => abs_hN_le hN0 hx) (fun _ hx => hN'_ge hN2 hx) hμ hΔ hΔe hSe hW
    hflow

/-- **Theorem 2 at batch size `N`**, with `L₂ = 8 N`. -/
theorem early_phase_flow_batch {ν : Measure (Fin K → ℝ)} (hiso : Iso4 K ν) (hK : 0 < K) {N μ σ δ ε T : ℝ}
    (hN2 : 2 ≤ N) (hμ : 0 ≤ μ) {Δ S : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) {e : Fin d → ℝ}
    (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q) (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q)
    {W W' : ℝ → Fin K → Fin d → ℝ} (hW : ∀ t, HasDerivAt W (W' t) t)
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν (hN N) μ Δ S (W t + s • H)) (-frob (W' t) H) 0)
    (hsmall : ∀ t ∈ Icc 0 T, trM (bW S (W t)) ≤ ε) :
    ∀ t ∈ Icc 0 T, σ * nsq (col (W 0) e) * exp (4 * (σ * (-(μ * hN' N 0) / K) - δ -
      3 * μ * σ * (8 * N) * ε / (K * (K + 2))) * t) ≤ σ * nsq (col (W t) e) := by
  have hN0 : (0 : ℝ) ≤ N := by linarith [hN2]
  exact early_phase_flow hiso hK (fun _ hx => hasDerivAt_hN N hx) (measurable_hN' N)
    (fun _ hx => abs_hN'_le hN0 hx) (fun _ hx => abs_hN_le hN0 hx) (by positivity)
    (fun _ hx => hN'_le_lin hN0 hx) hμ hΔ hΔe hSe hW hflow hsmall

end LejepaDyn
