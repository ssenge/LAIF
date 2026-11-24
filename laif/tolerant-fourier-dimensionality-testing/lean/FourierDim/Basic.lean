import Mathlib

/-!
# Tolerant Fourier dimensionality testing: the arithmetic of the tester

Throughout, 0 ≤ α < 1/2 and x = 1 − 2α, so that 1 + 2α = 2 − x and 0 < x ≤ 1. The mass outside the
current subspace is w, its estimate is ŵ, the number of conditioned samples is m, and Λ ≥ 80αk.

* `phaseA_ratio`: a sample drawn after the certificate μ(W̄) ≥ Λε/2 leaves U with probability at
  most 8α/Λ ≤ 1/(10k).
* `phaseB_mass`: after ŵ > (2 − x)ε, the mass satisfies w > 7ε/8.
* `est_ratio`, `yes_margin`, `second_moment_eq`, `second_moment_le`: the yes case of phase B.
* `no_estimate`, `no_threshold`, `tail_exponent`: the no case of phase B.
* `outside_same`: replacing a subspace by the span of W and the samples inside it keeps the set of
  samples outside.
-/

namespace FourierDim

/-- Phase A: 4αε/(Λε/2) ≤ 1/(10k) when Λ ≥ 80αk. -/
theorem phaseA_ratio (α ε Λ : ℝ) (k : ℕ) (hk : 1 ≤ k) (hα : 0 ≤ α) (hε : 0 < ε) (hΛ : 0 < Λ)
    (hΛk : 80 * α * k ≤ Λ) : 4 * α * ε / (Λ * ε / 2) ≤ 1 / (10 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hΛk hε.le]

/-- Phase B: if ŵ ≤ w + (x/8) max(w, ε) and ŵ > (2 − x)ε, then w > 7ε/8. -/
theorem phaseB_mass (x ε w ŵ : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε)
    (hest : ŵ ≤ w + x / 8 * max w ε) (hacc : (2 - x) * ε < ŵ) : 7 * ε / 8 < w := by
  rcases le_total w ε with h | h
  · rw [max_eq_right h] at hest; nlinarith
  · linarith

/-- The estimate in the yes case: if 7ε/8 < w and ŵ ≤ w + (x/8) max(w, ε), then ŵ ≤ (1 + x/7) w. -/
theorem est_ratio (x ε w ŵ : ℝ) (hx : 0 < x) (hε : 0 < ε) (hw : 7 * ε / 8 < w)
    (hest : ŵ ≤ w + x / 8 * max w ε) : ŵ ≤ (1 + x / 7) * w := by
  rcases le_total w ε with h | h
  · rw [max_eq_right h] at hest; nlinarith
  · rw [max_eq_left h] at hest; nlinarith

/-- The yes-case margin: (1 + 2α)(1 − x/7) − 4α ≥ (5/7) x for x = 1 − 2α. -/
theorem yes_margin (α : ℝ) :
    5 / 7 * (1 - 2 * α) ≤ (1 + 2 * α) * (1 - (1 - 2 * α) / 7) - 4 * α := by
  nlinarith [sq_nonneg (1 - 2 * α)]

/-- The second-moment ratio: the variance bound 4αεm/w over the squared margin
((5/7) x (ε/w) m)² equals (196/25) α w/(ε m x²). -/
theorem second_moment_eq (α ε w m x : ℝ) (hε : 0 < ε) (hw : 0 < w) (hm : 0 < m) (hx : 0 < x) :
    4 * α * ε * m / w / (5 / 7 * x * (ε / w) * m) ^ 2 = 196 / 25 * α * w / (ε * m * x ^ 2) := by
  have h1 := hε.ne'
  have h2 := hw.ne'
  have h3 := hm.ne'
  have h4 := hx.ne'
  field_simp <;> ring

/-- With w ≤ Λε the ratio is at most 8αΛ/(m x²). -/
theorem second_moment_le (α ε w m x Λ : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) (hw : 0 < w) (hm : 0 < m)
    (hx : 0 < x) (hwΛ : w ≤ Λ * ε) :
    196 / 25 * α * w / (ε * m * x ^ 2) ≤ 8 * α * Λ / (m * x ^ 2) := by
  have hΛ : 0 ≤ Λ := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := mul_le_mul_of_nonneg_left hwΛ (by positivity : 0 ≤ α * (m * x ^ 2))
  have h2 : 0 ≤ α * Λ * ε * (m * x ^ 2) := by positivity
  nlinarith

/-- The no case: if w ≥ 2ε and ŵ ≥ (1 − x/8) w, then ŵ > (2 − x)ε, so the tester draws samples. -/
theorem no_estimate (x ε w ŵ : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) (hw : 2 * ε ≤ w)
    (hest : (1 - x / 8) * w ≤ ŵ) : (2 - x) * ε < ŵ := by
  nlinarith

/-- The no-case threshold: with ŵ ≥ (1 − x/8) w and m x ≥ 16k, the threshold (2 − x)(ε/ŵ) m is at
most (1 − x/4) times the lower bound (2ε/w)(m − k) on the mean. -/
theorem no_threshold (x ε w ŵ m k : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) (hw : 0 < w)
    (hest : (1 - x / 8) * w ≤ ŵ) (hk : 0 ≤ k) (hmk : k ≤ m) (hm : 16 * k ≤ m * x) :
    (2 - x) * (ε / ŵ) * m ≤ (1 - x / 4) * (2 * ε / w) * (m - k) := by
  have h8 : 0 < 1 - x / 8 := by linarith
  have hu : 0 < (1 - x / 8) * w := mul_pos h8 hw
  have hm0 : 0 ≤ m := le_trans hk hmk
  have h1 : (2 - x) * (ε / ŵ) * m ≤ (2 - x) * (ε / ((1 - x / 8) * w)) * m :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε.le hu hest) (by linarith)) hm0
  have key : (2 - x) * m ≤ (1 - x / 4) * 2 * (m - k) * (1 - x / 8) := by
    nlinarith [mul_nonneg hx.le hk, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hmk)]
  have h2 : (2 - x) * (ε / ((1 - x / 8) * w)) * m = ε / w * ((2 - x) * m / (1 - x / 8)) := by
    rw [mul_comm (1 - x / 8) w, ← div_div]; ring
  have h3 : (2 - x) * m / (1 - x / 8) ≤ (1 - x / 4) * 2 * (m - k) := by
    rw [div_le_iff₀ h8]; exact key
  calc (2 - x) * (ε / ŵ) * m ≤ ε / w * ((2 - x) * m / (1 - x / 8)) := h1.trans h2.le
    _ ≤ ε / w * ((1 - x / 4) * 2 * (m - k)) :=
        mul_le_mul_of_nonneg_left h3 (div_nonneg hε.le hw.le)
    _ = (1 - x / 4) * (2 * ε / w) * (m - k) := by ring

/-- The exponent of the lower-tail bound: with w ≤ Λε,
x²(m − k)/(16Λ) ≤ (x²/32)(2ε/w)(m − k). -/
theorem tail_exponent (x ε w Λ m k : ℝ) (hε : 0 < ε) (hw : 0 < w) (hΛ : 0 < Λ) (hwΛ : w ≤ Λ * ε)
    (hmk : k ≤ m) : x ^ 2 * (m - k) / (16 * Λ) ≤ x ^ 2 / 32 * (2 * ε / w) * (m - k) := by
  have h : 1 / Λ ≤ ε / w := by
    rw [div_le_div_iff₀ hΛ hw, one_mul, mul_comm]; exact hwΛ
  have hc : 0 ≤ x ^ 2 * (m - k) / 16 :=
    div_nonneg (mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hmk)) (by norm_num)
  calc x ^ 2 * (m - k) / (16 * Λ) = x ^ 2 * (m - k) / 16 * (1 / Λ) := by ring
    _ ≤ x ^ 2 * (m - k) / 16 * (ε / w) := mul_le_mul_of_nonneg_left h hc
    _ = x ^ 2 / 32 * (2 * ε / w) * (m - k) := by ring

/-- If W ≤ U, then a sample s ∈ S lies outside W ⊔ span(S ∩ U) exactly when it lies outside U. -/
theorem outside_same {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (W U : Submodule R M) (S : Set M) (hWU : W ≤ U) (s : M) (hs : s ∈ S) :
    s ∉ W ⊔ Submodule.span R {t | t ∈ S ∧ t ∈ U} ↔ s ∉ U := by
  have hle : W ⊔ Submodule.span R {t | t ∈ S ∧ t ∈ U} ≤ U :=
    sup_le hWU (Submodule.span_le.mpr (fun t ht => ht.2))
  constructor
  · intro h hU
    exact h (Submodule.mem_sup_right (Submodule.subset_span ⟨hs, hU⟩))
  · intro h hT
    exact h (hle hT)

end FourierDim
