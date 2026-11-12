import Mathlib

/-!
# Inequalities behind low-regret tomography of pure qudit states

Vectors live in a complex inner product space `E`; the inner product `⟪x, y⟫_ℂ` is
conjugate linear in `x`. The squared overlap of unit vectors `φ`, `ψ` is `‖⟪φ, ψ⟫_ℂ‖ ^ 2`.

* `chart_bound`: the algebraic core of Lemma 1 (the chart bound on the infidelity).
* `chart_region`: the scalar bound used for the region `|a| > 1` in the proof of Theorem 1.
* `inner_orth_sq_le`, `overlap_deriv_sq_le`: Lemma 2 (one two-outcome measurement carries
  information of trace at most 4), in the form of the derivative of the overlap along a
  tangent vector.
* `pair_difference`: Lemma 3 (exact linear model of a symmetric pair).
* `update_bound`: Lemma 4 (infidelity after the update).
-/

open scoped InnerProductSpace ComplexConjugate

namespace QuditRegret

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Core of Lemma 1: `(1 + ‖a‖²)(1 + ‖b‖²) - |1 + ⟪a, b⟫|² ≥ ‖a - b‖²`. For the chart vectors
`(1, a)/√(1 + ‖a‖²)` the left side divided by `(1 + ‖a‖²)(1 + ‖b‖²)` is their infidelity. -/
theorem chart_bound (a b : E) :
    ‖a - b‖ ^ 2 ≤ (1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2) - ‖(1 : ℂ) + ⟪a, b⟫_ℂ‖ ^ 2 := by
  have h1 := norm_sub_sq (𝕜 := ℂ) a b
  have h3 := norm_inner_le_norm (𝕜 := ℂ) a b
  have h4 : ‖⟪a, b⟫_ℂ‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h2 : ‖(1 : ℂ) + ⟪a, b⟫_ℂ‖ ^ 2 = 1 + 2 * (⟪a, b⟫_ℂ).re + ‖⟪a, b⟫_ℂ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    ring
  simp only [RCLike.re_to_complex] at h1
  linear_combination h4 + h2 + h1

/-- The bound used for `|a| > 1` in the proof of Theorem 1: `(u - 1/2)² ≥ (1 + u²)/8` for `u ≥ 1`,
so `(u - 1/2)² / (1.25 (1 + u²)) ≥ 0.1`. -/
theorem chart_region {u : ℝ} (hu : 1 ≤ u) : (1 + u ^ 2) / 8 ≤ (u - 1 / 2) ^ 2 := by
  linear_combination (1 / 8 : ℝ) * mul_nonneg (sub_nonneg.2 hu) (by linarith : (0 : ℝ) ≤ 7 * u - 1)

/-- Removing the component along a unit vector: `‖x - ⟪ψ, x⟫ ψ‖² = ‖x‖² - |⟪ψ, x⟫|²`. -/
theorem norm_sub_proj_sq {ψ : E} (hψ : ‖ψ‖ = 1) (x : E) :
    ‖x - ⟪ψ, x⟫_ℂ • ψ‖ ^ 2 = ‖x‖ ^ 2 - ‖⟪ψ, x⟫_ℂ‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, hψ, mul_one]
  have e2 : ⟪x, ψ⟫_ℂ = conj ⟪ψ, x⟫_ℂ := (inner_conj_symm x ψ).symm
  rw [e2, RCLike.mul_conj]
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  ring

/-- Lemma 2, first step: for unit `φ`, `ψ` and `v ⊥ ψ`, `|⟪φ, v⟫|² ≤ (1 - |⟪ψ, φ⟫|²) ‖v‖²`. -/
theorem inner_orth_sq_le {φ ψ v : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) (hv : ⟪ψ, v⟫_ℂ = 0) :
    ‖⟪φ, v⟫_ℂ‖ ^ 2 ≤ (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) * ‖v‖ ^ 2 := by
  have key : ⟪φ, v⟫_ℂ = ⟪φ - ⟪ψ, φ⟫_ℂ • ψ, v⟫_ℂ := by
    rw [inner_sub_left, inner_smul_left, hv, mul_zero, sub_zero]
  have cs := norm_inner_le_norm (𝕜 := ℂ) (φ - ⟪ψ, φ⟫_ℂ • ψ) v
  have hp := norm_sub_proj_sq hψ φ
  rw [hφ, one_pow] at hp
  rw [key]
  calc ‖⟪φ - ⟪ψ, φ⟫_ℂ • ψ, v⟫_ℂ‖ ^ 2 ≤ (‖φ - ⟪ψ, φ⟫_ℂ • ψ‖ * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) cs 2
    _ = ‖φ - ⟪ψ, φ⟫_ℂ • ψ‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ = (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) * ‖v‖ ^ 2 := by rw [hp]

/-- Lemma 2: a tangent vector at the unit vector `ψ` is `iλψ + v` with `λ` real and `v ⊥ ψ`, and
the derivative of the overlap `q = |⟪φ, ψ⟫|²` along it is `2 Re(conj⟪φ, ψ⟫ ⟪φ, iλψ + v⟫)`. Its
square is at most `4 q (1 - q) ‖v‖²`. In the chart, `‖v‖` is at most the length of the
coordinate direction, so the information `|∇q|² / (q (1 - q))` of one outcome is at most 4. -/
theorem overlap_deriv_sq_le {φ ψ v : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) (hv : ⟪ψ, v⟫_ℂ = 0)
    (lam : ℝ) :
    (2 * (conj ⟪φ, ψ⟫_ℂ * ⟪φ, ((lam : ℂ) * Complex.I) • ψ + v⟫_ℂ).re) ^ 2 ≤
      4 * (‖⟪φ, ψ⟫_ℂ‖ ^ 2 * (1 - ‖⟪φ, ψ⟫_ℂ‖ ^ 2)) * ‖v‖ ^ 2 := by
  set p := ⟪φ, ψ⟫_ℂ with hp_def
  have hsplit : conj p * ⟪φ, ((lam : ℂ) * Complex.I) • ψ + v⟫_ℂ =
      ((lam * ‖p‖ ^ 2 : ℝ) : ℂ) * Complex.I + conj p * ⟪φ, v⟫_ℂ := by
    rw [inner_add_right, inner_smul_right, mul_add]
    have : conj p * p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
    calc conj p * ((lam : ℂ) * Complex.I * p) + conj p * ⟪φ, v⟫_ℂ
        = (lam : ℂ) * Complex.I * (conj p * p) + conj p * ⟪φ, v⟫_ℂ := by ring
      _ = _ := by rw [this]; push_cast; ring
  have hre : (((lam * ‖p‖ ^ 2 : ℝ) : ℂ) * Complex.I).re = 0 := by
    rw [Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [hsplit, Complex.add_re, hre, zero_add]
  have habs : |(conj p * ⟪φ, v⟫_ℂ).re| ≤ ‖p‖ * ‖⟪φ, v⟫_ℂ‖ := by
    calc |(conj p * ⟪φ, v⟫_ℂ).re| ≤ ‖conj p * ⟪φ, v⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ = ‖p‖ * ‖⟪φ, v⟫_ℂ‖ := by rw [norm_mul, Complex.norm_conj]
  have hsq : (conj p * ⟪φ, v⟫_ℂ).re ^ 2 ≤ ‖p‖ ^ 2 * ‖⟪φ, v⟫_ℂ‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at this
    linear_combination this
  have horth := inner_orth_sq_le hφ hψ hv
  rw [norm_inner_symm ψ φ, ← hp_def] at horth
  have hp0 : 0 ≤ ‖p‖ ^ 2 := by positivity
  linear_combination 4 * hsq + 4 * mul_le_mul_of_nonneg_left horth hp0

/-- Lemma 3: for a symmetric pair `x ± y`, `|⟪x + y, ψ⟫|² - |⟪x - y, ψ⟫|² = 4 Re(conj⟪x, ψ⟫ ⟪y, ψ⟫)`.
With `x = cos s · c` and `y = sin s · u` this is `q₊ - q₋ = 2 sin 2s · Re(conj α ⟪u, β⟫)`. -/
theorem pair_difference (x y ψ : E) :
    ‖⟪x + y, ψ⟫_ℂ‖ ^ 2 - ‖⟪x - y, ψ⟫_ℂ‖ ^ 2 = 4 * (conj ⟪x, ψ⟫_ℂ * ⟪y, ψ⟫_ℂ).re := by
  rw [inner_add_left, inner_sub_left, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Lemma 4: let `c`, `ψ` be unit vectors with `α = ⟪c, ψ⟫ ≠ 0`, `β = ψ - α c` and `y ⊥ c`. The
infidelity of `(c + y)/‖c + y‖` with `ψ` is at most `‖y - β/α‖²`. -/
theorem update_bound {c ψ y : E} (hc : ‖c‖ = 1) (hψ : ‖ψ‖ = 1) (hy : ⟪c, y⟫_ℂ = 0)
    (hα : ⟪c, ψ⟫_ℂ ≠ 0) :
    1 - ‖⟪ψ, c + y⟫_ℂ‖ ^ 2 / ‖c + y‖ ^ 2 ≤
      ‖y - (⟪c, ψ⟫_ℂ)⁻¹ • (ψ - ⟪c, ψ⟫_ℂ • c)‖ ^ 2 := by
  set α := ⟪c, ψ⟫_ℂ with hα_def
  set e := y - α⁻¹ • (ψ - α • c) with he_def
  have hw : c + y = α⁻¹ • ψ + e := by
    rw [he_def, smul_sub, smul_smul, inv_mul_cancel₀ hα, one_smul]
    abel
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hinner : ⟪ψ, c + y⟫_ℂ = α⁻¹ + ⟪ψ, e⟫_ℂ := by
    rw [hw, inner_add_right, inner_smul_right, hψψ, mul_one]
  have hvec : (c + y) - ⟪ψ, c + y⟫_ℂ • ψ = e - ⟪ψ, e⟫_ℂ • ψ := by
    rw [hinner, add_smul]
    nth_rewrite 1 [hw]
    abel
  have hf : ‖c + y‖ ^ 2 - ‖⟪ψ, c + y⟫_ℂ‖ ^ 2 = ‖e‖ ^ 2 - ‖⟪ψ, e⟫_ℂ‖ ^ 2 := by
    rw [← norm_sub_proj_sq hψ, ← norm_sub_proj_sq hψ, hvec]
  have hwn : 1 ≤ ‖c + y‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hc, hy]
    simp only [map_zero, mul_zero, add_zero, one_pow]
    linarith [sq_nonneg ‖y‖]
  have hpos : 0 < ‖c + y‖ ^ 2 := by linarith
  have h1 : 1 - ‖⟪ψ, c + y⟫_ℂ‖ ^ 2 / ‖c + y‖ ^ 2 =
      (‖c + y‖ ^ 2 - ‖⟪ψ, c + y⟫_ℂ‖ ^ 2) / ‖c + y‖ ^ 2 := by
    rw [sub_div, div_self hpos.ne']
  rw [h1, hf, div_le_iff₀ hpos]
  have he0 : 0 ≤ ‖e‖ ^ 2 := by positivity
  linear_combination mul_le_mul_of_nonneg_left hwn he0 + sq_nonneg ‖⟪ψ, e⟫_ℂ‖

end QuditRegret
