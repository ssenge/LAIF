import QuditRegret.Basic

/-!
# Non-vacuity of the inequalities behind low-regret tomography

The hypotheses of the theorems of `QuditRegret.Basic` can be met, and the inequalities are
attained with nonzero sides, so none of them holds with room to spare for every input.

* `units_exist`: unit vectors with nonzero overlap exist (in `ℂ` itself).
* `chart_bound_zero`: equality in `chart_bound` at `b = 0`, with both sides `‖a‖²`.
* `chart_region_eq`, `chart_region_fails`: equality in `chart_region` at `u = 1`; the bound fails
  at `u = 1/2`, so the hypothesis `1 ≤ u` is needed.
* `proj_facts`, `inner_orth_sq_eq`: for unit `φ`, `ψ` the vector `v = φ - ⟪ψ, φ⟫ ψ` is orthogonal
  to `ψ`, has `‖v‖² = 1 - |⟪ψ, φ⟫|²` (nonzero when `|⟪ψ, φ⟫| < 1`), and attains equality in
  `inner_orth_sq_le`.
* `overlap_deriv_sq_eq`: with `λ = 0`, this `v` and a real overlap `⟪φ, ψ⟫`, equality holds in
  `overlap_deriv_sq_le`.
* `update_bound_exact`: the update `y = β/α` meets the hypotheses of `update_bound` for all unit
  `c`, `ψ` with `⟪c, ψ⟫ ≠ 0`, and gives infidelity at most `0`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace QuditRegret

theorem units_exist : ‖(1 : ℂ)‖ = 1 ∧ ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ ≠ 0 := by
  constructor
  · simp
  · rw [inner_self_eq_norm_sq_to_K]; simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem chart_bound_zero (a : E) :
    ‖a - 0‖ ^ 2 = (1 + ‖a‖ ^ 2) * (1 + ‖(0 : E)‖ ^ 2) - ‖(1 : ℂ) + ⟪a, (0 : E)⟫_ℂ‖ ^ 2 := by
  rw [sub_zero, norm_zero, inner_zero_right, add_zero, norm_one]
  ring

theorem chart_region_eq : (1 + (1 : ℝ) ^ 2) / 8 = (1 - 1 / 2) ^ 2 := by norm_num

theorem chart_region_fails : ¬ ((1 + (1 / 2 : ℝ) ^ 2) / 8 ≤ (1 / 2 - 1 / 2) ^ 2) := by norm_num

theorem proj_facts {φ ψ v : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) (hv : v = φ - ⟪ψ, φ⟫_ℂ • ψ) :
    ⟪ψ, v⟫_ℂ = 0 ∧ ‖v‖ ^ 2 = 1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 ∧ ⟪φ, v⟫_ℂ = ⟪v, v⟫_ℂ := by
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hperp : ⟪ψ, v⟫_ℂ = 0 := by
    rw [hv, inner_sub_right, inner_smul_right, hψψ, mul_one, sub_self]
  have hn : ‖v‖ ^ 2 = 1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
    rw [hv, norm_sub_proj_sq hψ φ, hφ, one_pow]
  have hφ_eq : φ = v + ⟪ψ, φ⟫_ℂ • ψ := by rw [hv, sub_add_cancel]
  refine ⟨hperp, hn, ?_⟩
  calc ⟪φ, v⟫_ℂ = ⟪v + ⟪ψ, φ⟫_ℂ • ψ, v⟫_ℂ := by rw [← hφ_eq]
    _ = ⟪v, v⟫_ℂ := by rw [inner_add_left, inner_smul_left, hperp, mul_zero, add_zero]

theorem inner_orth_sq_eq {φ ψ v : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hv : v = φ - ⟪ψ, φ⟫_ℂ • ψ) :
    ‖⟪φ, v⟫_ℂ‖ ^ 2 = (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) * ‖v‖ ^ 2 := by
  obtain ⟨-, hn, hφv⟩ := proj_facts hφ hψ hv
  rw [hφv, ← inner_self_re_eq_norm, ← norm_sq_eq_re_inner, hn]
  ring

theorem overlap_deriv_sq_eq {φ ψ v : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hv : v = φ - ⟪ψ, φ⟫_ℂ • ψ) (hreal : (⟪φ, ψ⟫_ℂ).im = 0) :
    (2 * (conj ⟪φ, ψ⟫_ℂ * ⟪φ, (((0 : ℝ) : ℂ) * Complex.I) • ψ + v⟫_ℂ).re) ^ 2 =
      4 * (‖⟪φ, ψ⟫_ℂ‖ ^ 2 * (1 - ‖⟪φ, ψ⟫_ℂ‖ ^ 2)) * ‖v‖ ^ 2 := by
  obtain ⟨-, hn, hφv⟩ := proj_facts hφ hψ hv
  have hvv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) v, RCLike.re_to_complex]
  have hq : ‖⟪φ, ψ⟫_ℂ‖ ^ 2 = (⟪φ, ψ⟫_ℂ).re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hreal]; ring
  rw [norm_inner_symm ψ φ] at hn
  rw [Complex.ofReal_zero, zero_mul, zero_smul, zero_add, hφv, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, hvv, hn, hq, hreal]
  ring

theorem update_bound_exact {c ψ : E} (hc : ‖c‖ = 1) (hψ : ‖ψ‖ = 1) (hα : ⟪c, ψ⟫_ℂ ≠ 0) :
    ⟪c, (⟪c, ψ⟫_ℂ)⁻¹ • (ψ - ⟪c, ψ⟫_ℂ • c)⟫_ℂ = 0 ∧
    1 - ‖⟪ψ, c + (⟪c, ψ⟫_ℂ)⁻¹ • (ψ - ⟪c, ψ⟫_ℂ • c)⟫_ℂ‖ ^ 2
        / ‖c + (⟪c, ψ⟫_ℂ)⁻¹ • (ψ - ⟪c, ψ⟫_ℂ • c)‖ ^ 2 ≤ 0 := by
  have hcc : ⟪c, c⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hc]; simp
  have hy : ⟪c, (⟪c, ψ⟫_ℂ)⁻¹ • (ψ - ⟪c, ψ⟫_ℂ • c)⟫_ℂ = 0 := by
    rw [inner_smul_right, inner_sub_right, inner_smul_right, hcc, mul_one, sub_self, mul_zero]
  refine ⟨hy, ?_⟩
  have h := update_bound hc hψ hy hα
  rw [sub_self, norm_zero] at h
  simpa using h

end QuditRegret
