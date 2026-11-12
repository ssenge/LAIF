import Mathlib

/-!
# The low-degree polynomial of Section 4

`polynomial_assembly` turns phases that are small outside a sparse set into a polynomial.
-/

open Finset

namespace CutQuery

section Polynomial

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]

/-- A vertex bit as a real number. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The factor `1 + h_v (e^{2πiφ} - 1)` agrees with `e^{2πi h_v φ}` on the cube. -/
theorem factor_eval (b : Bool) (p : ℝ) :
    (1 : ℂ) + (bit b : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * p) - 1)
      = Complex.exp (2 * Real.pi * Complex.I * ((bit b * p : ℝ) : ℂ)) := by
  cases b <;> simp [bit]

omit [Fintype V] in
/-- `∏_{v ∈ Y} (1 + a_v X_v)` has total degree at most `|Y|`. -/
theorem totalDegree_prod_factor (Y : Finset V) (a : V → ℂ) :
    (∏ v ∈ Y, ((1 : MvPolynomial V ℂ) + MvPolynomial.C (a v) * MvPolynomial.X v)).totalDegree
      ≤ Y.card := by
  induction Y using Finset.induction_on with
  | empty => simp
  | insert v Y hv ih =>
    rw [prod_insert hv, card_insert_of_notMem hv]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : ((1 : MvPolynomial V ℂ) + MvPolynomial.C (a v) * MvPolynomial.X v).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
    omega

/-- Section 4. Suppose `P(h) = Σ_u w_u e^{2πi Σ_v h_v φ_uv} q_u(h)` on the cube, with `‖q_u(h)‖ ≤ 1`,
`deg q_u ≤ d₁`, and `|φ_uv| ≤ τ` off a set `Y_u` of at most `d₂` vertices. Then a polynomial of degree at most
`d₁ + d₂` agrees with `P` on the cube up to `(Σ_u w_u) 2π |V| τ`. -/
theorem polynomial_assembly (w : U → ℝ) (hw : ∀ u, 0 ≤ w u) (p : U → V → ℝ)
    (q : U → MvPolynomial V ℂ) (Y : U → Finset V) (d₁ d₂ : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hq : ∀ u, (q u).totalDegree ≤ d₁) (hY : ∀ u, (Y u).card ≤ d₂)
    (hsmall : ∀ u, ∀ v ∉ Y u, |p u v| ≤ τ)
    (hbd : ∀ u (h : V → Bool), ‖MvPolynomial.eval (fun v => (bit (h v) : ℂ)) (q u)‖ ≤ 1) :
    ∃ Q : MvPolynomial V ℂ, Q.totalDegree ≤ d₁ + d₂ ∧ ∀ h : V → Bool,
      ‖(∑ u, (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p u v : ℝ) : ℂ))
            * MvPolynomial.eval (fun v => (bit (h v) : ℂ)) (q u)))
        - MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q‖
        ≤ (∑ u, w u) * (2 * Real.pi * (Fintype.card V * τ)) := by
  classical
  let fac : U → MvPolynomial V ℂ := fun u =>
    ∏ v ∈ Y u, ((1 : MvPolynomial V ℂ)
      + MvPolynomial.C (Complex.exp (2 * Real.pi * Complex.I * (p u v : ℂ)) - 1) * MvPolynomial.X v)
  refine ⟨∑ u, MvPolynomial.C (w u : ℂ) * (q u * fac u), ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun u _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (q u * fac u).totalDegree ≤ d₁ + d₂ :=
      (MvPolynomial.totalDegree_mul _ _).trans
        (add_le_add (hq u) ((totalDegree_prod_factor (Y u) _).trans (hY u)))
    simp only [MvPolynomial.totalDegree_C]
    omega
  · intro h
    rw [map_sum, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun u _ => ?_
    set ev := MvPolynomial.eval (fun v => (bit (h v) : ℂ)) with hev
    set inY : ℝ := ∑ v ∈ Y u, bit (h v) * p u v with hinY
    set offY : ℝ := ∑ v ∈ univ \ Y u, bit (h v) * p u v with hoffY
    have hsplit : (∑ v, bit (h v) * p u v) = inY + offY := by
      rw [hinY, hoffY, add_comm]
      exact (sum_sdiff (subset_univ (Y u))).symm
    have hfac : ev (fac u) = Complex.exp (2 * Real.pi * Complex.I * (inY : ℂ)) := by
      rw [hev, map_prod, hinY]
      push_cast
      rw [mul_sum, Complex.exp_sum]
      refine prod_congr rfl fun v _ => ?_
      simp only [map_add, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [mul_comm (Complex.exp _ - 1), factor_eval]
      push_cast
      rfl
    have hoff : |offY| ≤ Fintype.card V * τ := by
      calc |offY| ≤ ∑ v ∈ univ \ Y u, |bit (h v) * p u v| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ v ∈ univ \ Y u, τ := sum_le_sum fun v hv => by
            have hv' : v ∉ Y u := (mem_sdiff.mp hv).2
            have hb : |bit (h v)| ≤ 1 := by cases h v <;> simp [bit]
            rw [abs_mul]
            calc |bit (h v)| * |p u v| ≤ 1 * τ :=
                  mul_le_mul hb (hsmall u v hv') (abs_nonneg _) zero_le_one
              _ = τ := one_mul τ
        _ = ((univ \ Y u).card : ℝ) * τ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ Fintype.card V * τ := by
            refine mul_le_mul_of_nonneg_right ?_ hτ
            exact_mod_cast card_le_univ _
    have hdiff : ‖Complex.exp (2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ)) - 1‖
        ≤ 2 * Real.pi * (Fintype.card V * τ) := by
      have h1 := Real.norm_eq_abs (2 * Real.pi * offY)
      have h2 : ‖Complex.exp (Complex.I * ((2 * Real.pi * offY : ℝ) : ℂ)) - 1‖
          ≤ ‖(2 * Real.pi * offY : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      have h3 : Complex.I * ((2 * Real.pi * offY : ℝ) : ℂ)
          = 2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ) := by push_cast; ring
      rw [h3, h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left hoff (by positivity))
    have hwn : ‖(w u : ℂ)‖ = w u := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw u)]
    have hexp1 : ‖Complex.exp (2 * Real.pi * Complex.I * ((inY : ℝ) : ℂ))‖ = 1 := by
      have : 2 * Real.pi * Complex.I * ((inY : ℝ) : ℂ) = ((2 * Real.pi * inY : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hrw : (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p u v : ℝ) : ℂ))
          * ev (q u)) - ev (MvPolynomial.C (w u : ℂ) * (q u * fac u))
        = (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((inY : ℝ) : ℂ)) * ev (q u)
            * (Complex.exp (2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ)) - 1)) := by
      rw [map_mul, map_mul, hfac, hsplit, hev, MvPolynomial.eval_C]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    rw [hrw, norm_mul, hwn, norm_mul, norm_mul, hexp1, one_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hw u)
    calc ‖ev (q u)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ)) - 1‖
        ≤ 1 * (2 * Real.pi * (Fintype.card V * τ)) :=
          mul_le_mul (hbd u h) hdiff (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Polynomial

end CutQuery
