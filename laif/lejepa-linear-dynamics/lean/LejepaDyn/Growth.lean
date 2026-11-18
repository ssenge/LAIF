import Mathlib

/-!
# Exponential comparison for a scalar differential inequality

If `ṅ ≤ R n` on `[0, T]`, then `n(t) ≤ n(0) e^{R t}` there, and the reverse inequalities hold as well.
-/

open Set Real

namespace LejepaDyn

lemma hasDerivAt_mul_exp {n : ℝ → ℝ} {d R t : ℝ} (hn : HasDerivAt n d t) :
    HasDerivAt (fun s => n s * exp (-(R * s))) ((d - R * n t) * exp (-(R * t))) t := by
  have he : HasDerivAt (fun s => exp (-(R * s))) (exp (-(R * t)) * (-R)) t := by
    have := ((hasDerivAt_id t).const_mul R).neg.exp
    simpa using this
  convert hn.mul he using 1; ring

/-- `ṅ ≤ R n` on `[0, T]` gives `n(t) ≤ n(0) e^{R t}` on `[0, T]`. -/
theorem growth_le {n d : ℝ → ℝ} {R T : ℝ} (hd : ∀ t, HasDerivAt n (d t) t)
    (hle : ∀ t ∈ Icc 0 T, d t ≤ R * n t) : ∀ t ∈ Icc 0 T, n t ≤ n 0 * exp (R * t) := by
  set f := fun s => n s * exp (-(R * s))
  have hf : ∀ t, HasDerivAt f ((d t - R * n t) * exp (-(R * t))) t := fun t => hasDerivAt_mul_exp (hd t)
  have hanti : AntitoneOn f (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [(hf t).deriv]
    rw [interior_Icc] at ht
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle t (Ioo_subset_Icc_self ht)]) (exp_pos _).le
  intro t ht
  by_cases hT : 0 ≤ T
  · have := hanti ⟨le_rfl, hT⟩ ht ht.1
    simp only [f, mul_zero, neg_zero, exp_zero, mul_one] at this
    have hpos := exp_pos (R * t)
    calc n t = n t * exp (-(R * t)) * exp (R * t) := by rw [mul_assoc, ← exp_add]; simp
      _ ≤ n 0 * exp (R * t) := mul_le_mul_of_nonneg_right this hpos.le
  · exact absurd (ht.1.trans ht.2) hT

/-- `ṅ ≥ R n` on `[0, T]` gives `n(t) ≥ n(0) e^{R t}` on `[0, T]`. -/
theorem growth_ge {n d : ℝ → ℝ} {R T : ℝ} (hd : ∀ t, HasDerivAt n (d t) t)
    (hge : ∀ t ∈ Icc 0 T, R * n t ≤ d t) : ∀ t ∈ Icc 0 T, n 0 * exp (R * t) ≤ n t := by
  have := growth_le (n := fun s => -n s) (d := fun s => -d s) (R := R) (T := T)
    (fun t => (hd t).neg) (fun t ht => by linarith [hge t ht])
  intro t ht
  have := this t ht
  linarith

end LejepaDyn
