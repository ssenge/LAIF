import SigregDim.Collapse

/-!
# The SIGReg slice function

For a slice with law `N(0, s)`, the population characteristic-function statistic of SIGReg with weight `e^{-t²/2}` is
`D(s) = √(2π) ((2s+1)^{-1/2} - 2 (s+2)^{-1/2} + 3^{-1/2})`.
This file shows that `D` satisfies the assumptions `SliceFn` of the collapse theorems on `[0, ∞)`
with curvature constant `L = 8` (the sharp value is `D''(0) ≈ 6.855`).

The closed form of `D` itself rests on the Gaussian integral `∫ e^{-ct²/2} dt = √(2π/c)`.
-/

open Real Set

namespace SigregDim

/-- The SIGReg slice function. -/
noncomputable def epD (s : ℝ) : ℝ :=
  √(2 * π) * ((2 * s + 1) ^ (-(1 / 2 : ℝ)) - 2 * (s + 2) ^ (-(1 / 2 : ℝ)) + 3 ^ (-(1 / 2 : ℝ)))

/-- Its derivative. -/
noncomputable def epD' (s : ℝ) : ℝ :=
  √(2 * π) * ((s + 2) ^ (-(3 / 2 : ℝ)) - (2 * s + 1) ^ (-(3 / 2 : ℝ)))

/-- Its second derivative. -/
noncomputable def epD'' (s : ℝ) : ℝ :=
  √(2 * π) * (3 * (2 * s + 1) ^ (-(5 / 2 : ℝ)) - 3 / 2 * (s + 2) ^ (-(5 / 2 : ℝ)))

lemma sqrt_two_pi_le : √(2 * π) ≤ 2.51 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_d2]

lemma sqrt_two_pi_nonneg : 0 ≤ √(2 * π) := Real.sqrt_nonneg _

/-- Derivative of `s ↦ (a s + b)^p` at a point where `a s + b > 0`. -/
lemma hasDerivAt_affine_rpow (a b p s : ℝ) (hs : 0 < a * s + b) :
    HasDerivAt (fun s => (a * s + b) ^ p) (p * (a * s + b) ^ (p - 1) * a) s := by
  have h1 : HasDerivAt (fun s => a * s + b) a s := by
    simpa using ((hasDerivAt_id s).const_mul a).add_const b
  convert h1.rpow_const (p := p) (Or.inl hs.ne') using 1
  ring

lemma hasDerivAt_epD {s : ℝ} (hs : 0 ≤ s) : HasDerivAt epD (epD' s) s := by
  have h1 := hasDerivAt_affine_rpow 2 1 (-(1 / 2)) s (by linarith)
  have h2 := hasDerivAt_affine_rpow 1 2 (-(1 / 2)) s (by linarith)
  have := (((h1.sub (h2.const_mul 2)).add_const (3 ^ (-(1 / 2 : ℝ)))).const_mul √(2 * π))
  convert this using 1
  · funext x; simp [epD, one_mul]
  · unfold epD'
    have e1 : (2 * s + 1) ^ (-(1 / 2 : ℝ) - 1) = (2 * s + 1) ^ (-(3 / 2 : ℝ)) := by norm_num
    have e2 : (1 * s + 2) ^ (-(1 / 2 : ℝ) - 1) = (s + 2) ^ (-(3 / 2 : ℝ)) := by norm_num
    rw [e1, e2]; ring

lemma hasDerivAt_epD' {s : ℝ} (hs : 0 ≤ s) : HasDerivAt epD' (epD'' s) s := by
  have h1 := hasDerivAt_affine_rpow 1 2 (-(3 / 2)) s (by linarith)
  have h2 := hasDerivAt_affine_rpow 2 1 (-(3 / 2)) s (by linarith)
  have := (h1.sub h2).const_mul √(2 * π)
  convert this using 1
  · funext x; simp [epD', one_mul]
  · unfold epD''
    have e1 : (2 * s + 1) ^ (-(3 / 2 : ℝ) - 1) = (2 * s + 1) ^ (-(5 / 2 : ℝ)) := by norm_num
    have e2 : (1 * s + 2) ^ (-(3 / 2 : ℝ) - 1) = (s + 2) ^ (-(5 / 2 : ℝ)) := by norm_num
    rw [e1, e2]; ring

/-- `0 ≤ (a s + b)^{-q} ≤ 1` for `s ≥ 0`, `a ≥ 0`, `b ≥ 1`, `q ≥ 0`. -/
lemma rpow_neg_mem {a b q s : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    0 ≤ (a * s + b) ^ (-q) ∧ (a * s + b) ^ (-q) ≤ 1 := by
  have hx : 1 ≤ a * s + b := by nlinarith
  exact ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)⟩

lemma abs_epD''_le {s : ℝ} (hs : 0 ≤ s) : |epD'' s| ≤ 8 := by
  obtain ⟨a0, a1⟩ := rpow_neg_mem (a := 2) (b := 1) (q := 5 / 2) (by norm_num) le_rfl (by norm_num) hs
  obtain ⟨b0, b1⟩ := rpow_neg_mem (a := 1) (b := 2) (q := 5 / 2) (by norm_num) (by norm_num)
    (by norm_num) hs
  simp only [one_mul] at b0 b1
  unfold epD''
  rw [abs_mul, abs_of_nonneg sqrt_two_pi_nonneg]
  have hin : |3 * (2 * s + 1) ^ (-(5 / 2 : ℝ)) - 3 / 2 * (s + 2) ^ (-(5 / 2 : ℝ))| ≤ 3 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  calc √(2 * π) * |3 * (2 * s + 1) ^ (-(5 / 2 : ℝ)) - 3 / 2 * (s + 2) ^ (-(5 / 2 : ℝ))|
      ≤ 2.51 * 3 := mul_le_mul sqrt_two_pi_le hin (abs_nonneg _) (by norm_num)
    _ ≤ 8 := by norm_num

lemma abs_epD_le {s : ℝ} (hs : 0 ≤ s) : |epD s| ≤ 11 := by
  obtain ⟨a0, a1⟩ := rpow_neg_mem (a := 2) (b := 1) (q := 1 / 2) (by norm_num) le_rfl (by norm_num) hs
  obtain ⟨b0, b1⟩ := rpow_neg_mem (a := 1) (b := 2) (q := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) hs
  obtain ⟨c0, c1⟩ := rpow_neg_mem (a := 0) (b := 3) (q := 1 / 2) le_rfl (by norm_num) (by norm_num) hs
  simp only [one_mul, zero_mul, zero_add] at b0 b1 c0 c1
  unfold epD
  rw [abs_mul, abs_of_nonneg sqrt_two_pi_nonneg]
  have hin : |(2 * s + 1) ^ (-(1 / 2 : ℝ)) - 2 * (s + 2) ^ (-(1 / 2 : ℝ)) + 3 ^ (-(1 / 2 : ℝ))| ≤ 2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  calc √(2 * π) * |(2 * s + 1) ^ (-(1 / 2 : ℝ)) - 2 * (s + 2) ^ (-(1 / 2 : ℝ)) + 3 ^ (-(1 / 2 : ℝ))|
      ≤ 2.51 * 2 := mul_le_mul sqrt_two_pi_le hin (abs_nonneg _) (by norm_num)
    _ ≤ 11 := by norm_num

lemma abs_epD'_le {s : ℝ} (hs : 0 ≤ s) : |epD' s| ≤ 3 := by
  obtain ⟨a0, a1⟩ := rpow_neg_mem (a := 2) (b := 1) (q := 3 / 2) (by norm_num) le_rfl (by norm_num) hs
  obtain ⟨b0, b1⟩ := rpow_neg_mem (a := 1) (b := 2) (q := 3 / 2) (by norm_num) (by norm_num)
    (by norm_num) hs
  simp only [one_mul] at b0 b1
  unfold epD'
  rw [abs_mul, abs_of_nonneg sqrt_two_pi_nonneg]
  have hin : |(s + 2) ^ (-(3 / 2 : ℝ)) - (2 * s + 1) ^ (-(3 / 2 : ℝ))| ≤ 1 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  calc √(2 * π) * |(s + 2) ^ (-(3 / 2 : ℝ)) - (2 * s + 1) ^ (-(3 / 2 : ℝ))|
      ≤ 2.51 * 1 := mul_le_mul sqrt_two_pi_le hin (abs_nonneg _) (by norm_num)
    _ ≤ 3 := by norm_num

/-- `D'` is 8-Lipschitz on `[0, ∞)`. -/
lemma epD'_lip {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : |epD' x - epD' y| ≤ 8 * |x - y| := by
  have := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := epD') (f' := epD'') (C := 8)
    (fun t ht => (hasDerivAt_epD' ht).hasDerivWithinAt)
    (fun t ht => by simpa [Real.norm_eq_abs] using abs_epD''_le ht) hy hx
  simpa [Real.norm_eq_abs] using this

/-- Descent inequality from a Lipschitz derivative, on `[0, ∞)`. -/
lemma descent_of_lip {h h' : ℝ → ℝ} {L : ℝ} (hd : ∀ x, 0 ≤ x → HasDerivAt h (h' x) x)
    (hlip : ∀ x y, 0 ≤ x → 0 ≤ y → |h' x - h' y| ≤ L * |x - y|) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : h y ≤ h x + h' x * (y - x) + L / 2 * (y - x) ^ 2 := by
  have hφd : ∀ t, 0 ≤ t → HasDerivAt (fun t => h t - h x - h' x * (t - x) - L / 2 * (t - x) ^ 2)
      (h' t - h' x - L * (t - x)) t := by
    intro t ht
    have h2 : HasDerivAt (fun t => h' x * (t - x)) (h' x) t := by
      simpa using ((hasDerivAt_id' t).sub_const x).const_mul (h' x)
    have h3 : HasDerivAt (fun t => L / 2 * (t - x) ^ 2) (L * (t - x)) t := by
      have := (((hasDerivAt_id' t).sub_const x).pow 2).const_mul (L / 2)
      convert this using 1
      norm_num <;> ring
    have := (((hd t ht).sub_const (h x)).sub h2).sub h3
    convert this using 1
  suffices (fun t => h t - h x - h' x * (t - x) - L / 2 * (t - x) ^ 2) y ≤ 0 by
    simp only at this; linarith
  have hφx : (fun t => h t - h x - h' x * (t - x) - L / 2 * (t - x) ^ 2) x = 0 := by simp
  rcases le_total x y with hxy | hyx
  · -- on `[x, y]` the derivative is nonpositive
    have hanti : AntitoneOn (fun t => h t - h x - h' x * (t - x) - L / 2 * (t - x) ^ 2)
        (Icc x y) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x y)
        (fun t ht => (hφd t (hx.trans ht.1)).continuousAt.continuousWithinAt)
        (fun t ht => (hφd t (hx.trans (interior_subset ht).1)).hasDerivWithinAt) ?_
      intro t ht
      rw [interior_Icc] at ht
      have hl := hlip t x (hx.trans ht.1.le) hx
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - x)] at hl
      linarith [le_abs_self (h' t - h' x)]
    have := hanti ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
    linarith
  · -- on `[y, x]` the derivative is nonnegative
    have hmono : MonotoneOn (fun t => h t - h x - h' x * (t - x) - L / 2 * (t - x) ^ 2)
        (Icc y x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc y x)
        (fun t ht => (hφd t (hy.trans ht.1)).continuousAt.continuousWithinAt)
        (fun t ht => (hφd t (hy.trans (interior_subset ht).1)).hasDerivWithinAt) ?_
      intro t ht
      rw [interior_Icc] at ht
      have hl := hlip t x (hy.trans ht.1.le) hx
      rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0)] at hl
      linarith [neg_abs_le (h' t - h' x)]
    have := hmono ⟨le_rfl, hyx⟩ ⟨hyx, le_rfl⟩ hyx
    linarith

/-- **The SIGReg slice function satisfies the collapse assumptions with `L = 8`.** -/
theorem sliceFn_epD : SliceFn epD epD' 8 where
  meas := by unfold epD; fun_prop
  meas' := by unfold epD'; fun_prop
  bdd := ⟨11, fun x hx => abs_epD_le hx⟩
  bdd' := ⟨3, fun x hx => abs_epD'_le hx⟩
  desc := fun x y hx hy => descent_of_lip (fun t ht => hasDerivAt_epD ht)
    (fun a b ha hb => epD'_lip ha hb) hx hy
  curv := fun x y hx hxy => by
    have := epD'_lip (hx.trans hxy) hx
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)] at this
    linarith [le_abs_self (epD' y - epD' x)]
  L_nonneg := by norm_num

/-- `D(1) = 0`: the standard Gaussian slice has zero statistic. -/
lemma epD_one : epD 1 = 0 := by
  unfold epD
  rw [show (2 * (1 : ℝ) + 1) = 3 by norm_num, show ((1 : ℝ) + 2) = 3 by norm_num]
  ring

end SigregDim
