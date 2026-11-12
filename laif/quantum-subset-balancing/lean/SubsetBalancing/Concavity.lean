import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Pi

/-!
# Proposition 2: the exponents on a box

The tangent part. A concave function with a supergradient `g` at a point `x` satisfies
`f y ≤ f x + g (y - x)`. A linear function on a box is largest at a corner. So a concave function with
a derivative at a centre is bounded on a box by the value of its tangent at one corner.

The fixed-kernel part. Fix a kernel `W c l b ≥ 0`, with `c` the value, `l` the label and `b` the pair
`(x, y)`. All of the laws below are linear in the profile `π`. In bits:

* `a₀ = ∑_c π_c H(x, y | L, c)` is linear in `π`, by its form;
* `H(L)` is concave, as `negMulLog` of a linear map, so `a = H(L) - ∑_c π_c H(L | c)` is concave;
* `H(f | L) = H(f, L) - H(L)`, for `f` a function of the pair, is concave. It is a sum over `l` and `s`
  of the perspective `q ↦ q negMulLog (p / q)` of `negMulLog`, at `p` the joint mass of `(l, s)` and
  `q` the mass of `l`, and the perspective is jointly concave. This is the log-sum inequality.

With these, each of the four terms of the total exponent is concave in `π`.
-/

open Finset
open Real (log log_pos log_div negMulLog concaveOn_negMulLog)

namespace SubsetBalancing

/-! ## The tangent -/

section Tangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tangent bound along a segment: if `t ↦ f (x + t (y - x))` has derivative `g'` at `0`, then a
function concave on a set containing `x` and `y` has `f y ≤ f x + g'`. -/
theorem tangent_le_of_hasDerivAt {s : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ s f) {x y : E}
    (hx : x ∈ s) (hy : y ∈ s) {g' : ℝ}
    (hg : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) g' 0) : f y ≤ f x + g' := by
  have hlim := hg.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f y - f x ≤ t⁻¹ • (f (x + (0 + t) • (y - x)) - f (x + (0 : ℝ) • (y - x))) := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 := hf.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    have h2 : (1 - t) • x + t • y = x + (0 + t) • (y - x) := by
      rw [zero_add, smul_sub, sub_smul, one_smul]
      abel
    rw [h2] at h1
    simp only [smul_eq_mul, zero_smul, add_zero] at h1 ⊢
    rw [le_inv_mul_iff₀ ht0]
    linarith
  have := ge_of_tendsto hlim hev
  linarith

/-- **The tangent.** If `f` is concave on a set and has derivative `g` at `x`, then
`f y ≤ f x + g (y - x)` on that set. -/
theorem tangent_le {s : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {g : E →L[ℝ] ℝ} (hg : HasFDerivAt f g x) : f y ≤ f x + g (y - x) := by
  refine tangent_le_of_hasDerivAt hf hx hy ?_
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hg0 : HasFDerivAt f g (x + (0 : ℝ) • (y - x)) := by simpa using hg
  exact hg0.comp_hasDerivAt (0 : ℝ) hline

end Tangent

/-! ## The corner -/

section Corner

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The corner of the box `[lo, hi]` that maximizes the linear form with coefficients `w`. -/
noncomputable def corner (w lo hi : κ → ℝ) : κ → ℝ := fun c => if 0 ≤ w c then hi c else lo c

omit [Fintype κ] [DecidableEq κ] in
theorem corner_mem {w lo hi : κ → ℝ} (h : lo ≤ hi) : corner w lo hi ∈ Set.Icc lo hi := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · simp only [corner]
    split_ifs
    · exact h c
    · exact le_rfl
  · simp only [corner]
    split_ifs
    · exact le_rfl
    · exact h c

omit [DecidableEq κ] in
/-- A linear form with coefficients `w` is largest on the box at `corner w lo hi`. -/
theorem sum_le_corner {w lo hi x : κ → ℝ} (hx : x ∈ Set.Icc lo hi) :
    ∑ c, w c * x c ≤ ∑ c, w c * corner w lo hi c := by
  refine sum_le_sum fun c _ => ?_
  simp only [corner]
  split_ifs with hw
  · exact mul_le_mul_of_nonneg_left (hx.2 c) hw
  · exact mul_le_mul_of_nonpos_left (hx.1 c) (not_le.mp hw).le

/-- The coefficients of a linear form on `κ → ℝ`. -/
def coeffs (φ : (κ → ℝ) →ₗ[ℝ] ℝ) : κ → ℝ := fun c => φ fun j => if c = j then 1 else 0

theorem linear_eq_sum (φ : (κ → ℝ) →ₗ[ℝ] ℝ) (x : κ → ℝ) : φ x = ∑ c, coeffs φ c * x c := by
  rw [LinearMap.pi_apply_eq_sum_univ φ x]
  exact sum_congr rfl fun c _ => by simp [coeffs, mul_comm]

/-- **A linear function on a box is largest at a corner.** -/
theorem linear_le_corner (φ : (κ → ℝ) →ₗ[ℝ] ℝ) {lo hi x : κ → ℝ} (hx : x ∈ Set.Icc lo hi) :
    φ x ≤ φ (corner (coeffs φ) lo hi) := by
  rw [linear_eq_sum φ x, linear_eq_sum φ (corner _ lo hi)]
  exact sum_le_corner hx

/-- The maximum of a linear function over a box is attained at a point whose coordinates are end
points of the box. -/
theorem exists_corner_max (φ : (κ → ℝ) →ₗ[ℝ] ℝ) {lo hi : κ → ℝ} (h : lo ≤ hi) :
    ∃ z ∈ Set.Icc lo hi, (∀ c, z c = lo c ∨ z c = hi c) ∧ ∀ x ∈ Set.Icc lo hi, φ x ≤ φ z := by
  refine ⟨corner (coeffs φ) lo hi, corner_mem h, fun c => ?_, fun x hx => linear_le_corner φ hx⟩
  simp only [corner]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The tangent at a centre, on a box.** A function concave on a set containing the box, with
derivative `g` at a centre `x` of that set, is bounded on the box by the tangent at the corner of `g`. -/
theorem concave_le_corner {s : Set (κ → ℝ)} {f : (κ → ℝ) → ℝ} (hf : ConcaveOn ℝ s f) {lo hi x : κ → ℝ}
    (hbox : Set.Icc lo hi ⊆ s) (hx : x ∈ s) {g : (κ → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt f g x)
    {y : κ → ℝ} (hy : y ∈ Set.Icc lo hi) :
    f y ≤ f x + g (corner (coeffs (g : (κ → ℝ) →ₗ[ℝ] ℝ)) lo hi - x) := by
  have h1 := tangent_le hf hx (hbox hy) hg
  have h2 := linear_le_corner (g : (κ → ℝ) →ₗ[ℝ] ℝ) hy
  simp only [ContinuousLinearMap.coe_coe] at h2
  rw [map_sub] at h1 ⊢
  linarith

end Corner

/-! ## Finite sums of concave functions -/

theorem concaveOn_sum {E α : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    (t : Finset α) {f : α → E → ℝ} (h : ∀ a ∈ t, ConcaveOn ℝ s (f a)) :
    ConcaveOn ℝ s (fun x => ∑ a ∈ t, f a x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using concaveOn_const (0 : ℝ) hs
  | insert a t ha ih =>
    have h1 := (h a (mem_insert_self _ _)).add (ih fun b hb => h b (mem_insert_of_mem hb))
    convert h1 using 1
    funext x
    simp [sum_insert ha]

/-! ## Entropy in bits and its perspective -/

/-- The entropy term `-x log₂ x`. -/
noncomputable def ent (x : ℝ) : ℝ := negMulLog x / log 2

theorem log_two_pos' : 0 < log (2 : ℝ) := log_pos (by norm_num)

theorem concaveOn_ent : ConcaveOn ℝ (Set.Ici (0 : ℝ)) ent := by
  have h := concaveOn_negMulLog.smul (inv_nonneg.mpr log_two_pos'.le)
  convert h using 1
  funext x
  simp [ent, div_eq_inv_mul]

/-- The perspective of the entropy term: `A ent (a / A)`. -/
noncomputable def persp (a A : ℝ) : ℝ := A * ent (a / A)

theorem persp_smul {t : ℝ} (a A : ℝ) (ht : 0 ≤ t) : persp (t * a) (t * A) = t * persp a A := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [persp]
  · unfold persp
    rw [mul_div_mul_left _ _ ht.ne']
    ring

theorem persp_zero_left (A : ℝ) (hA : A = 0) : persp 0 A = 0 := by
  simp [persp, hA]

/-- **The log-sum inequality.** The perspective is superadditive on `0 ≤ a ≤ A`. -/
theorem persp_add_le {a A b B : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B) :
    persp a A + persp b B ≤ persp (a + b) (A + B) := by
  rcases (ha.trans haA).eq_or_lt with hA | hA
  · have ha0 : a = 0 := le_antisymm (hA ▸ haA) ha
    subst ha0
    rw [← hA]
    simp [persp]
  rcases (hb.trans hbB).eq_or_lt with hB | hB
  · have hb0 : b = 0 := le_antisymm (hB ▸ hbB) hb
    subst hb0
    rw [← hB]
    simp [persp]
  have hAB : 0 < A + B := by linarith
  have hα : 0 ≤ A / (A + B) := by positivity
  have hβ : 0 ≤ B / (A + B) := by positivity
  have hsum : A / (A + B) + B / (A + B) = 1 := by field_simp
  have h1 := concaveOn_ent.2 (x := a / A) (y := b / B) (Set.mem_Ici.mpr (by positivity))
    (Set.mem_Ici.mpr (by positivity)) hα hβ hsum
  have hmix : (A / (A + B)) • (a / A) + (B / (A + B)) • (b / B) = (a + b) / (A + B) := by
    simp only [smul_eq_mul]
    field_simp
  rw [hmix] at h1
  simp only [smul_eq_mul] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hAB.le
  unfold persp
  have h3 : (A + B) * (A / (A + B) * ent (a / A) + B / (A + B) * ent (b / B))
      = A * ent (a / A) + B * ent (b / B) := by
    field_simp
  linarith

/-- The perspective composed with a pair of linear maps is concave. -/
theorem concaveOn_persp {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    (P Q : E →ₗ[ℝ] ℝ) (h : ∀ x ∈ s, 0 ≤ P x ∧ P x ≤ Q x) :
    ConcaveOn ℝ s (fun x => persp (P x) (Q x)) := by
  refine ⟨hs, fun x hx y hy α β hα hβ _ => ?_⟩
  obtain ⟨h1, h2⟩ := h x hx
  obtain ⟨h3, h4⟩ := h y hy
  simp only [smul_eq_mul, map_add, map_smul]
  have h5 := persp_add_le (mul_nonneg hα h1) (mul_le_mul_of_nonneg_left h2 hα)
    (mul_nonneg hβ h3) (mul_le_mul_of_nonneg_left h4 hβ)
  rwa [persp_smul _ _ hα, persp_smul _ _ hβ] at h5

theorem persp_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    persp p q = ent p + p * log q / log 2 := by
  have h : q * (p / q) = p := by field_simp
  rcases hp.eq_or_lt with rfl | hp
  · simp [persp, ent, negMulLog]
  · unfold persp ent negMulLog
    rw [log_div hp.ne' hq.ne']
    calc q * (-(p / q) * (log p - log q) / log 2)
        = -(q * (p / q)) * (log p - log q) / log 2 := by ring
      _ = -p * log p / log 2 + p * log q / log 2 := by
        rw [h]
        ring

/-- The sum of the perspectives over `s` with common `q = ∑_s p_s` is `∑_s ent p_s - ent q`. -/
theorem sum_persp {γ : Type*} (t : Finset γ) (P : γ → ℝ) (hP : ∀ s ∈ t, 0 ≤ P s) :
    ∑ s ∈ t, persp (P s) (∑ s ∈ t, P s) = ∑ s ∈ t, ent (P s) - ent (∑ s ∈ t, P s) := by
  rcases (sum_nonneg hP).eq_or_lt with hq0 | hq0
  · have hzero : ∀ s ∈ t, P s = 0 := (sum_eq_zero_iff_of_nonneg hP).mp hq0.symm
    have e1 : ∀ s ∈ t, ent (P s) = 0 := fun s hs => by simp [hzero s hs, ent]
    rw [← hq0, sum_eq_zero e1]
    simp [persp, ent]
  · have hterm : ∀ s ∈ t, persp (P s) (∑ s ∈ t, P s)
        = ent (P s) + P s * log (∑ s ∈ t, P s) / log 2 := fun s hs => persp_eq (hP s hs) hq0
    rw [sum_congr rfl hterm, sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    unfold ent negMulLog
    ring

/-! ## The fixed kernel -/

section Kernel

variable {κ Lab β γ : Type*} [Fintype κ] [Fintype Lab] [Fintype β] [Fintype γ] [DecidableEq γ]

/-- The profiles: the nonnegative vectors on the values. The simplex and its boxes lie inside. -/
def profiles (κ : Type*) : Set (κ → ℝ) := {π | ∀ c, 0 ≤ π c}

omit [Fintype κ] in
theorem convex_profiles : Convex ℝ (profiles κ) := by
  intro x hx y hy a b ha hb _
  show ∀ c, 0 ≤ (a • x + b • y) c
  intro c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx c)) (mul_nonneg hb (hy c))

/-- The linear form `π ↦ ∑_c w_c π_c`. -/
noncomputable def formOf (w : κ → ℝ) : (κ → ℝ) →ₗ[ℝ] ℝ :=
  ∑ c, w c • LinearMap.proj c

omit [Fintype Lab] [Fintype β] [Fintype γ] [DecidableEq γ] in
theorem formOf_apply (w π : κ → ℝ) : formOf w π = ∑ c, π c * w c := by
  simp [formOf, LinearMap.sum_apply, mul_comm]

/-- The mass of the label `l` given `c`. -/
noncomputable def labGiven (W : κ → Lab → β → ℝ) (c : κ) (l : Lab) : ℝ := ∑ b, W c l b

/-- The mass of the pair `(l, s)` given `c`, for `f b = s`. -/
noncomputable def jointGiven (W : κ → Lab → β → ℝ) (f : β → γ) (c : κ) (l : Lab) (s : γ) : ℝ :=
  ∑ b with f b = s, W c l b

/-- The law of the label under the profile `π`: `q(l) = ∑_c π_c W(l | c)`. -/
noncomputable def labLaw (W : κ → Lab → β → ℝ) (l : Lab) : (κ → ℝ) →ₗ[ℝ] ℝ :=
  formOf fun c => labGiven W c l

/-- The law of `(l, s)` under the profile `π`. -/
noncomputable def jointLaw (W : κ → Lab → β → ℝ) (f : β → γ) (l : Lab) (s : γ) : (κ → ℝ) →ₗ[ℝ] ℝ :=
  formOf fun c => jointGiven W f c l s

/-- `H(L)` under the profile `π`. -/
noncomputable def entL (W : κ → Lab → β → ℝ) (π : κ → ℝ) : ℝ := ∑ l, ent (labLaw W l π)

/-- `H(L | c)` for the fixed kernel. -/
noncomputable def entLgiven (W : κ → Lab → β → ℝ) (c : κ) : ℝ := ∑ l, ent (labGiven W c l)

/-- `H(f, L)` under the profile `π`. -/
noncomputable def entJoint (W : κ → Lab → β → ℝ) (f : β → γ) (π : κ → ℝ) : ℝ :=
  ∑ l, ∑ s, ent (jointLaw W f l s π)

/-- `H(f | L) = H(f, L) - H(L)`, the exponent of a list, with `f` the first or second symbol. -/
noncomputable def listEnt (W : κ → Lab → β → ℝ) (f : β → γ) (π : κ → ℝ) : ℝ :=
  entJoint W f π - entL W π

/-- `a = H(L) - ∑_c π_c H(L | c)`. -/
noncomputable def aExp (W : κ → Lab → β → ℝ) (π : κ → ℝ) : ℝ :=
  entL W π - ∑ c, π c * entLgiven W c

/-- `H(x, y | L, c) = H(L, x, y | c) - H(L | c)` for the fixed kernel. -/
noncomputable def a₀Given (W : κ → Lab → β → ℝ) (c : κ) : ℝ :=
  ∑ l, ∑ b, ent (W c l b) - entLgiven W c

/-- `a₀ = ∑_c π_c H(x, y | L, c)`. -/
noncomputable def a₀Exp (W : κ → Lab → β → ℝ) (π : κ → ℝ) : ℝ := ∑ c, π c * a₀Given W c

omit [Fintype γ] [DecidableEq γ] in
/-- **`a₀` is linear in the profile.** -/
theorem a₀Exp_linear (W : κ → Lab → β → ℝ) : a₀Exp W = formOf (a₀Given W) := by
  funext π
  rw [formOf_apply, a₀Exp]

/-- The size of the varying classes: `|F| / n = ∑_c π_c w_c` is linear in the profile, for `w_c` the
mass of the varying classes given `c`. -/
theorem freeFrac_le_corner [DecidableEq κ] (w : κ → ℝ) {lo hi π : κ → ℝ} (hπ : π ∈ Set.Icc lo hi) :
    ∑ c, w c * π c ≤ ∑ c, w c * corner w lo hi c :=
  sum_le_corner hπ

variable {W : κ → Lab → β → ℝ}

omit [Fintype Lab] [Fintype γ] [DecidableEq γ] in
theorem labLaw_nonneg (hW : ∀ c l b, 0 ≤ W c l b) (l : Lab) {π : κ → ℝ} (hπ : π ∈ profiles κ) :
    0 ≤ labLaw W l π := by
  rw [labLaw, formOf_apply]
  exact sum_nonneg fun c _ => mul_nonneg (hπ c) (sum_nonneg fun b _ => hW c l b)

omit [Fintype Lab] [Fintype γ] in
theorem jointLaw_nonneg (hW : ∀ c l b, 0 ≤ W c l b) (f : β → γ) (l : Lab) (s : γ) {π : κ → ℝ}
    (hπ : π ∈ profiles κ) : 0 ≤ jointLaw W f l s π := by
  rw [jointLaw, formOf_apply]
  exact sum_nonneg fun c _ => mul_nonneg (hπ c) (sum_nonneg fun b _ => hW c l b)

omit [Fintype Lab] in
/-- The label law is the sum of the joint law over the symbols. -/
theorem sum_jointLaw (f : β → γ) (l : Lab) (π : κ → ℝ) :
    ∑ s, jointLaw W f l s π = labLaw W l π := by
  simp only [jointLaw, labLaw, formOf_apply, jointGiven, labGiven]
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [← mul_sum]
  congr 1
  exact sum_fiberwise _ _ _

omit [Fintype γ] [DecidableEq γ] in
/-- **`H(L)` is concave in the profile**, as `negMulLog` of a linear map. -/
theorem entL_concave (hW : ∀ c l b, 0 ≤ W c l b) : ConcaveOn ℝ (profiles κ) (entL W) := by
  refine concaveOn_sum convex_profiles univ fun l _ => ?_
  have h := concaveOn_ent.comp_linearMap (labLaw W l)
  exact h.subset (fun π hπ => labLaw_nonneg hW l hπ) convex_profiles

omit [Fintype γ] [DecidableEq γ] in
/-- **`a = H(L) - ∑_c π_c H(L | c)` is concave in the profile.** -/
theorem aExp_concave (hW : ∀ c l b, 0 ≤ W c l b) : ConcaveOn ℝ (profiles κ) (aExp W) := by
  have h := (entL_concave hW).add
    ((formOf fun c => - entLgiven W c).concaveOn convex_profiles)
  convert h using 1
  funext π
  simp only [aExp, Pi.add_apply, formOf_apply, mul_neg, sum_neg_distrib]
  ring

/-- `H(f | L)` as the sum of perspectives, on the profiles. -/
theorem listEnt_eq_persp (hW : ∀ c l b, 0 ≤ W c l b) (f : β → γ) {π : κ → ℝ} (hπ : π ∈ profiles κ) :
    listEnt W f π = ∑ l, ∑ s, persp (jointLaw W f l s π) (labLaw W l π) := by
  unfold listEnt entJoint entL
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [← sum_jointLaw f l π]
  exact (sum_persp univ _ fun s _ => jointLaw_nonneg hW f l s hπ).symm

/-- **`H(f | L)` is concave in the profile.** The joint law of `(l, s)` is linear in the profile, and
the conditional entropy is a sum of perspectives of `negMulLog`. -/
theorem listEnt_concave (hW : ∀ c l b, 0 ≤ W c l b) (f : β → γ) :
    ConcaveOn ℝ (profiles κ) (listEnt W f) := by
  have h : ConcaveOn ℝ (profiles κ)
      (fun π => ∑ l, ∑ s, persp (jointLaw W f l s π) (labLaw W l π)) := by
    refine concaveOn_sum convex_profiles univ fun l _ => ?_
    refine concaveOn_sum convex_profiles univ fun s _ => ?_
    refine concaveOn_persp convex_profiles _ _ fun π hπ => ⟨jointLaw_nonneg hW f l s hπ, ?_⟩
    rw [← sum_jointLaw f l π]
    exact single_le_sum (fun s _ => jointLaw_nonneg hW f l s hπ) (mem_univ s)
  refine ⟨h.1, fun x hx y hy α β' hα hβ hαβ => ?_⟩
  have h1 := h.2 hx hy hα hβ hαβ
  rwa [listEnt_eq_persp hW f hx, listEnt_eq_persp hW f hy,
    listEnt_eq_persp hW f (convex_profiles hx hy hα hβ hαβ)]

/-! ## The four terms -/

omit [Fintype γ] [DecidableEq γ] in
/-- The first term `a / 2 + a₀ + σ` is concave. -/
theorem term_table_concave (hW : ∀ c l b, 0 ≤ W c l b) (σ : ℝ) :
    ConcaveOn ℝ (profiles κ) (fun π => aExp W π / 2 + a₀Exp W π + σ) := by
  have h := (((aExp_concave hW).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    ((formOf (a₀Given W)).concaveOn convex_profiles)).add (concaveOn_const σ convex_profiles)
  convert h using 1
  funext π
  simp only [Pi.add_apply, smul_eq_mul, a₀Exp_linear W]
  ring

/-- The second and third term `a / 2 + σ / 2 + (2/3)(u_f - a₀ - σ)` are concave, with `u_f` the list
exponent of `f`. -/
theorem term_search_concave (hW : ∀ c l b, 0 ≤ W c l b) (f : β → γ) (σ : ℝ) :
    ConcaveOn ℝ (profiles κ)
      (fun π => aExp W π / 2 + σ / 2 + (2 / 3) * (listEnt W f π - a₀Exp W π - σ)) := by
  have h := (((aExp_concave hW).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    ((listEnt_concave hW f).smul (by norm_num : (0 : ℝ) ≤ 2 / 3))).add
    (((formOf fun c => -(2 / 3) * a₀Given W c).concaveOn convex_profiles).add
      (concaveOn_const (σ / 2 - (2 / 3) * σ) convex_profiles))
  convert h using 1
  funext π
  simp only [Pi.add_apply, smul_eq_mul, a₀Exp, formOf_apply]
  have : ∑ c, π c * (-(2 / 3) * a₀Given W c) = -(2 / 3) * ∑ c, π c * a₀Given W c := by
    rw [mul_sum]
    exact sum_congr rfl fun c _ => by ring
  rw [this]
  ring

omit [Fintype γ] [DecidableEq γ] in
/-- The fourth term `a / 2 + σ / 2` is concave. -/
theorem term_half_concave (hW : ∀ c l b, 0 ≤ W c l b) (σ : ℝ) :
    ConcaveOn ℝ (profiles κ) (fun π => aExp W π / 2 + σ / 2) := by
  have h := ((aExp_concave hW).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    (concaveOn_const (σ / 2) convex_profiles)
  convert h using 1
  funext π
  simp only [Pi.add_apply, smul_eq_mul]
  ring

end Kernel

end SubsetBalancing
