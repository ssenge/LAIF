import Mathlib

/-!
# Error bound of a banded mean estimator

A real random variable `x` on a finite probability space is split into a central band
`|x| ≤ t 0`, outer bands `t j < |x| ≤ t (j + 1)` for `j < n`, and a tail `|x| > t n`. The mean of
each band is read off from one amplitude estimation run, which ends with an angle interval of
width at most `η` around the true angle. This file proves the deterministic error bound that holds
when every run succeeds:

* `ae_error`: one run, error at most `η / 2`, and at most `√a · η + η² / 2` for `a = sin² θ`;
* `mean_decomp`: the mean of `x` is the sum of the band means and the tail mean;
* `estimate_error`: the error of the combined estimate;
* `outer_sum_le`, `tail_le`, `budget_le`: the bounds through the second moment of `x`;
* `estimator_error`: the combined bound.
-/

open Real Finset

namespace MeanEstimation

noncomputable section

/-! ## One amplitude estimation run -/

lemma sin_sq_sub_sin_sq (u l : ℝ) : sin u ^ 2 - sin l ^ 2 = sin (u + l) * sin (u - l) := by
  rw [sin_add, sin_sub]
  have hu := sin_sq_add_cos_sq u
  have hl := sin_sq_add_cos_sq l
  linear_combination (sin l ^ 2) * hu - (sin u ^ 2) * hl

lemma sin_sq_le_sin_sq {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    sin x ^ 2 ≤ sin y ^ 2 := by
  have h1 : sin x ≤ sin y :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hy hxy
  have h0 : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx (by linarith [pi_pos])
  nlinarith

/-- An angle interval `[l, u] ⊆ [0, π/2]` of width at most `η` that contains `θ` gives the
midpoint estimate `(sin² l + sin² u) / 2` of `a = sin² θ` with error at most `η / 2` and at most
`sin θ · η + η² / 2`, where `sin θ = √a`. -/
theorem ae_error {l u θ η : ℝ} (hl : 0 ≤ l) (hlθ : l ≤ θ) (hθu : θ ≤ u) (hu : u ≤ π / 2)
    (hw : u - l ≤ η) :
    |(sin l ^ 2 + sin u ^ 2) / 2 - sin θ ^ 2| ≤ η / 2 ∧
      |(sin l ^ 2 + sin u ^ 2) / 2 - sin θ ^ 2| ≤ sin θ * η + η ^ 2 / 2 := by
  have hθ0 : 0 ≤ θ := hl.trans hlθ
  have h1 := sin_sq_le_sin_sq hl hlθ (hθu.trans hu)
  have h2 := sin_sq_le_sin_sq hθ0 hθu hu
  have hmid : |(sin l ^ 2 + sin u ^ 2) / 2 - sin θ ^ 2| ≤ (sin u ^ 2 - sin l ^ 2) / 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [sin_sq_sub_sin_sq] at hmid
  have hd0 : 0 ≤ u - l := by linarith
  have hη : 0 ≤ η := hd0.trans hw
  have hsd0 : 0 ≤ sin (u - l) := sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [pi_pos])
  have hsd : sin (u - l) ≤ η := (sin_le hd0).trans hw
  have hs0 : 0 ≤ sin (u + l) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : sin (u + l) ≤ 1 := sin_le_one _
  have hsθ : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos])
  have hs2 : sin (u + l) ≤ 2 * sin θ + η := by
    have h := abs_sin_sub_sin_le (u + l) (2 * θ)
    have h' : |u + l - 2 * θ| ≤ η := by rw [abs_le]; constructor <;> linarith
    have h2θ : sin (2 * θ) ≤ 2 * sin θ := by
      rw [sin_two_mul]; nlinarith [cos_le_one θ]
    have := (abs_le.mp (h.trans h')).2
    linarith
  have p1 : sin (u + l) * sin (u - l) ≤ 1 * η :=
    mul_le_mul hs1 hsd hsd0 zero_le_one
  have p2 : sin (u + l) * sin (u - l) ≤ (2 * sin θ + η) * η :=
    mul_le_mul hs2 hsd hsd0 (by linarith)
  constructor <;> nlinarith

/-- The second bound of `ae_error` in terms of `a = sin² θ`. -/
theorem ae_error_sqrt {l u θ η : ℝ} (hl : 0 ≤ l) (hlθ : l ≤ θ) (hθu : θ ≤ u) (hu : u ≤ π / 2)
    (hw : u - l ≤ η) :
    |(sin l ^ 2 + sin u ^ 2) / 2 - sin θ ^ 2| ≤ √(sin θ ^ 2) * η + η ^ 2 / 2 := by
  have hθ0 : 0 ≤ θ := hl.trans hlθ
  rw [sqrt_sq (sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos]))]
  exact (ae_error hl hlθ hθu hu hw).2

/-! ## Bands on a finite probability space -/

variable {Ω : Type*} [Fintype Ω]

/-- Expectation with weights `p`. -/
def E (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

lemma E_add (p f g : Ω → ℝ) : E p (fun ω => f ω + g ω) = E p f + E p g := by
  simp [E, mul_add, sum_add_distrib]

lemma E_le (p f g : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (h : ∀ ω, f ω ≤ g ω) : E p f ≤ E p g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hp ω)

/-- The outer bands partition `t 0 < |x| ≤ t n`, for monotone thresholds. -/
lemma band_sum (t : ℕ → ℝ) (ht : Monotone t) (x g : ℝ) (n : ℕ) :
    ∑ j ∈ range n, (if t j < |x| ∧ |x| ≤ t (j + 1) then g else 0) =
      if t 0 < |x| ∧ |x| ≤ t n then g else 0 := by
  have key : ∀ a b : ℝ, (if a < |x| ∧ |x| ≤ b then g else 0) =
      (Set.Ioc a b).indicator (fun _ => g) |x| := by
    intro a b; simp [Set.indicator_apply, Set.mem_Ioc]
  simp only [key]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, ← Set.Ioc_union_Ioc_eq_Ioc (ht (Nat.zero_le n)) (ht (Nat.le_succ n)),
      Set.indicator_union_of_disjoint (Set.Ioc_disjoint_Ioc_of_le le_rfl)]

/-- Band variables. `W` is the central band, shifted into `[0, 1]`; `Z j` is the outer band `j`,
signed and scaled by `t (j + 1)`; `tail` is the part beyond `t n`. -/
def W (t : ℕ → ℝ) (x : ℝ) : ℝ := (1 + if |x| ≤ t 0 then x / t 0 else 0) / 2
def Zp (t : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ := if t j < x ∧ x ≤ t (j + 1) then x / t (j + 1) else 0
def Zm (t : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ := Zp t j (-x)
def tail (t : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ := if t n < |x| then x else 0

lemma Zp_sub_Zm (t : ℕ → ℝ) (ht0 : 0 < t 0) (ht : Monotone t) (j : ℕ) (x : ℝ) :
    t (j + 1) * (Zp t j x - Zm t j x) = if t j < |x| ∧ |x| ≤ t (j + 1) then x else 0 := by
  have hpos : 0 < t (j + 1) := ht0.trans_le (ht (Nat.zero_le _))
  have hpj : 0 < t j := ht0.trans_le (ht (Nat.zero_le _))
  unfold Zm Zp
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have : ¬ (t j < -x ∧ -x ≤ t (j + 1)) := fun h => by linarith [h.1]
    rw [if_neg this]
    split_ifs
    · field_simp; ring
    · simp
  · rw [abs_of_neg hx]
    have : ¬ (t j < x ∧ x ≤ t (j + 1)) := fun h => by linarith [h.1]
    rw [if_neg this]
    split_ifs
    · field_simp; ring
    · simp

/-- Pointwise decomposition of `x` into its bands. -/
lemma point_decomp (t : ℕ → ℝ) (ht0 : 0 < t 0) (ht : Monotone t) (n : ℕ) (x : ℝ) :
    x = 2 * t 0 * (W t x - 1 / 2) + ∑ j ∈ range n, t (j + 1) * (Zp t j x - Zm t j x) +
      tail t n x := by
  simp only [Zp_sub_Zm t ht0 ht, band_sum t ht x x n]
  unfold W tail
  have h0n : t 0 ≤ t n := ht (Nat.zero_le n)
  have hc : 2 * t 0 * ((1 + if |x| ≤ t 0 then x / t 0 else 0) / 2 - 1 / 2) =
      if |x| ≤ t 0 then x else 0 := by
    split_ifs
    · field_simp; ring
    · simp
  rw [hc]
  by_cases h1 : |x| ≤ t 0
  · have h2 : ¬ (t 0 < |x| ∧ |x| ≤ t n) := fun h => by linarith [h.1]
    have h3 : ¬ t n < |x| := by linarith
    simp [h1, h2, h3]
  · by_cases h2 : |x| ≤ t n
    · have h3 : ¬ t n < |x| := by linarith
      have h4 : t 0 < |x| ∧ |x| ≤ t n := ⟨by linarith, h2⟩
      simp [h1, h4, h3]
    · have h4 : ¬ (t 0 < |x| ∧ |x| ≤ t n) := fun h => h2 h.2
      have h3 : t n < |x| := by linarith
      simp [h1, h4, h3]

/-- The mean of `x` is the sum of the band means and the tail mean. -/
theorem mean_decomp (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) (t : ℕ → ℝ) (ht0 : 0 < t 0)
    (ht : Monotone t) (n : ℕ) :
    E p X = 2 * t 0 * (E p (fun ω => W t (X ω)) - 1 / 2) +
      ∑ j ∈ range n, t (j + 1) * (E p (fun ω => Zp t j (X ω)) - E p (fun ω => Zm t j (X ω))) +
      E p (fun ω => tail t n (X ω)) := by
  have hpt : ∀ ω, p ω * X ω = 2 * t 0 * (p ω * W t (X ω)) - t 0 * p ω +
      ∑ j ∈ range n, t (j + 1) * (p ω * Zp t j (X ω) - p ω * Zm t j (X ω)) +
      p ω * tail t n (X ω) := by
    intro ω
    conv_lhs => rw [point_decomp t ht0 ht n (X ω)]
    rw [mul_add, mul_add, mul_sum]
    have : ∀ j ∈ range n, p ω * (t (j + 1) * (Zp t j (X ω) - Zm t j (X ω))) =
        t (j + 1) * (p ω * Zp t j (X ω) - p ω * Zm t j (X ω)) := fun j _ => by ring
    rw [sum_congr rfl this]; ring
  have hA : ∑ ω, 2 * t 0 * (p ω * W t (X ω)) = 2 * t 0 * ∑ ω, p ω * W t (X ω) := by
    rw [mul_sum]
  have hB : ∑ ω, t 0 * p ω = t 0 := by rw [← mul_sum, hp1, mul_one]
  have hC : ∑ ω, ∑ j ∈ range n, t (j + 1) * (p ω * Zp t j (X ω) - p ω * Zm t j (X ω)) =
      ∑ j ∈ range n, t (j + 1) * (∑ ω, p ω * Zp t j (X ω) - ∑ ω, p ω * Zm t j (X ω)) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun ω _ => by ring
  unfold E
  rw [sum_congr rfl fun ω _ => hpt ω, sum_add_distrib, sum_add_distrib, sum_sub_distrib]
  linarith [hA, hB, hC]

/-! ## Error of the combined estimate -/

lemma abs_sum_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, |f i| ≤ g i) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i :=
  (abs_sum_le_sum_abs f s).trans (sum_le_sum h)

/-- If every band mean is estimated within the given errors, the estimate of the mean of `x`
without its tail is within the weighted sum of the errors. -/
theorem estimate_error (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) (t : ℕ → ℝ) (ht0 : 0 < t 0)
    (ht : Monotone t) (n : ℕ) (aW eW : ℝ) (ap am ep em : ℕ → ℝ)
    (hW : |aW - E p (fun ω => W t (X ω))| ≤ eW)
    (hp : ∀ j ∈ range n, |ap j - E p (fun ω => Zp t j (X ω))| ≤ ep j)
    (hm : ∀ j ∈ range n, |am j - E p (fun ω => Zm t j (X ω))| ≤ em j) :
    |2 * t 0 * (aW - 1 / 2) + ∑ j ∈ range n, t (j + 1) * (ap j - am j) - E p X| ≤
      2 * t 0 * eW + ∑ j ∈ range n, t (j + 1) * (ep j + em j) +
        |E p (fun ω => tail t n (X ω))| := by
  rw [mean_decomp p hp1 X t ht0 ht n]
  have hpos : ∀ j, 0 < t (j + 1) := fun j => ht0.trans_le (ht (Nat.zero_le _))
  have hsum : |∑ j ∈ range n, t (j + 1) * (ap j - am j) - ∑ j ∈ range n, t (j + 1) *
      (E p (fun ω => Zp t j (X ω)) - E p (fun ω => Zm t j (X ω)))| ≤
      ∑ j ∈ range n, t (j + 1) * (ep j + em j) := by
    rw [← sum_sub_distrib]
    refine abs_sum_le_sum _ _ _ fun j hj => ?_
    rw [← mul_sub, abs_mul, abs_of_pos (hpos j)]
    refine mul_le_mul_of_nonneg_left ?_ (hpos j).le
    have := abs_sub (ap j - E p (fun ω => Zp t j (X ω))) (am j - E p (fun ω => Zm t j (X ω)))
    calc |ap j - am j - (E p (fun ω => Zp t j (X ω)) - E p (fun ω => Zm t j (X ω)))|
        = |(ap j - E p (fun ω => Zp t j (X ω))) - (am j - E p (fun ω => Zm t j (X ω)))| := by
          ring_nf
      _ ≤ ep j + em j := this.trans (add_le_add (hp j hj) (hm j hj))
  have hW' : |2 * t 0 * (aW - 1 / 2) - 2 * t 0 * (E p (fun ω => W t (X ω)) - 1 / 2)| ≤
      2 * t 0 * eW := by
    rw [← mul_sub, abs_mul, abs_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left (by simpa using hW) (by linarith)
  have key := abs_add_three (2 * t 0 * (aW - 1 / 2) - 2 * t 0 * (E p (fun ω => W t (X ω)) - 1 / 2))
    (∑ j ∈ range n, t (j + 1) * (ap j - am j) - ∑ j ∈ range n, t (j + 1) *
      (E p (fun ω => Zp t j (X ω)) - E p (fun ω => Zm t j (X ω))))
    (-E p (fun ω => tail t n (X ω)))
  rw [abs_neg] at key
  calc _ = |(2 * t 0 * (aW - 1 / 2) - 2 * t 0 * (E p (fun ω => W t (X ω)) - 1 / 2)) +
        (∑ j ∈ range n, t (j + 1) * (ap j - am j) - ∑ j ∈ range n, t (j + 1) *
          (E p (fun ω => Zp t j (X ω)) - E p (fun ω => Zm t j (X ω)))) +
        -E p (fun ω => tail t n (X ω))| := by ring_nf
    _ ≤ _ := key.trans (by linarith)

/-! ## Bounds through the second moment -/

/-- On the band `t j < x ≤ t (j + 1)`, `x / t (j + 1) ≤ x² / (t j · t (j + 1))`. -/
lemma Zp_le (t : ℕ → ℝ) (ht0 : 0 < t 0) (ht : Monotone t) (j : ℕ) (x : ℝ) :
    Zp t j x ≤ (if t j < x ∧ x ≤ t (j + 1) then x ^ 2 else 0) / (t j * t (j + 1)) := by
  have hpj : 0 < t j := ht0.trans_le (ht (Nat.zero_le _))
  have hpos : 0 < t (j + 1) := ht0.trans_le (ht (Nat.zero_le _))
  unfold Zp
  split_ifs with h
  · rw [div_le_div_iff₀ hpos (mul_pos hpj hpos)]
    have hx : x * t j ≤ x ^ 2 := by nlinarith [h.1]
    calc x * (t j * t (j + 1)) = (x * t j) * t (j + 1) := by ring
      _ ≤ x ^ 2 * t (j + 1) := mul_le_mul_of_nonneg_right hx hpos.le
  · simp

lemma Zp_nonneg (t : ℕ → ℝ) (ht0 : 0 < t 0) (ht : Monotone t) (j : ℕ) (x : ℝ) :
    0 ≤ Zp t j x := by
  have hpj : 0 < t j := ht0.trans_le (ht (Nat.zero_le _))
  have hpos : 0 < t (j + 1) := ht0.trans_le (ht (Nat.zero_le _))
  unfold Zp; split_ifs with h
  · exact div_nonneg (by linarith [h.1]) hpos.le
  · exact le_rfl

/-- `t (j + 1) √a ≤ √(ρ m)` when `a ≤ m / (t j · t (j + 1))` and `t (j + 1) ≤ ρ t j`. -/
lemma scaled_sqrt_le {a m tj tj1 ρ : ℝ} (htj : 0 < tj) (htj1 : 0 < tj1) (hρ : tj1 ≤ ρ * tj)
    (ha : a ≤ m / (tj * tj1)) (hm : 0 ≤ m) :
    tj1 * √a ≤ √(ρ * m) := by
  rw [← sqrt_sq htj1.le, ← sqrt_mul (sq_nonneg _)]
  apply sqrt_le_sqrt
  calc tj1 ^ 2 * a ≤ tj1 ^ 2 * (m / (tj * tj1)) :=
        mul_le_mul_of_nonneg_left ha (sq_nonneg _)
    _ = tj1 / tj * m := by field_simp
    _ ≤ ρ * m := by
        apply mul_le_mul_of_nonneg_right _ hm
        rw [div_le_iff₀ htj]; exact hρ

/-- The tail mean is at most the tail second moment over `t n`. -/
lemma tail_le (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ) (t : ℕ → ℝ) (ht0 : 0 < t 0)
    (ht : Monotone t) (n : ℕ) :
    |E p (fun ω => tail t n (X ω))| ≤
      E p (fun ω => if t n < |X ω| then X ω ^ 2 else 0) / t n := by
  have htn : 0 < t n := ht0.trans_le (ht (Nat.zero_le _))
  simp only [E]
  rw [sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
  rw [abs_mul, abs_of_nonneg (hp ω), mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hp ω)
  unfold tail; split_ifs with h
  · rw [le_div_iff₀ htn, ← sq_abs (X ω)]; nlinarith [abs_nonneg (X ω)]
  · simp

lemma E_sum_add (p : Ω → ℝ) (s : Finset ℕ) (A B : ℕ → Ω → ℝ) (C : Ω → ℝ) :
    ∑ j ∈ s, (E p (A j) + E p (B j)) + E p C =
      E p (fun ω => ∑ j ∈ s, (A j ω + B j ω) + C ω) := by
  unfold E
  simp only [mul_add, mul_sum, sum_add_distrib]
  congr 1; congr 1 <;> exact sum_comm

/-- The bands and the tail together use at most the second moment of `x`. -/
lemma budget_le (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ) (t : ℕ → ℝ) (ht0 : 0 < t 0)
    (ht : Monotone t) (n : ℕ) :
    ∑ j ∈ range n, (E p (fun ω => if t j < X ω ∧ X ω ≤ t (j + 1) then X ω ^ 2 else 0) +
        E p (fun ω => if t j < -X ω ∧ -X ω ≤ t (j + 1) then (-X ω) ^ 2 else 0)) +
      E p (fun ω => if t n < |X ω| then X ω ^ 2 else 0) ≤ E p (fun ω => X ω ^ 2) := by
  have hpt : ∀ x : ℝ, ∑ j ∈ range n, ((if t j < x ∧ x ≤ t (j + 1) then x ^ 2 else 0) +
      (if t j < -x ∧ -x ≤ t (j + 1) then (-x) ^ 2 else 0)) + (if t n < |x| then x ^ 2 else 0)
      ≤ x ^ 2 := by
    intro x
    have hsplit : ∀ j, ((if t j < x ∧ x ≤ t (j + 1) then x ^ 2 else 0) +
        (if t j < -x ∧ -x ≤ t (j + 1) then (-x) ^ 2 else 0)) =
        if t j < |x| ∧ |x| ≤ t (j + 1) then x ^ 2 else 0 := by
      intro j
      have hpj : 0 < t j := ht0.trans_le (ht (Nat.zero_le _))
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        have : ¬ (t j < -x ∧ -x ≤ t (j + 1)) := fun h => by linarith [h.1]
        rw [if_neg this, add_zero]
      · rw [abs_of_neg hx]
        have : ¬ (t j < x ∧ x ≤ t (j + 1)) := fun h => by linarith [h.1]
        rw [if_neg this, zero_add, neg_sq]
    simp only [hsplit, band_sum t ht x (x ^ 2) n]
    have h0n : t 0 ≤ t n := ht (Nat.zero_le n)
    split_ifs with h1 h2 <;> first | (exfalso; linarith [h1.2]) | nlinarith [sq_nonneg x]
  calc _ = E p (fun ω => ∑ j ∈ range n,
          ((if t j < X ω ∧ X ω ≤ t (j + 1) then X ω ^ 2 else 0) +
            (if t j < -X ω ∧ -X ω ≤ t (j + 1) then (-X ω) ^ 2 else 0)) +
          (if t n < |X ω| then X ω ^ 2 else 0)) :=
        E_sum_add p (range n) (fun j ω => if t j < X ω ∧ X ω ≤ t (j + 1) then X ω ^ 2 else 0)
          (fun j ω => if t j < -X ω ∧ -X ω ≤ t (j + 1) then (-X ω) ^ 2 else 0)
          (fun ω => if t n < |X ω| then X ω ^ 2 else 0)
    _ ≤ _ := E_le p _ _ hp fun ω => hpt (X ω)

/-- Worst case over the split of the second moment between the outer bands (`M`) and the tail
(`M_T`): `√(A M) + M_T / T` is at most `√(A S)` if `S ≤ A T² / 4`, and at most `A T / 4 + S / T`
otherwise. -/
def B (A S T : ℝ) : ℝ := if S ≤ A * T ^ 2 / 4 then √(A * S) else A * T / 4 + S / T

lemma split_le {A S T M MT : ℝ} (hA : 0 ≤ A) (hT : 0 < T) (hM : 0 ≤ M) (hMT : 0 ≤ MT)
    (hS : M + MT ≤ S) : √(A * M) + MT / T ≤ B A S T := by
  have hs := sq_sqrt (mul_nonneg hA hM)
  have hs0 := sqrt_nonneg (A * M)
  unfold B
  split_ifs with h
  · rcases hA.eq_or_lt with hA0 | hApos
    · subst hA0
      have : S ≤ 0 := by simpa using h
      have : MT = 0 := by linarith
      simp [this]
    have hv := sq_sqrt (mul_nonneg hA (hM.trans (by linarith : M ≤ S)))
    have hv0 := sqrt_nonneg (A * S)
    have huv : √(A * M) ≤ √(A * S) := sqrt_le_sqrt (by nlinarith)
    have hvT : √(A * S) ≤ A * T / 2 := by
      rw [sqrt_le_left (by positivity)]; nlinarith
    -- (v - u)(v + u) = A (S - M) and v + u ≤ A T
    have key : A * (S - M) ≤ (√(A * S) - √(A * M)) * (A * T) := by
      have : (√(A * S) - √(A * M)) * (√(A * S) + √(A * M)) = A * (S - M) := by
        have e : (√(A * S) - √(A * M)) * (√(A * S) + √(A * M)) =
            √(A * S) ^ 2 - √(A * M) ^ 2 := by ring
        rw [e, hv, hs]; ring
      rw [← this]
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have : (S - M) / T ≤ √(A * S) - √(A * M) := by
      rw [div_le_iff₀ hT]
      have := key
      nlinarith
    have : MT / T ≤ (S - M) / T := div_le_div_of_nonneg_right (by linarith) hT.le
    linarith
  · -- arithmetic and geometric means
    have amgm : √(A * M) ≤ A * T / 4 + M / T := by
      rcases hA.eq_or_lt with hA0 | hApos
      · subst hA0; simp; positivity
      have h1 : A * (A * T ^ 2 / 4 + M - T * √(A * M)) = (A * T / 2 - √(A * M)) ^ 2 := by
        ring_nf; rw [hs]; ring
      have h2 : 0 ≤ A * T ^ 2 / 4 + M - T * √(A * M) := by
        by_contra hc
        push Not at hc
        have := mul_neg_of_pos_of_neg hApos hc
        nlinarith [sq_nonneg (A * T / 2 - √(A * M))]
      have : T * √(A * M) ≤ T * (A * T / 4 + M / T) := by
        have : T * (A * T / 4 + M / T) = A * T ^ 2 / 4 + M := by
          rw [mul_add, mul_div_cancel₀ _ hT.ne']; ring
        linarith
      exact le_of_mul_le_mul_left this hT
    have : MT / T ≤ (S - M) / T := div_le_div_of_nonneg_right (by linarith) hT.le
    have : M / T + (S - M) / T = S / T := by field_simp; ring
    linarith

/-- The full error bound: if the central run is within `η / 2` and every outer run is within
`√a · η + η² / 2`, then the estimate of the mean of `x` is within
`t 0 · η + B (2 n ρ η²) S (t n) + η² · Σ_j t (j + 1)`, where `S` bounds the second moment of `x`
and `t (j + 1) ≤ ρ · t j`. -/
theorem estimator_error (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ)
    (t : ℕ → ℝ) (ht0 : 0 < t 0) (ht : Monotone t) (n : ℕ) (ρ η S : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j, t (j + 1) ≤ ρ * t j) (hη : 0 ≤ η) (hS : E p (fun ω => X ω ^ 2) ≤ S)
    (aW : ℝ) (ap am : ℕ → ℝ)
    (hW : |aW - E p (fun ω => W t (X ω))| ≤ η / 2)
    (hap : ∀ j ∈ range n, |ap j - E p (fun ω => Zp t j (X ω))| ≤
      √(E p (fun ω => Zp t j (X ω))) * η + η ^ 2 / 2)
    (ham : ∀ j ∈ range n, |am j - E p (fun ω => Zm t j (X ω))| ≤
      √(E p (fun ω => Zm t j (X ω))) * η + η ^ 2 / 2) :
    |2 * t 0 * (aW - 1 / 2) + ∑ j ∈ range n, t (j + 1) * (ap j - am j) - E p X| ≤
      t 0 * η + B (2 * n * ρ * η ^ 2) S (t n) + η ^ 2 * ∑ j ∈ range n, t (j + 1) := by
  have hpos : ∀ j, 0 < t j := fun j => ht0.trans_le (ht (Nat.zero_le _))
  have h1 := estimate_error p hp1 X t ht0 ht n aW (η / 2) ap am _ _ hW hap ham
  -- second moments of the bands and the tail
  set mp : ℕ → ℝ := fun j => E p (fun ω => if t j < X ω ∧ X ω ≤ t (j + 1) then X ω ^ 2 else 0)
  set mm : ℕ → ℝ := fun j =>
    E p (fun ω => if t j < -X ω ∧ -X ω ≤ t (j + 1) then (-X ω) ^ 2 else 0)
  set MT := E p (fun ω => if t n < |X ω| then X ω ^ 2 else 0)
  have hnn : ∀ (c : Prop) [Decidable c] (y : ℝ), 0 ≤ if c then y ^ 2 else 0 := by
    intro c _ y; split_ifs <;> positivity
  have hmp0 : ∀ j, 0 ≤ mp j := fun j => sum_nonneg fun ω _ => mul_nonneg (hp ω) (hnn _ _)
  have hmm0 : ∀ j, 0 ≤ mm j := fun j => sum_nonneg fun ω _ => mul_nonneg (hp ω) (hnn _ _)
  have hMT0 : 0 ≤ MT := sum_nonneg fun ω _ => mul_nonneg (hp ω) (hnn _ _)
  have hap' : ∀ j, E p (fun ω => Zp t j (X ω)) ≤ mp j / (t j * t (j + 1)) := by
    intro j; simp only [mp, E]; rw [sum_div]
    exact sum_le_sum fun ω _ => by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (Zp_le t ht0 ht j (X ω)) (hp ω)
  have ham' : ∀ j, E p (fun ω => Zm t j (X ω)) ≤ mm j / (t j * t (j + 1)) := by
    intro j; simp only [mm, E, Zm]; rw [sum_div]
    exact sum_le_sum fun ω _ => by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (Zp_le t ht0 ht j (-X ω)) (hp ω)
  -- the outer runs
  have hout : ∑ j ∈ range n, t (j + 1) * ((√(E p (fun ω => Zp t j (X ω))) * η + η ^ 2 / 2) +
      (√(E p (fun ω => Zm t j (X ω))) * η + η ^ 2 / 2)) ≤
      √(2 * n * ρ * η ^ 2 * ∑ j ∈ range n, (mp j + mm j)) +
        η ^ 2 * ∑ j ∈ range n, t (j + 1) := by
    have e : ∀ j ∈ range n, t (j + 1) * ((√(E p (fun ω => Zp t j (X ω))) * η + η ^ 2 / 2) +
        (√(E p (fun ω => Zm t j (X ω))) * η + η ^ 2 / 2)) =
        η * (t (j + 1) * √(E p (fun ω => Zp t j (X ω))) +
          t (j + 1) * √(E p (fun ω => Zm t j (X ω)))) + η ^ 2 * t (j + 1) := fun j _ => by ring
    rw [sum_congr rfl e, sum_add_distrib, ← mul_sum, ← mul_sum]
    refine add_le_add ?_ le_rfl
    have hb : ∀ j ∈ range n, t (j + 1) * √(E p (fun ω => Zp t j (X ω))) +
        t (j + 1) * √(E p (fun ω => Zm t j (X ω))) ≤ √(ρ * mp j) + √(ρ * mm j) := fun j _ =>
      add_le_add (scaled_sqrt_le (hpos j) (hpos (j + 1)) (hρ j) (hap' j) (hmp0 j))
        (scaled_sqrt_le (hpos j) (hpos (j + 1)) (hρ j) (ham' j) (hmm0 j))
    have cs : ∑ j ∈ range n, (√(ρ * mp j) + √(ρ * mm j)) ≤
        √(2 * n) * √(ρ * ∑ j ∈ range n, (mp j + mm j)) := by
      have := sum_sqrt_mul_sqrt_le (range n ×ˢ (univ : Finset (Fin 2)))
        (f := fun _ => (1 : ℝ)) (g := fun q => ρ * (if q.2 = 0 then mp q.1 else mm q.1))
        (fun _ => zero_le_one) (fun q => mul_nonneg hρ0 (by split_ifs <;> simp [hmp0, hmm0]))
      simp only [sqrt_one, one_mul, sum_const, card_product, card_range, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, sum_product, Fin.sum_univ_two] at this
      simp only [Fin.isValue, ↓reduceIte, one_ne_zero, mul_add, sum_add_distrib] at this ⊢
      convert this using 2
      all_goals first | (rw [mul_sum, mul_sum]) | (push_cast; ring)
    calc η * ∑ j ∈ range n, (t (j + 1) * √(E p (fun ω => Zp t j (X ω))) +
          t (j + 1) * √(E p (fun ω => Zm t j (X ω))))
        ≤ η * (√(2 * n) * √(ρ * ∑ j ∈ range n, (mp j + mm j))) :=
          mul_le_mul_of_nonneg_left ((sum_le_sum hb).trans cs) hη
      _ = √(2 * n * ρ * η ^ 2 * ∑ j ∈ range n, (mp j + mm j)) := by
          rw [show 2 * n * ρ * η ^ 2 * ∑ j ∈ range n, (mp j + mm j) =
            η ^ 2 * ((2 * n) * (ρ * ∑ j ∈ range n, (mp j + mm j))) by ring,
            sqrt_mul' _ (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * n)
              (mul_nonneg hρ0 (sum_nonneg fun j _ => add_nonneg (hmp0 j) (hmm0 j)))),
            sqrt_sq hη, sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * n)]
  have hbud : ∑ j ∈ range n, (mp j + mm j) + MT ≤ E p (fun ω => X ω ^ 2) :=
    budget_le p hp X t ht0 ht n
  have htl : |E p (fun ω => tail t n (X ω))| ≤ MT / t n := tail_le p hp X t ht0 ht n
  have hsplit := split_le (A := 2 * n * ρ * η ^ 2) (S := S) (T := t n)
    (M := ∑ j ∈ range n, (mp j + mm j)) (MT := MT) (by positivity) (hpos n)
    (sum_nonneg fun j _ => add_nonneg (hmp0 j) (hmm0 j)) hMT0 (by linarith)
  have h2 : 2 * t 0 * (η / 2) = t 0 * η := by ring
  linarith [h1, hout, hsplit, htl]

/-- `estimator_error` for geometric thresholds `t j = b ρ ^ j`. -/
theorem estimator_error_geom (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ)
    (b ρ η S : ℝ) (hb : 0 < b) (hρ : 1 ≤ ρ) (n : ℕ) (hη : 0 ≤ η)
    (hS : E p (fun ω => X ω ^ 2) ≤ S) (aW : ℝ) (ap am : ℕ → ℝ)
    (hW : |aW - E p (fun ω => W (fun j => b * ρ ^ j) (X ω))| ≤ η / 2)
    (hap : ∀ j ∈ range n, |ap j - E p (fun ω => Zp (fun j => b * ρ ^ j) j (X ω))| ≤
      √(E p (fun ω => Zp (fun j => b * ρ ^ j) j (X ω))) * η + η ^ 2 / 2)
    (ham : ∀ j ∈ range n, |am j - E p (fun ω => Zm (fun j => b * ρ ^ j) j (X ω))| ≤
      √(E p (fun ω => Zm (fun j => b * ρ ^ j) j (X ω))) * η + η ^ 2 / 2) :
    |2 * b * (aW - 1 / 2) + ∑ j ∈ range n, b * ρ ^ (j + 1) * (ap j - am j) - E p X| ≤
      b * η + B (2 * n * ρ * η ^ 2) S (b * ρ ^ n) + η ^ 2 * ∑ j ∈ range n, b * ρ ^ (j + 1) := by
  have h := estimator_error p hp hp1 X (fun j => b * ρ ^ j) (by simpa using hb)
    (fun i j hij => mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ hij) hb.le) n ρ η S
    (by linarith) (fun j => by rw [pow_succ]; nlinarith [pow_pos (by linarith : (0:ℝ) < ρ) j])
    hη hS aW ap am (by simpa using hW) hap ham
  simpa using h

end

end MeanEstimation
