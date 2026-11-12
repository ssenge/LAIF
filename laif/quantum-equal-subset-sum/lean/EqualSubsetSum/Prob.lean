import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform probability on a finite set

`prob Ω p` is the fraction of `Ω` satisfying `p`, and `mean Ω f` the average of `f` over `Ω`. The
random choices of the procedure, the prime among them, are of this form.

The basic estimate is `count_above`, which gives both Markov's inequality and the averaging step
of the filter. It needs `f ≥ 0`, which is why the statements below ask for it.
-/

open Finset

namespace EqualSubsetSum

variable {ω : Type*}

open scoped Classical in
/-- The probability of `p` under the uniform choice from `Ω`. -/
noncomputable def prob (Ω : Finset ω) (p : ω → Prop) : ℝ := (#(Ω.filter p) : ℝ) / #Ω

theorem prob_eq (Ω : Finset ω) (p : ω → Prop) [DecidablePred p] :
    prob Ω p = (#(Ω.filter p) : ℝ) / #Ω := by
  unfold prob
  congr!

/-- The mean of `f` under the uniform choice from `Ω`. -/
noncomputable def mean (Ω : Finset ω) (f : ω → ℝ) : ℝ := (∑ x ∈ Ω, f x) / #Ω

/-- If the sum of `e ≥ 0` over `K` is at most `|K| A`, then at most a `1/m` fraction of `K` has
`e > m A`. The case `A = 0` is included: then `e` vanishes on `K`. -/
theorem count_above {κ : Type*} (K : Finset κ) (e : κ → ℝ) (he : ∀ j ∈ K, 0 ≤ e j) {A : ℝ}
    (hmean : ∑ j ∈ K, e j ≤ #K * A) {m : ℝ} (hm : 0 < m) :
    m * (#{j ∈ K | m * A < e j} : ℝ) ≤ #K := by
  set B := K.filter fun j => m * A < e j with hB
  rcases B.eq_empty_or_nonempty with h0 | ⟨j, hj⟩
  · simp [h0]
  have hjK : j ∈ K := (mem_filter.mp hj).1
  have hjA : m * A < e j := (mem_filter.mp hj).2
  have h1 : (#B : ℝ) * (m * A) ≤ ∑ x ∈ B, e x := by
    have := card_nsmul_le_sum B e (m * A) fun x hx => le_of_lt (mem_filter.mp hx).2
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ x ∈ B, e x ≤ ∑ x ∈ K, e x :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x hx _ => he x hx
  have h3 : e j ≤ ∑ x ∈ K, e x := single_le_sum he hjK
  have hKpos : (0 : ℝ) < #K := by
    have : 0 < #K := card_pos.mpr ⟨j, hjK⟩
    exact_mod_cast this
  have hA : 0 < A := by
    by_contra hA
    have hA' : A ≤ 0 := not_lt.mp hA
    have h4 : (#K : ℝ) * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKpos.le hA'
    have h5 := he j hjK
    have h6 : e j = 0 := by linarith
    have h7 : A = 0 := by
      have : 0 ≤ (#K : ℝ) * A := by linarith
      nlinarith
    rw [h6, h7] at hjA
    simp at hjA
  have h8 : (m * (#B : ℝ)) * A ≤ (#K : ℝ) * A := by nlinarith
  exact le_of_mul_le_mul_right h8 hA

/-- **Averaging.** If the mean of `e ≥ 0` over `K` is at most `A`, then at least half of `K` has
`e ≤ 2 A`. -/
theorem averaging {κ : Type*} (K : Finset κ) (e : κ → ℝ) (he : ∀ j ∈ K, 0 ≤ e j) {A : ℝ}
    (hmean : ∑ j ∈ K, e j ≤ #K * A) :
    #K ≤ 2 * #{j ∈ K | e j ≤ 2 * A} := by
  have h := count_above K e he hmean (m := 2) (by norm_num)
  have hsplit := card_filter_add_card_filter_not (s := K) (fun j => e j ≤ 2 * A)
  have hnot : (K.filter fun j => ¬ e j ≤ 2 * A) = K.filter fun j => 2 * A < e j := by
    ext j
    simp
  rw [hnot] at hsplit
  have h' : 2 * #{j ∈ K | 2 * A < e j} ≤ #K := by
    have : ((2 * #{j ∈ K | 2 * A < e j} : ℕ) : ℝ) ≤ #K := by
      push_cast
      exact h
    exact_mod_cast this
  omega

open scoped Classical in
/-- **Markov**, for a uniform choice from a finite set: `Pr[f > t] ≤ E[f] / t`. -/
theorem markov (Ω : Finset ω) (f : ω → ℝ) (hf : ∀ x ∈ Ω, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    prob Ω (fun x => t < f x) ≤ mean Ω f / t := by
  unfold prob mean
  rcases Ω.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : (0 : ℝ) < #Ω := by exact_mod_cast card_pos.mpr hne
  rw [div_div, div_le_div_iff₀ hpos (by positivity)]
  have h1 : (#(Ω.filter fun x => t < f x) : ℝ) * t ≤ ∑ x ∈ Ω, f x := by
    have h2 := card_nsmul_le_sum (Ω.filter fun x => t < f x) f t
      fun x hx => le_of_lt (mem_filter.mp hx).2
    have h3 : ∑ x ∈ Ω.filter (fun x => t < f x), f x ≤ ∑ x ∈ Ω, f x :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x hx _ => hf x hx
    have h4 : (#(Ω.filter fun x => t < f x) : ℝ) * t
        ≤ ∑ x ∈ Ω.filter (fun x => t < f x), f x := by
      simpa [nsmul_eq_mul] using h2
    linarith
  nlinarith

/-- The chain rule for a mean: if at least a fraction `α` of `Ω₁` is good, and for each good first
choice the mean of `f ≥ 0` over `Ω₂` is at least `β`, then the mean of `f` over the pairs is at least
`α β`. -/
theorem mean_chain {ω₂ : Type*} (Ω₁ : Finset ω) (Ω₂ : Finset ω₂) (p : ω → Prop) (f : ω → ω₂ → ℝ)
    {α β : ℝ} (hα : α ≤ prob Ω₁ p) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hf : ∀ x ∈ Ω₁, ∀ y ∈ Ω₂, 0 ≤ f x y) (hq : ∀ x ∈ Ω₁, p x → β ≤ mean Ω₂ (f x)) :
    α * β ≤ mean (Ω₁ ×ˢ Ω₂) (fun x => f x.1 x.2) := by
  classical
  have hm0 : ∀ x ∈ Ω₁, 0 ≤ mean Ω₂ (f x) := fun x hx =>
    div_nonneg (sum_nonneg fun y hy => hf x hx y hy) (by positivity)
  have hprod : mean (Ω₁ ×ˢ Ω₂) (fun x => f x.1 x.2) = (∑ x ∈ Ω₁, mean Ω₂ (f x)) / #Ω₁ := by
    unfold mean
    rw [sum_product, card_product, ← sum_div]
    push_cast
    rw [div_div, mul_comm]
  rw [hprod]
  rcases Ω₁.eq_empty_or_nonempty with rfl | h₁
  · simp only [prob_eq, filter_empty, card_empty, Nat.cast_zero, div_zero] at hα
    have : α = 0 := le_antisymm hα hα0
    simp [this]
  have hp₁ : (0 : ℝ) < #Ω₁ := by exact_mod_cast card_pos.mpr h₁
  rw [le_div_iff₀ hp₁]
  rw [prob_eq, le_div_iff₀ hp₁] at hα
  have h1 : ∑ _x ∈ Ω₁.filter p, β ≤ ∑ x ∈ Ω₁, mean Ω₂ (f x) := by
    calc ∑ _x ∈ Ω₁.filter p, β ≤ ∑ x ∈ Ω₁.filter p, mean Ω₂ (f x) :=
          sum_le_sum fun x hx => hq x (mem_filter.mp hx).1 (mem_filter.mp hx).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x hx _ => hm0 x hx
  rw [sum_const, nsmul_eq_mul] at h1
  have h2 : (α * #Ω₁) * β ≤ (#(Ω₁.filter p) : ℝ) * β := mul_le_mul_of_nonneg_right hα hβ0
  calc α * β * #Ω₁ = (α * #Ω₁) * β := by ring
    _ ≤ _ := h2.trans h1

end EqualSubsetSum
