import LPType.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The sampling lemma

The law of `S` is the product measure over `Finset H`, written out as a finite sum: `prodWeight p S`
is the probability that the sample is `S`, and `prodExp p φ` is the expectation of `φ`.

The main inequality is stated in the multiplicative form `s w_h (1 - p_h) ≤ Z p_h`, which divides
by nothing, so `p_h = 1` and `w_h = 0` need no special case. Lemma 1 follows, with `Z` free: the notes
use it with an estimate `W̃` in place of the total weight, and `Z` need not be the total weight.
-/

open Finset

namespace LPType

variable {H : Type*} [DecidableEq H] [Fintype H]

/-! ## Product measure -/

/-- The probability of the sample `S` when each `h` is included independently with probability
`p h`. -/
def prodWeight (p : H → ℝ) (S : Finset H) : ℝ := ∏ h, if h ∈ S then p h else 1 - p h

/-- Expectation under the product measure. -/
def prodExp (p : H → ℝ) (φ : Finset H → ℝ) : ℝ := ∑ S : Finset H, prodWeight p S * φ S

/-- `p` is a vector of inclusion probabilities. -/
def IsProb (p : H → ℝ) : Prop := ∀ h, 0 ≤ p h ∧ p h ≤ 1

theorem prodWeight_nonneg {p : H → ℝ} (hp : IsProb p) (S : Finset H) : 0 ≤ prodWeight p S := by
  refine prod_nonneg fun h _ => ?_
  split_ifs
  · exact (hp h).1
  · linarith [(hp h).2]

/-- The product measure has total mass one. -/
theorem prodWeight_sum (p : H → ℝ) : ∑ S : Finset H, prodWeight p S = 1 := by
  have h := Finset.prod_add p (fun h => 1 - p h) (univ : Finset H)
  have h1 : ∏ i : H, (p i + (1 - p i)) = 1 := by simp
  rw [h1, powerset_univ] at h
  rw [h]
  refine sum_congr rfl fun S _ => ?_
  rw [prodWeight, ← prod_filter_mul_prod_filter_not univ (· ∈ S)]
  simp only [filter_mem_eq_inter, univ_inter]
  congr 1
  · exact prod_congr rfl fun x hx => by simp [hx]
  · have : filter (fun x => x ∉ S) univ = univ \ S := by ext; simp
    rw [this]
    exact prod_congr rfl fun x hx => by simp [(mem_sdiff.1 hx).2]

/-- The factors other than `h`. -/
def prodRest (p : H → ℝ) (h : H) (S : Finset H) : ℝ :=
  ∏ i ∈ univ.erase h, if i ∈ S then p i else 1 - p i

theorem prodRest_nonneg {p : H → ℝ} (hp : IsProb p) (h : H) (S : Finset H) :
    0 ≤ prodRest p h S := by
  refine prod_nonneg fun i _ => ?_
  split_ifs
  · exact (hp i).1
  · linarith [(hp i).2]

theorem prodWeight_of_notMem (p : H → ℝ) {h : H} {S : Finset H} (hS : h ∉ S) :
    prodWeight p S = prodRest p h S * (1 - p h) := by
  rw [prodWeight, prodRest, ← prod_erase_mul univ _ (mem_univ h), ite_eq_right hS]

theorem prodWeight_insert (p : H → ℝ) {h : H} {S : Finset H} :
    prodWeight p (insert h S) = prodRest p h S * p h := by
  rw [prodWeight, prodRest, ← prod_erase_mul univ _ (mem_univ h), ite_eq_left (mem_insert_self h S)]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  have hne : i ≠ h := (mem_erase.1 hi).1
  simp [mem_insert, hne]

/-- The independence identity: `P[S ∖ {h} = A, h ∉ S] · p_h = P[S ∖ {h} = A, h ∈ S] · (1 - p_h)`. -/
theorem prodWeight_swap (p : H → ℝ) {h : H} {A : Finset H} (hA : h ∉ A) :
    prodWeight p A * p h = prodWeight p (insert h A) * (1 - p h) := by
  rw [prodWeight_of_notMem p hA, prodWeight_insert p]
  ring

/-- Reindexing: sums over sets avoiding `h` are sums over sets containing `h`. -/
theorem sum_notMem_eq_sum_mem (h : H) (g : Finset H → ℝ) :
    ∑ A ∈ univ.filter (fun A : Finset H => h ∉ A), g (insert h A)
      = ∑ S ∈ univ.filter (fun S : Finset H => h ∈ S), g S := by
  refine sum_bij (fun A _ => insert h A) ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro A hA A' hA' e
    have hA1 := (mem_filter.1 hA).2
    have hA2 := (mem_filter.1 hA').2
    have := congrArg (fun X => X.erase h) e
    simpa [erase_insert hA1, erase_insert hA2] using this
  · intro S hS
    have hS' := (mem_filter.1 hS).2
    exact ⟨S.erase h, by simp, insert_erase hS'⟩
  · intro _ _
    rfl

/-- The inclusion probability of `h` under the product measure. -/
theorem prodWeight_marginal (p : H → ℝ) (h : H) :
    ∑ S ∈ univ.filter (fun S : Finset H => h ∈ S), prodWeight p S = p h := by
  have htot := prodWeight_sum p
  rw [← sum_filter_add_sum_filter_not univ (fun S : Finset H => h ∈ S)] at htot
  have hswap : (∑ A ∈ univ.filter (fun A : Finset H => h ∉ A), prodWeight p A) * p h
      = (∑ S ∈ univ.filter (fun S : Finset H => h ∈ S), prodWeight p S) * (1 - p h) := by
    rw [← sum_notMem_eq_sum_mem h (prodWeight p), sum_mul, sum_mul]
    refine sum_congr rfl fun A hA => ?_
    exact prodWeight_swap p (mem_filter.1 hA).2
  linear_combination hswap.symm + p h * htot

/-- The expected value of a sum over the sample is the sum of inclusion probabilities times terms. -/
theorem prodExp_sum_mem (p : H → ℝ) (a : H → ℝ) :
    prodExp p (fun S => ∑ h ∈ S, a h) = ∑ h, p h * a h := by
  have key : ∀ S : Finset H, prodWeight p S * ∑ h ∈ S, a h
      = ∑ h, (if h ∈ S then prodWeight p S else 0) * a h := by
    intro S
    rw [mul_sum, ← sum_filter_add_sum_filter_not univ (· ∈ S) (fun h =>
      (if h ∈ S then prodWeight p S else 0) * a h)]
    have : ∑ x ∈ univ.filter (· ∉ S), (if x ∈ S then prodWeight p S else 0) * a x = 0 :=
      sum_eq_zero fun x hx => by simp [(mem_filter.1 hx).2]
    rw [this, add_zero, filter_mem_eq_inter, univ_inter]
    exact sum_congr rfl fun x hx => by simp [hx]
  simp only [prodExp, key]
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  rw [← sum_mul, ← prodWeight_marginal p h, sum_filter]

/-- **Horvitz-Thompson is unbiased.** -/
theorem prodExp_htSum {p : H → ℝ} (hp : ∀ h, 0 < p h) (w : H → ℝ) :
    prodExp p (fun R => ∑ h ∈ R, w h / p h) = ∑ h, w h := by
  rw [prodExp_sum_mem]
  exact sum_congr rfl fun h _ => by
    have := (hp h).ne'
    field_simp

/-- The expected sample size is the sum of the inclusion probabilities. -/
theorem prodExp_card (p : H → ℝ) : prodExp p (fun S => (#S : ℝ)) = ∑ h, p h := by
  have := prodExp_sum_mem p (fun _ => 1)
  simpa using this

theorem prodExp_mono {p : H → ℝ} (hp : IsProb p) {φ ψ : Finset H → ℝ} (h : ∀ S, φ S ≤ ψ S) :
    prodExp p φ ≤ prodExp p ψ :=
  sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (h S) (prodWeight_nonneg hp S)

theorem prodExp_const (p : H → ℝ) (c : ℝ) : prodExp p (fun _ => c) = c := by
  simp [prodExp, ← sum_mul, prodWeight_sum]

/-! ## Lemma 1 -/

variable {R : Type*} [PartialOrder R] (P : Problem H R)

namespace Problem

open scoped Classical in
/-- The violators of `S`. -/
noncomputable def violators (S : Finset H) : Finset H := univ.filter fun h => P.Violates h S

@[simp] theorem mem_violators {S : Finset H} {h : H} : h ∈ P.violators S ↔ P.Violates h S := by
  simp [violators]

@[simp] theorem mem_extremes {S : Finset H} {h : H} : h ∈ P.extremes S ↔ P.Extreme h S := by
  simp [extremes]

open scoped Classical in
/-- **The identity in the proof of Lemma 1**: `p_h P[h ∈ V] = (1 - p_h) P[h ∈ S, h extreme in S]`. -/
theorem prob_violator_identity (p : H → ℝ) (h : H) :
    (∑ S ∈ univ.filter (fun S => P.Violates h S), prodWeight p S) * p h
      = (∑ S ∈ univ.filter (fun S => P.Extreme h S), prodWeight p S) * (1 - p h) := by
  have hL : univ.filter (fun S => P.Violates h S)
      = (univ.filter fun A : Finset H => h ∉ A).filter (fun S => P.Violates h S) := by
    ext S
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hv => ⟨hv.not_mem, hv⟩, fun hv => hv.2⟩
  have hR : ∑ S ∈ univ.filter (fun S => P.Extreme h S), prodWeight p S
      = ∑ S ∈ (univ.filter fun S : Finset H => h ∈ S),
          if P.Extreme h S then prodWeight p S else 0 := by
    rw [← sum_filter, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext S
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun he => ⟨he.1, he⟩, fun he => he.2⟩
  rw [hL, hR, sum_filter, ← sum_notMem_eq_sum_mem h, sum_mul, sum_mul]
  refine sum_congr rfl fun A hA => ?_
  have hA' := (mem_filter.1 hA).2
  by_cases hv : P.Violates h A
  · rw [ite_eq_left hv, ite_eq_left ((fact2 hA').1 hv)]
    exact prodWeight_swap p hA'
  · rw [ite_eq_right hv, ite_eq_right (fun he => hv ((fact2 hA').2 he))]
    simp

/-- The expected number of extreme elements of the sample is at most `δ`. -/
theorem prodExp_extremes_le {p : H → ℝ} (hp : IsProb p) :
    prodExp p (fun S => (#(P.extremes S) : ℝ)) ≤ P.combDim := by
  calc prodExp p (fun S => (#(P.extremes S) : ℝ))
      ≤ prodExp p (fun _ => (P.combDim : ℝ)) :=
        prodExp_mono hp fun S => by exact_mod_cast fact1 S
    _ = P.combDim := prodExp_const p _

/-- The core of Lemma 1, in multiplicative form. If `s w_h (1 - p_h) ≤ Z p_h` for all `h`, then
`s E[w(V)] ≤ δ Z`. No positivity of `p_h` is needed and `Z` need not be the total weight. -/
theorem prodExp_violators_core {p w : H → ℝ} {s Z : ℝ} (hp : IsProb p) (hZ : 0 ≤ Z)
    (hkey : ∀ h, s * w h * (1 - p h) ≤ Z * p h) :
    s * prodExp p (fun S => ∑ h ∈ P.violators S, w h) ≤ P.combDim * Z := by
  classical
  -- pointwise: moving `h` from outside to inside the sample
  have hpt : ∀ (h : H) (A : Finset H), h ∉ A →
      s * w h * prodWeight p A ≤ Z * prodWeight p (insert h A) := by
    intro h A hA
    rw [prodWeight_of_notMem p hA, prodWeight_insert p]
    have := mul_le_mul_of_nonneg_left (hkey h) (prodRest_nonneg hp h A)
    linarith
  -- rewrite the expectation of the sum as a sum over `h`
  have hexch : ∀ (a : H → Finset H → Prop) [∀ h S, Decidable (a h S)] (c : H → ℝ),
      ∑ S : Finset H, prodWeight p S * ∑ h ∈ univ.filter (fun h => a h S), c h
        = ∑ h, c h * ∑ S ∈ univ.filter (fun S => a h S), prodWeight p S := by
    intro a _ c
    simp_rw [sum_filter, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun S _ => ?_
    split_ifs <;> ring
  have hV : s * prodExp p (fun S => ∑ h ∈ P.violators S, w h)
      = ∑ h, ∑ S ∈ univ.filter (fun S => P.Violates h S), s * w h * prodWeight p S := by
    have h1 := hexch (fun h S => P.Violates h S) w
    have h2 : prodExp p (fun S => ∑ h ∈ P.violators S, w h)
        = ∑ S : Finset H, prodWeight p S * ∑ h ∈ univ.filter (fun h => P.Violates h S), w h := by
      refine sum_congr rfl fun S _ => ?_
      congr 2
    rw [h2, h1, mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun S _ => by ring
  have hE : ∑ h, ∑ S ∈ univ.filter (fun S => P.Extreme h S), prodWeight p S
      = prodExp p (fun S => (#(P.extremes S) : ℝ)) := by
    have h1 := hexch (fun h S => P.Extreme h S) (fun _ => 1)
    simp only [one_mul] at h1
    rw [← h1]
    refine sum_congr rfl fun S _ => ?_
    simp only [sum_const, nsmul_eq_mul, mul_one]
    congr 2
  have hstep : ∀ h : H, ∑ S ∈ univ.filter (fun S => P.Violates h S), s * w h * prodWeight p S
      ≤ Z * ∑ S ∈ univ.filter (fun S => P.Extreme h S), prodWeight p S := by
    intro h
    -- injection `S ↦ insert h S` from violated sets to sets where `h` is extreme
    rw [mul_sum]
    have himg : (univ.filter (fun S => P.Violates h S)).image (insert h)
        ⊆ univ.filter (fun S => P.Extreme h S) := by
      intro T hT
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hT
      have hv := (mem_filter.1 hA).2
      exact mem_filter.2 ⟨mem_univ _, (fact2 hv.not_mem).1 hv⟩
    have hinj : Set.InjOn (insert h)
        (↑(univ.filter (fun S => P.Violates h S)) : Set (Finset H)) := by
      intro A hA A' hA' e
      have h1 := (mem_filter.1 (mem_coe.1 hA)).2.not_mem
      have h2 := (mem_filter.1 (mem_coe.1 hA')).2.not_mem
      have := congrArg (fun X => X.erase h) e
      simpa [erase_insert h1, erase_insert h2] using this
    calc ∑ S ∈ univ.filter (fun S => P.Violates h S), s * w h * prodWeight p S
        ≤ ∑ S ∈ univ.filter (fun S => P.Violates h S), Z * prodWeight p (insert h S) :=
          sum_le_sum fun S hS => hpt h S (mem_filter.1 hS).2.not_mem
      _ = ∑ T ∈ (univ.filter (fun S => P.Violates h S)).image (insert h), Z * prodWeight p T :=
          (sum_image (f := fun T => Z * prodWeight p T) hinj).symm
      _ ≤ ∑ T ∈ univ.filter (fun S => P.Extreme h S), Z * prodWeight p T :=
          sum_le_sum_of_subset_of_nonneg himg fun T _ _ =>
            mul_nonneg hZ (prodWeight_nonneg hp T)
  calc s * prodExp p (fun S => ∑ h ∈ P.violators S, w h)
      = ∑ h, ∑ S ∈ univ.filter (fun S => P.Violates h S), s * w h * prodWeight p S := hV
    _ ≤ ∑ h, Z * ∑ S ∈ univ.filter (fun S => P.Extreme h S), prodWeight p S :=
        sum_le_sum fun h _ => hstep h
    _ = Z * prodExp p (fun S => (#(P.extremes S) : ℝ)) := by rw [← mul_sum, hE]
    _ ≤ Z * P.combDim := mul_le_mul_of_nonneg_left (P.prodExp_extremes_le hp) hZ
    _ = P.combDim * Z := mul_comm _ _

omit [DecidableEq H] [Fintype H] in
/-- The pointwise inequality for `p_h ≥ min(1, s w_h / Z)`, with `Z > 0`. The cases `p_h = 1` and
`w_h = 0` are not special here, and `p_h > 0` is not needed. -/
theorem key_of_min_le {p w : H → ℝ} {s Z : ℝ} (hp : IsProb p) (hw : ∀ h, 0 ≤ w h)
    (hs : 0 < s) (hZ : 0 < Z) (hmin : ∀ h, min 1 (s * w h / Z) ≤ p h) (h : H) :
    s * w h * (1 - p h) ≤ Z * p h := by
  have hp1 := (hp h).2
  have hp0 := (hp h).1
  rcases hp1.lt_or_eq with hlt | heq
  · -- `p_h < 1`: the minimum is `s w_h / Z`
    have hle : s * w h / Z ≤ p h := by
      rcases min_le_iff.1 (hmin h) with h1 | h1
      · linarith
      · exact h1
    have hle' : s * w h ≤ Z * p h := by
      rw [div_le_iff₀ hZ] at hle
      linarith
    have : 0 ≤ s * w h := mul_nonneg hs.le (hw h)
    nlinarith
  · rw [heq]
    simp [hZ.le]

/-- **Lemma 1, general form**, with any `Z > 0` in place of the total weight, as used in the proof
of Theorem 1. -/
theorem lemma1_general {p w : H → ℝ} {s Z : ℝ} (hp : IsProb p) (hw : ∀ h, 0 ≤ w h)
    (hs : 0 < s) (hZ : 0 < Z) (hmin : ∀ h, min 1 (s * w h / Z) ≤ p h) :
    prodExp p (fun S => ∑ h ∈ P.violators S, w h) ≤ P.combDim * Z / s := by
  have := P.prodExp_violators_core (s := s) hp hZ.le (key_of_min_le hp hw hs hZ hmin)
  rw [le_div_iff₀ hs]
  linarith

/-- **Lemma 1.** `w ≥ 0` with total `W`, and independent inclusion probabilities `p_h > 0` with
`p_h ≥ min(1, s w_h / W)`. Then `E[w(V)] ≤ δ W / s`. If `W = 0` every `w_h` vanishes and both sides
are `0`. -/
theorem lemma1 {p w : H → ℝ} {s : ℝ} (hp0 : ∀ h, 0 < p h) (hp1 : ∀ h, p h ≤ 1)
    (hw : ∀ h, 0 ≤ w h) (hs : 0 < s)
    (hmin : ∀ h, min 1 (s * w h / ∑ i, w i) ≤ p h) :
    prodExp p (fun S => ∑ h ∈ P.violators S, w h) ≤ P.combDim * (∑ i, w i) / s := by
  have hp : IsProb p := fun h => ⟨(hp0 h).le, hp1 h⟩
  rcases (sum_nonneg fun i _ => hw i : 0 ≤ ∑ i, w i).lt_or_eq with hW | hW
  · exact P.lemma1_general hp hw hs hW hmin
  · have hzero : ∀ h, w h = 0 := fun h =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hw i).1 hW.symm h (mem_univ h)
    simp [prodExp, hzero]

end Problem

end LPType
