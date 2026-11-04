import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite adaptive processes

A finite probability formulation of an adaptive algorithm: a state, a finite set of possible steps,
a law of the next step given the state, and a deterministic state update. The law of a run of `T`
steps is the product of the conditional laws along the run, so it is an explicit weight on the finite
set of paths of length `T` (`pathWeight`, `paths`), with total mass one (`pathWeight_sum`).
`expect_eq_sum_paths` identifies the recursion `expect`, the tower rule, with that finite sum.
-/

open Finset

namespace LPType

/-- A finite adaptive process: the law of the next step and the update of the state. -/
structure Kernel (State Step : Type*) [Fintype Step] where
  /-- The conditional probability of a step given the state. -/
  weight : State → Step → ℝ
  /-- The state after a step. -/
  next : State → Step → State
  weight_nonneg : ∀ σ x, 0 ≤ weight σ x
  weight_sum : ∀ σ, ∑ x, weight σ x = 1

namespace Kernel

variable {State Step : Type*} [Fintype Step] (K : Kernel State Step)

/-- The state after a path. -/
def run (σ : State) (l : List Step) : State := l.foldl K.next σ

@[simp] theorem run_nil (σ : State) : K.run σ [] = σ := rfl

@[simp] theorem run_cons (σ : State) (x : Step) (l : List Step) :
    K.run σ (x :: l) = K.run (K.next σ x) l := rfl

/-- The expectation of a function of the path over `T` steps from `σ`. -/
noncomputable def expect : ℕ → State → (List Step → ℝ) → ℝ
  | 0, _, φ => φ []
  | T + 1, σ, φ => ∑ x, K.weight σ x * expect T (K.next σ x) (fun l => φ (x :: l))

/-- The probability of a path from `σ`. -/
noncomputable def pathWeight : State → List Step → ℝ
  | _, [] => 1
  | σ, x :: l => K.weight σ x * pathWeight (K.next σ x) l

open scoped Classical in
/-- All paths of length `T`. -/
noncomputable def paths : ℕ → Finset (List Step)
  | 0 => {[]}
  | T + 1 => (univ ×ˢ paths T).image fun p => p.1 :: p.2

theorem mem_paths {T : ℕ} {l : List Step} : l ∈ paths (Step := Step) T ↔ l.length = T := by
  classical
  induction T generalizing l with
  | zero => simp [paths, List.length_eq_zero_iff]
  | succ T ih =>
    simp only [paths, mem_image, mem_product, mem_univ, true_and, Prod.exists, ih]
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      simp [hb]
    · intro hl
      cases l with
      | nil => simp at hl
      | cons x l => exact ⟨x, l, by simpa using hl, rfl⟩

/-- The recursion `expect` is the finite sum over paths against the path probabilities. -/
theorem expect_eq_sum_paths (T : ℕ) (σ : State) (φ : List Step → ℝ) :
    K.expect T σ φ = ∑ l ∈ paths T, K.pathWeight σ l * φ l := by
  classical
  induction T generalizing σ φ with
  | zero => simp [expect, paths, pathWeight]
  | succ T ih =>
    have hinj : Set.InjOn (fun p : Step × List Step => p.1 :: p.2)
        (↑((univ : Finset Step) ×ˢ paths (Step := Step) T) : Set (Step × List Step)) := by
      intro a _ b _ e
      simpa [Prod.ext_iff] using e
    rw [expect, paths, sum_image hinj, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [ih, mul_sum]
    exact sum_congr rfl fun l _ => by simp only [pathWeight]; ring

theorem pathWeight_nonneg (σ : State) (l : List Step) : 0 ≤ K.pathWeight σ l := by
  induction l generalizing σ with
  | nil => simp [pathWeight]
  | cons x l ih => exact mul_nonneg (K.weight_nonneg σ x) (ih _)

theorem expect_const (T : ℕ) (σ : State) (c : ℝ) : K.expect T σ (fun _ => c) = c := by
  induction T generalizing σ with
  | zero => rfl
  | succ T ih => simp [expect, ih, ← sum_mul, K.weight_sum]

/-- The path probabilities have total mass one. -/
theorem pathWeight_sum (T : ℕ) (σ : State) : ∑ l ∈ paths (Step := Step) T, K.pathWeight σ l = 1 := by
  have := K.expect_eq_sum_paths T σ (fun _ => 1)
  rw [K.expect_const] at this
  simpa using this.symm

theorem expect_mono {T : ℕ} {σ : State} {φ ψ : List Step → ℝ}
    (h : ∀ l : List Step, l.length = T → φ l ≤ ψ l) : K.expect T σ φ ≤ K.expect T σ ψ := by
  rw [K.expect_eq_sum_paths, K.expect_eq_sum_paths]
  exact sum_le_sum fun l hl =>
    mul_le_mul_of_nonneg_left (h l (mem_paths.1 hl)) (K.pathWeight_nonneg σ l)

theorem expect_const_mul (T : ℕ) (σ : State) (c : ℝ) (φ : List Step → ℝ) :
    K.expect T σ (fun l => c * φ l) = c * K.expect T σ φ := by
  rw [K.expect_eq_sum_paths, K.expect_eq_sum_paths, mul_sum]
  exact sum_congr rfl fun l _ => by ring

open scoped Classical in
/-- The probability of an event on paths of length `T`. -/
noncomputable def prob (T : ℕ) (σ : State) (A : List Step → Prop) : ℝ :=
  K.expect T σ fun l => if A l then 1 else 0

/-- **Markov**, in the form used for Theorem 1. -/
theorem markov {T : ℕ} {σ : State} {A : List Step → Prop} {φ : List Step → ℝ} {a : ℝ}
    (hφ : ∀ l, l.length = T → 0 ≤ φ l) (hA : ∀ l, l.length = T → A l → a ≤ φ l) :
    a * K.prob T σ A ≤ K.expect T σ φ := by
  classical
  rw [prob, ← K.expect_const_mul]
  refine K.expect_mono fun l hl => ?_
  by_cases h : A l
  · simpa [h] using hA l hl h
  · simpa [h] using hφ l hl

/-- **The tower rule for a potential.** If the potential `G` grows by at most a factor `c` in
expectation in each step, then `E[G_T] ≤ c^T G_0`. The inequality is required on an invariant set
of states. -/
theorem expect_potential_le_on {G : State → ℝ} {c : ℝ} {I : State → Prop} (hc : 0 ≤ c)
    (hinv : ∀ σ x, I σ → K.weight σ x ≠ 0 → I (K.next σ x))
    (hstep : ∀ σ, I σ → ∑ x, K.weight σ x * G (K.next σ x) ≤ c * G σ)
    (T : ℕ) (σ : State) (hσ : I σ) :
    K.expect T σ (fun l => G (K.run σ l)) ≤ c ^ T * G σ := by
  induction T generalizing σ with
  | zero => simp [expect]
  | succ T ih =>
    have h1 : ∀ x, K.weight σ x * K.expect T (K.next σ x) (fun l => G (K.run (K.next σ x) l))
        ≤ K.weight σ x * (c ^ T * G (K.next σ x)) := by
      intro x
      by_cases hx : K.weight σ x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left (ih _ (hinv σ x hσ hx)) (K.weight_nonneg σ x)
    calc K.expect (T + 1) σ (fun l => G (K.run σ l))
        = ∑ x, K.weight σ x * K.expect T (K.next σ x) (fun l => G (K.run (K.next σ x) l)) := rfl
      _ ≤ ∑ x, K.weight σ x * (c ^ T * G (K.next σ x)) := sum_le_sum fun x _ => h1 x
      _ = c ^ T * ∑ x, K.weight σ x * G (K.next σ x) := by
          rw [mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ c ^ T * (c * G σ) := mul_le_mul_of_nonneg_left (hstep σ hσ) (pow_nonneg hc T)
      _ = c ^ (T + 1) * G σ := by ring

/-- The tower rule with the step inequality on all states. -/
theorem expect_potential_le {G : State → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ σ, ∑ x, K.weight σ x * G (K.next σ x) ≤ c * G σ) (T : ℕ) (σ : State) :
    K.expect T σ (fun l => G (K.run σ l)) ≤ c ^ T * G σ :=
  K.expect_potential_le_on (I := fun _ => True) hc (fun _ _ _ _ => trivial)
    (fun σ _ => hstep σ) T σ trivial

/-! ## Rejection -/

open scoped Classical in
/-- The acceptance probability of a step. -/
noncomputable def acceptProb (A : State → Step → Prop) (σ : State) : ℝ :=
  ∑ x, if A σ x then K.weight σ x else 0

open scoped Classical in
/-- Redrawing a whole step until the event `A` holds: the law of the step conditioned on `A`.
If `A` has probability `0` the redraw would never end, and the law is left unchanged here to
keep a total function; theorems about it assume that the acceptance probability is positive. -/
noncomputable def conditioned (A : State → Step → Prop) : Kernel State Step where
  weight σ x :=
    if 0 < K.acceptProb A σ then (if A σ x then K.weight σ x else 0) / K.acceptProb A σ
    else K.weight σ x
  next := K.next
  weight_nonneg σ x := by
    have h1 := K.weight_nonneg σ x
    by_cases h : 0 < K.acceptProb A σ
    · rw [ite_eq_left h]
      refine div_nonneg ?_ h.le
      split_ifs
      · exact h1
      · exact le_rfl
    · rw [ite_eq_right h]
      exact h1
  weight_sum σ := by
    by_cases h : 0 < K.acceptProb A σ
    · simp only [ite_eq_left h]
      rw [← sum_div, ← acceptProb, div_self h.ne']
    · simp only [ite_eq_right h]
      exact K.weight_sum σ

open scoped Classical in
/-- Conditioning on `A` raises the expectation of a non-negative function by at most the factor
`1 / P[A]`. -/
theorem sum_conditioned_le (A : State → Step → Prop) {σ : State} (hq : 0 < K.acceptProb A σ)
    {g : Step → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ x, (K.conditioned A).weight σ x * g x ≤ (∑ x, K.weight σ x * g x) / K.acceptProb A σ := by
  rw [le_div_iff₀ hq, sum_mul]
  refine sum_le_sum fun x _ => ?_
  have hw := K.weight_nonneg σ x
  simp only [conditioned, ite_eq_left hq]
  by_cases hx : A σ x
  · rw [ite_eq_left hx]
    have := hq.ne'
    apply le_of_eq
    field_simp
  · rw [ite_eq_right hx, zero_div, zero_mul, zero_mul]
    exact mul_nonneg hw (hg x)

end Kernel

end LPType
