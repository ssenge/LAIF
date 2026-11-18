import Mathlib

/-!
# Exactness of sequential sampling from prefix sums

Let `f : (Fin n → Bool) → ℝ` be a nonnegative weight with positive total `Z = ∑ y, f y`, for example
`f y = exp (-β E y)` on the configurations of a block with the required weight and `0` elsewhere. Let
`M t z` be the total weight of the configurations that agree with `z` on the first `t` coordinates.
Drawing the coordinates one after the other, coordinate `t` with probability `M (t + 1) z / M t z`, draws `z`
with probability `f z / Z`, and every step is a probability distribution. A transfer-matrix pass computes
these sums; with the coordinates taken in reverse order this is the block heat bath.
-/

namespace BlockHeatBath

open Finset

variable {n : ℕ}

/-- Total weight of the configurations that agree with `z` on the coordinates below `t`. -/
noncomputable def M (f : (Fin n → Bool) → ℝ) (t : ℕ) (z : Fin n → Bool) : ℝ :=
  ∑ y ∈ univ.filter (fun y => ∀ i : Fin n, (i : ℕ) < t → y i = z i), f y

/-- Probability of drawing `z` coordinate by coordinate. -/
noncomputable def P (f : (Fin n → Bool) → ℝ) (z : Fin n → Bool) : ℝ :=
  ∏ t ∈ range n, M f (t + 1) z / M f t z

theorem M_zero (f : (Fin n → Bool) → ℝ) (z : Fin n → Bool) : M f 0 z = ∑ y, f y := by
  unfold M; congr 1; ext y; simp

theorem M_n (f : (Fin n → Bool) → ℝ) (z : Fin n → Bool) : M f n z = f z := by
  unfold M
  have : univ.filter (fun y : Fin n → Bool => ∀ i : Fin n, (i : ℕ) < n → y i = z i) = {z} := by
    ext y; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => funext fun i => h i i.isLt, fun h i _ => h ▸ rfl⟩
  rw [this, sum_singleton]

/-- Every step is a probability distribution: the two children of a prefix sum to it. -/
theorem M_split (f : (Fin n → Bool) → ℝ) (z : Fin n → Bool) (t : Fin n) :
    M f t z = M f (t + 1) (Function.update z t false) + M f (t + 1) (Function.update z t true) := by
  unfold M
  rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  have key : ∀ b : Bool, (∀ i : Fin n, (i : ℕ) < t + 1 → y i = Function.update z t b i) ↔
      ((∀ i : Fin n, (i : ℕ) < t → y i = z i) ∧ y t = b) := by
    intro b; constructor
    · intro h
      refine ⟨fun i hi => ?_, by simpa using h t (Nat.lt_succ_self _)⟩
      have hne : i ≠ t := fun e => by subst e; exact lt_irrefl _ hi
      simpa [Function.update_of_ne hne] using h i (Nat.lt_succ_of_lt hi)
    · rintro ⟨h, hb⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · have hne : i ≠ t := fun e => by subst e; exact lt_irrefl _ hi
        simpa [Function.update_of_ne hne] using h i hi
      · have : i = t := Fin.ext hi
        subst this; simpa using hb
  by_cases h : ∀ i : Fin n, (i : ℕ) < t → y i = z i
  · cases hy : y t
    · rw [if_pos h, if_pos ((key false).2 ⟨h, hy⟩),
        if_neg (fun h' => by simpa [hy] using ((key true).1 h').2), add_zero]
    · rw [if_pos h, if_neg (fun h' => by simpa [hy] using ((key false).1 h').2),
        if_pos ((key true).2 ⟨h, hy⟩), zero_add]
  · rw [if_neg h, if_neg (fun h' => h ((key false).1 h').1), if_neg (fun h' => h ((key true).1 h').1), add_zero]

theorem M_nonneg {f : (Fin n → Bool) → ℝ} (hf : ∀ y, 0 ≤ f y) (t : ℕ) (z : Fin n → Bool) :
    0 ≤ M f t z :=
  sum_nonneg fun y _ => hf y

theorem le_M {f : (Fin n → Bool) → ℝ} (hf : ∀ y, 0 ≤ f y) (t : ℕ) (z : Fin n → Bool) :
    f z ≤ M f t z :=
  single_le_sum (f := f) (fun y _ => hf y) (by simp)

theorem prod_telescope {f : (Fin n → Bool) → ℝ} (z : Fin n → Bool) (hM : ∀ t ≤ n, M f t z ≠ 0) :
    ∀ k ≤ n, ∏ t ∈ range k, M f (t + 1) z / M f t z = M f k z / M f 0 z := by
  intro k hk
  induction k with
  | zero => simp [div_self (hM 0 (Nat.zero_le _))]
  | succ k ih =>
    rw [prod_range_succ, ih (Nat.le_of_succ_le hk)]
    have h1 := hM k (Nat.le_of_succ_le hk)
    field_simp

/-- **Exactness.** Sequential sampling from the prefix sums draws every configuration with probability
`f z / Z`. -/
theorem P_eq {f : (Fin n → Bool) → ℝ} (hf : ∀ y, 0 ≤ f y) (hZ : 0 < ∑ y, f y) (z : Fin n → Bool) :
    P f z = f z / ∑ y, f y := by
  unfold P
  rcases (hf z).lt_or_eq with hz | hz
  · rw [prod_telescope z (fun t _ => (lt_of_lt_of_le hz (le_M hf t z)).ne') n le_rfl, M_n, M_zero]
  · rw [← hz, zero_div]
    cases n with
    | zero =>
      exfalso
      have : (∑ y : Fin 0 → Bool, f y) = f z := by
        rw [Fintype.sum_unique (fun y => f y)]
        exact congrArg f (Subsingleton.elim _ _)
      rw [this, ← hz] at hZ; exact lt_irrefl _ hZ
    | succ m =>
      refine prod_eq_zero (mem_range.2 (Nat.lt_succ_self m)) ?_
      rw [M_n, ← hz, zero_div]

/-- The probabilities of all configurations sum to one. -/
theorem sum_P {f : (Fin n → Bool) → ℝ} (hf : ∀ y, 0 ≤ f y) (hZ : 0 < ∑ y, f y) :
    ∑ z, P f z = 1 := by
  simp_rw [P_eq hf hZ, ← sum_div]; exact div_self hZ.ne'

end BlockHeatBath
