import ArbGroups.Basic

/-!
# Non-vacuity of the counting lemmas

Each main lemma has satisfiable hypotheses, and its bound is attained on an instance.
-/

namespace ArbGroups

open Finset

/-- The class step of `cls_double` is attained: size `1` has class `0`, size `2` class `1`. -/
example : cls 1 + 1 = cls 2 := by
  unfold cls; rw [Nat.log_one_right, Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 1 ≤ 2) (by norm_num : 2 < 2 ^ 2)]

/-- `card_le_of_distinct_cls` is tight: groups of sizes `1, 2, 4` (total `7`) have three distinct
classes, and `log₂ 7 + 1 = 3`. -/
example : ∃ size : Fin 3 → ℕ, Set.InjOn (fun g => cls (size g)) (univ : Finset (Fin 3)) ∧
    ∑ g, size g ≤ 7 ∧ (univ : Finset (Fin 3)).card = Nat.log 2 7 + 1 := by
  refine ⟨fun g => 2 ^ (g : ℕ), ?_, ?_, ?_⟩
  · intro a _ b _ h
    simp only [cls, Nat.log_pow (by norm_num : 1 < 2)] at h
    exact Fin.ext h
  · simp [Fin.sum_univ_three]
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 2 ≤ 7) (by norm_num : 7 < 2 ^ 3)]; simp

/-- `lemma2` is tight: for `n = 4`, a vertex can change its group `4 = 2 log₂ 4` times. Steps `0, 1`
double its supernode `1 → 2 → 4`; steps `2, 3` raise the class `0 → 1 → 2`. -/
example : ∃ (c z : ℕ → ℕ) (A : Finset ℕ),
    (∀ i < 4, c i ≤ c (i + 1)) ∧ (∀ i < 4, i ∉ A → c i + 1 ≤ c (i + 1)) ∧
    (∀ i < 4, z i ≤ z (i + 1)) ∧ (∀ i < 4, i ∈ A → 2 * z i ≤ z (i + 1)) ∧
    1 ≤ z 0 ∧ z 4 ≤ 4 ∧ c 4 ≤ Nat.log 2 4 ∧ 4 = 2 * Nat.log 2 4 := by
  have hl : Nat.log 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, Nat.log_pow (by norm_num)]
  refine ⟨fun i => [0, 0, 0, 1, 2].getD i 0, fun i => [1, 2, 4, 4, 4].getD i 0, {0, 1},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hl] <;> decide

/-- `lemma4_rows` is tight: batches `1, 2` after one drop give `3 = 2 · 1 + 1` rows. -/
example : ∑ i ∈ range 1, 2 ^ i ≤ 1 ∧ ∑ i ∈ range 2, 2 ^ i = 2 * 1 + 1 := by
  simp [sum_range_succ]

/-- `total_cost` has satisfiable hypotheses and is attained by one group. -/
example : ∑ _g ∈ (univ : Finset (Fin 1)), (1 : ℝ) =
    1 * Real.sqrt 1 * Real.sqrt 1 * Real.sqrt 1 ∧
    ∀ g ∈ (univ : Finset (Fin 1)), (1 : ℝ) ≤ 1 * Real.sqrt (1 * 1 * 1) := by
  simp

end ArbGroups
