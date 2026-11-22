import Mathlib.Algebra.Order.Round
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Counting step of the attention head for a fixed subset parity

For values `x_j ∈ {−1, +1}` on a subset of size `k` with sum `t`, the number of `−1` entries is
`(k − t)/2` and the product is `(−1)` to that power. The output map rounds `N z` to the integer `t`,
which is exact once `N z` is within `1/2` of `t`, and the rounding of the unit output to
`p` fractional bits with `2^p ≥ 4N` moves `N z` by at most `1/8`.
-/

namespace SubsetParity

/-- Product and sum of a list of signs: both are determined by the number of `−1` entries. -/
theorem prod_sum_signs (xs : List ℤ) (h : ∀ x ∈ xs, x = 1 ∨ x = -1) :
    xs.prod = (-1) ^ xs.count (-1) ∧ (xs.length : ℤ) - xs.sum = 2 * xs.count (-1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self) with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp [ih1]
      · simp only [List.length_cons, List.sum_cons, List.count_cons]; push_cast; simp; linarith
    · refine ⟨?_, ?_⟩
      · simp [ih1, pow_succ]
      · simp only [List.length_cons, List.sum_cons, List.count_cons]; push_cast; simp; linarith

/-- The parity is recovered from the count: `∏ x_j = (−1)^((k − t)/2)` with `k − t` even. -/
theorem prod_eq_from_count (xs : List ℤ) (h : ∀ x ∈ xs, x = 1 ∨ x = -1) :
    ∃ m : ℕ, (xs.length : ℤ) - xs.sum = 2 * m ∧ xs.prod = (-1) ^ m :=
  ⟨xs.count (-1), (prod_sum_signs xs h).2, (prod_sum_signs xs h).1⟩

/-- Rounding recovers an integer from a value within `1/2` of it. -/
theorem round_eq_of_near (x : ℝ) (t : ℤ) (h : |x - t| < 1 / 2) : round x = t := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

/-- Rounding to `p` fractional bits with `2^p ≥ 4N` moves `N z` by at most `1/8`. -/
theorem rounding_error (N : ℝ) (p : ℕ) (hp : 4 * N ≤ 2 ^ p) :
    N * (1 / 2) ^ (p + 1) ≤ 1 / 8 := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  rw [pow_succ, div_pow, one_pow]
  rw [show N * (1 / 2 ^ p * (1 / 2)) = N / 2 ^ p / 2 by ring]
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith

end SubsetParity
