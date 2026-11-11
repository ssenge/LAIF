import Mathlib

/-!
# The query count of the search

The search amplifies a base procedure that costs at most `3√n + 4` queries (a neighbour sample of `⌈√n⌉` steps, one
query, and a witness search of `⌈√n⌉` steps with two queries each) and succeeds with probability at least `1 / (c n)`.
Amplitude amplification repeats it `O(√(c n))` times, and the product is at most `7 √c · n`.
-/

namespace ClusterRec

/-- **The count.** For `n ≥ 1` and `c ≥ 0`: `√(c n) (3√n + 4) ≤ 7 √c · n`. -/
theorem search_cost {n c : ℝ} (hn : 1 ≤ n) (hc : 0 ≤ c) :
    Real.sqrt (c * n) * (3 * Real.sqrt n + 4) ≤ 7 * Real.sqrt c * n := by
  have hn0 : 0 ≤ n := by linarith
  have h2 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn
  have h3 : Real.sqrt (c * n) * Real.sqrt n = Real.sqrt c * n := by
    rw [Real.sqrt_mul hc, mul_assoc, Real.mul_self_sqrt hn0]
  have hs : 0 ≤ Real.sqrt (c * n) := Real.sqrt_nonneg _
  calc Real.sqrt (c * n) * (3 * Real.sqrt n + 4) ≤ Real.sqrt (c * n) * (7 * Real.sqrt n) := by
        apply mul_le_mul_of_nonneg_left _ hs
        linarith
    _ = 7 * (Real.sqrt (c * n) * Real.sqrt n) := by ring
    _ = 7 * Real.sqrt c * n := by rw [h3]; ring

end ClusterRec
