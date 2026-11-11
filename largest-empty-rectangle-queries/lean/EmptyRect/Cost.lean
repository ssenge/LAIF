import Mathlib

/-!
# The query count

At one depth of the front learner the regions have `rᵢ` rows and `wᵢ` columns with `∑ rᵢ ≤ R` and `∑ wᵢ ≤ W`, so the
searches cost at most `√(R W)` up to a constant (`level_cost`). There are at most `⌈n/d⌉ ⌈n/h⌉` lattice cells, and a
search over them with a window test of cost `√(d h)` costs at most `2 n` (`outer_cost`).
-/

open Finset

namespace EmptyRect

/-- **Cost at one depth.** -/
theorem level_cost {ι : Type*} (s : Finset ι) (r w : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i) {R W : ℝ}
    (hR : ∑ i ∈ s, r i ≤ R) (hW : ∑ i ∈ s, w i ≤ W) :
    ∑ i ∈ s, Real.sqrt (r i * w i) ≤ Real.sqrt (R * W) := by
  calc ∑ i ∈ s, Real.sqrt (r i * w i) = ∑ i ∈ s, Real.sqrt (r i) * Real.sqrt (w i) := by
        refine sum_congr rfl fun i _ => Real.sqrt_mul (hr i) _
    _ ≤ Real.sqrt (∑ i ∈ s, r i) * Real.sqrt (∑ i ∈ s, w i) := Real.sum_sqrt_mul_sqrt_le s hr hw
    _ ≤ Real.sqrt R * Real.sqrt W :=
        mul_le_mul (Real.sqrt_le_sqrt hR) (Real.sqrt_le_sqrt hW) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (R * W) := by
        have h0 : 0 ≤ R := (sum_nonneg fun i _ => hr i).trans hR
        rw [Real.sqrt_mul h0]

/-- The number of lattice rows: `⌈n/d⌉ d ≤ 2 n` for `1 ≤ d ≤ n`. -/
theorem ceil_mul_le {n d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) : (n + d - 1) / d * d ≤ 2 * n := by
  have := Nat.div_mul_le_self (n + d - 1) d
  omega

/-- **The outer search.** With `A d ≤ 2 n` and `B h ≤ 2 n`, a search over `A B` lattice cells with a window test of cost
`√(d h)` costs `√(A B) √(d h) ≤ 2 n`. -/
theorem outer_cost {n d h A B : ℝ} (hd : 0 ≤ d) (hh : 0 ≤ h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAd : A * d ≤ 2 * n) (hBh : B * h ≤ 2 * n) :
    Real.sqrt (A * B) * Real.sqrt (d * h) ≤ 2 * n := by
  have hn : 0 ≤ n := by nlinarith [mul_nonneg hA hd]
  rw [← Real.sqrt_mul (mul_nonneg hA hB)]
  have : A * B * (d * h) = (A * d) * (B * h) := by ring
  rw [this]
  calc Real.sqrt (A * d * (B * h)) ≤ Real.sqrt ((2 * n) * (2 * n)) :=
        Real.sqrt_le_sqrt (mul_le_mul hAd hBh (mul_nonneg hB hh) (by linarith))
    _ = 2 * n := Real.sqrt_mul_self (by linarith)

end EmptyRect
