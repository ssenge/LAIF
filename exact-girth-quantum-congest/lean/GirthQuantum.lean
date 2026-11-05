import Mathlib

/-!
Counting steps for exact girth by quantum minimum finding over BFS sources.

A source `s` on a shortest cycle `C` of length `g`: `C` contains an edge that is not in the BFS tree
of `s`, at positions `i, i + 1` of `C` (position `0` is `s`). Its endpoints have depth at most
`⌊g/2⌋`, and the closed walk through it has length at most `g`.

Round `k` of the doubling: minimum finding over at most `n` sources with at least `k / 2` minima,
`p = k` parallel BFS per batch, batches of `K * k` rounds. The cost is `√(2n) * K` for every `k`.
-/

namespace GirthQuantum

/-- Distance along a cycle of length `g` from position `0` to position `i`. -/
def cdist (g i : ℕ) : ℕ := min i (g - i)

theorem cdist_le_half (g i : ℕ) (hi : i ≤ g) : cdist g i ≤ g / 2 := by
  unfold cdist; omega

/-- Every edge of the cycle closes a walk of length at most `g` through the source. -/
theorem edge_on_cycle (g i : ℕ) (hi : i + 1 ≤ g) : cdist g i + cdist g (i + 1) + 1 ≤ g := by
  unfold cdist; omega

/-- Round cost of the doubling step `k`: `b * (K k)` with `b = √(n / ((k/2) k))` batches. -/
theorem round_cost (n k K : ℝ) (hk : 0 < k) :
    Real.sqrt (n / (k / 2 * k)) * (K * k) = Real.sqrt (2 * n) * K := by
  have hk2 : k / 2 * k = k ^ 2 / 2 := by ring
  rw [hk2, div_div_eq_mul_div, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hk.le]
  field_simp

end GirthQuantum
