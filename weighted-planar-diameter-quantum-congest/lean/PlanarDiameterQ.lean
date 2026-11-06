import Mathlib

/-!
Path weights in the planar diameter gadget, with `M = 4`. Coordinate nodes `a i` (Alice) and
`b j` (Bob), `1 ≤ i, j ≤ n`, hubs `l, r` (Alice) and `l', r'` (Bob), edges `l l'` and `r r'` of
weight `4`. With input bits `α = A i` and `β = B j`:

* `w (a i, l) = 4 i + α`, `w (a i, r) = 4 (n + 1 - i) + α`,
* `w (b j, l') = 4 (n + 1 - j) + β`, `w (b j, r') = 4 j + β`.

A coordinate node has degree two, so a path that passes through one pays `4 (n + 1)` there.
The only other paths between `a i` and `b j` are `a i, l, l', b j` and `a i, r, r', b j`.
-/

namespace PlanarDiameterQ

/-- Weight of the left path `a i, l, l', b j`. -/
def left (n i j α β : ℕ) : ℕ := 4 * i + α + 4 + (4 * (n + 1 - j) + β)

/-- Weight of the right path `a i, r, r', b j`. -/
def right (n i j α β : ℕ) : ℕ := 4 * (n + 1 - i) + α + 4 + (4 * j + β)

/-- The pair `a i, b i` is at distance `4 (n + 2) + α + β`. -/
theorem cross_same (n i α β : ℕ) (hi : i ≤ n) :
    left n i i α β = 4 * (n + 2) + α + β ∧ right n i i α β = 4 * (n + 2) + α + β := by
  unfold left right; omega

/-- Pairs `a i, b j` with `i ≠ j` are at distance at most `4 (n + 1) + 2`. -/
theorem cross_diff (n i j α β : ℕ) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≠ j) (hα : α ≤ 1)
    (hβ : β ≤ 1) : min (left n i j α β) (right n i j α β) ≤ 4 * (n + 1) + 2 := by
  unfold left right; omega

/-- Pairs `a i, a j` (paths `a i, l, a j` and `a i, r, a j`) are at distance at most
`4 (n + 1) + 2`; Bob's side is the same with `i, j` replaced by `n + 1 - i, n + 1 - j`. -/
theorem same_side (n i j α β : ℕ) (hi : i ≤ n) (hj : j ≤ n) (hα : α ≤ 1) (hβ : β ≤ 1) :
    min (4 * i + α + (4 * j + β)) (4 * (n + 1 - i) + α + (4 * (n + 1 - j) + β)) ≤
      4 * (n + 1) + 2 := by
  omega

/-- A coordinate node is at distance at most `4 (n + 1) + 1` from every hub. -/
theorem to_hub (n i α : ℕ) (hi : 1 ≤ i) (hi' : i ≤ n) (hα : α ≤ 1) :
    4 * i + α ≤ 4 * (n + 1) + 1 ∧ 4 * (n + 1 - i) + α ≤ 4 * (n + 1) + 1 ∧
      4 * i + α + 4 ≤ 4 * (n + 1) + 1 ∧ 4 * (n + 1 - i) + α + 4 ≤ 4 * (n + 1) + 1 := by
  omega

/-- Hub pairs: `l, r` via `a 1` (and `l', r'` via `b 1`) are at distance at most
`4 (n + 1) + 2`; `l, r'` (and `r, l'`) via `l', b 1, r'` or `a 1, r, r'` are at distance at most
`4 (n + 2)` unless `A 1 = B 1 = 1`. -/
theorem hubs (n α β : ℕ) (hα : α ≤ 1) (hβ : β ≤ 1) :
    4 * 1 + α + (4 * n + α) ≤ 4 * (n + 1) + 2 ∧
      (min (4 + (4 * n + β) + (4 * 1 + β)) (4 * 1 + α + (4 * n + α) + 4) ≤ 4 * (n + 2) ∨
        (α = 1 ∧ β = 1)) := by
  omega

/-- A path through a coordinate node `a k` uses both of its edges; with its first and last edge
(each at least `4`) and a crossing edge it weighs more than every distance above. -/
theorem through_node (n k e₁ e₂ : ℕ) (hk : k ≤ n) (h₁ : 4 ≤ e₁) (h₂ : 4 ≤ e₂) :
    4 * (n + 2) + 2 < e₁ + (4 * k + 4 * (n + 1 - k)) + 4 + e₂ := by
  omega

/-- The diameter is `4 (n + 2) + 2` if the inputs intersect, and at most `4 (n + 2) + 1` if not. -/
theorem gap (n α β : ℕ) (hα : α ≤ 1) (hβ : β ≤ 1) :
    (4 * (n + 2) + α + β = 4 * (n + 2) + 2 ↔ α = 1 ∧ β = 1) ∧
      4 * (n + 1) + 2 < 4 * (n + 2) + 1 := by
  omega

end PlanarDiameterQ
