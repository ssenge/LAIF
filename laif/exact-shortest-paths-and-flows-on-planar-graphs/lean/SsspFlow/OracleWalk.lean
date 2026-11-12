import SsspFlow.OracleTree

/-!
# The parent chain as a walk

From a node of finite distance in an output of the oracle, the parent chain read backwards is a walk
from a root to the node. Its length plus the offset of the root is the distance of the node, and its
nodes are exactly the nodes of the chain, the nodes that the marking run from the node reaches.

* `Net.parOf_iterate_root`: past a root the parent chain stays at the root.
* `Net.ExactSpec.chain_walk`: the walk along the parent chain from a root to a node of finite
  distance, with its length and its nodes.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Past a root, the parent chain stays at the root. -/
theorem Net.parOf_iterate_root {r : V → ℕ∞ × Option V} {v : V} {k : ℕ}
    (h : (r ((Net.parOf r)^[k] v)).2 = none) : ∀ m, (Net.parOf r)^[k + m] v = (Net.parOf r)^[k] v
  | 0 => rfl
  | m + 1 => by
    rw [← add_assoc, Function.iterate_succ_apply', Net.parOf_iterate_root h m]
    simp [Net.parOf, h]

/-- **The parent chain as a walk.** From a node `v` of finite distance, the parent chain leads to a
root after `k` steps, and read backwards it is a walk from the root to `v`. The offset of the root
plus the length of the walk is the distance of `v`, and the nodes of the walk are exactly the nodes
`parOf^[i] v`. -/
theorem Net.ExactSpec.chain_walk {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (v : V) (hv : (r v).1 ≠ ⊤) :
    ∃ (k : ℕ) (p : SsspFlow.Walk N.G.Adj ((Net.parOf r)^[k] v) v),
      (r ((Net.parOf r)^[k] v)).2 = none ∧ (r ((Net.parOf r)^[k] v)).1 = φ ((Net.parOf r)^[k] v) ∧
      offTop φ ((Net.parOf r)^[k] v) + p.wt (lenTop ℓ) = ((r v).1 : ℝ≥0∞) ∧
      ∀ y, y ∈ p.support ↔ ∃ i, (Net.parOf r)^[i] v = y := by
  obtain ⟨k, h1, h2, h3, h4⟩ := h.chain v hv
  have aux : ∀ i ≤ k, ∃ p : SsspFlow.Walk N.G.Adj ((Net.parOf r)^[i] v) v,
      p.wt (lenTop ℓ) = (((∑ j ∈ Finset.range i, ℓ ((Net.parOf r)^[j + 1] v) ((Net.parOf r)^[j] v)) : ℕ∞) :
        ℝ≥0∞) ∧
      ∀ y, y ∈ p.support ↔ ∃ j ≤ i, (Net.parOf r)^[j] v = y := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨.nil v, by simp [SsspFlow.Walk.wt], fun y => ?_⟩
      simp only [SsspFlow.Walk.support_nil, List.mem_singleton, Nat.le_zero, exists_eq_left,
        Function.iterate_zero, id_eq]
      exact eq_comm
    | succ i ih =>
      intro hi
      obtain ⟨p, hp, hs⟩ := ih (by omega)
      refine ⟨.cons (h3 i (by omega)).2 p, ?_, fun y => ?_⟩
      · rw [SsspFlow.Walk.wt_cons, hp, Finset.sum_range_succ, ENat.toENNReal_add, add_comm]
        rfl
      · rw [SsspFlow.Walk.support_cons, List.mem_cons, hs]
        constructor
        · rintro (rfl | ⟨j, hj, rfl⟩)
          · exact ⟨i + 1, le_rfl, rfl⟩
          · exact ⟨j, by omega, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
          · exact .inr ⟨j, by omega, rfl⟩
          · obtain rfl : j = i + 1 := by omega
            exact .inl rfl
  obtain ⟨p, hp, hs⟩ := aux k le_rfl
  refine ⟨k, p, h1, h2, ?_, fun y => ?_⟩
  · rw [hp, offTop, ← ENat.toENNReal_add, h4]
  · rw [hs]
    constructor
    · rintro ⟨j, -, hj⟩
      exact ⟨j, hj⟩
    · rintro ⟨i, rfl⟩
      rcases Nat.lt_or_ge i k with hik | hik
      · exact ⟨i, hik.le, rfl⟩
      · refine ⟨k, le_rfl, ?_⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hik
        exact (Net.parOf_iterate_root h1 m).symm

end Congest

end SsspFlow
