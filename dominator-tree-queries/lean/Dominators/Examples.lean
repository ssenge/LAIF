import Dominators.Kosaraju
import Dominators.LengauerTarjan

/-!
# Running the algorithms

A plain scan meets the search specification and the minimum specification, so the algorithms can be run. The
`#guard` lines are checked when this file is built, and a wrong answer fails the build. They are sanity checks:
the theorems are in the other files.
-/

namespace Dominators

universe u

variable {V : Type u} [DecidableEq V]

/-- Search by scanning a list of all vertices. -/
def linSearch (adj : V → V → Bool) (vs : List V) (v : V) (S : Finset V) : Option V :=
  vs.find? (fun w => adj v w && decide (w ∉ S))

theorem linSearch_spec (adj : V → V → Bool) {vs : List V} (hvs : ∀ x, x ∈ vs) :
    IsSearch (fun a b => adj a b = true) (linSearch adj vs) where
  found := by
    intro v S w h
    have := List.find?_some h
    simpa using this
  none := by
    intro v S h w he
    have := List.find?_eq_none.mp h w (hvs w)
    simp only [he, Bool.true_and, decide_eq_true_eq, not_not] at this
    exact this

/-- Minimum over predecessors by scanning a list of all vertices. -/
def linMin (adj : V → V → Bool) (vs : List V) (w : V) (f : V → WithTop ℕ) : WithTop ℕ :=
  vs.foldr (fun v acc => if adj v w = true then min (f v) acc else acc) ⊤

omit [DecidableEq V] in
theorem linMin_list (adj : V → V → Bool) (vs : List V) (w : V) (f : V → WithTop ℕ) :
    (∀ v ∈ vs, adj v w = true → linMin adj vs w f ≤ f v) ∧
      (linMin adj vs w f = ⊤ ∨ ∃ v, adj v w = true ∧ linMin adj vs w f = f v) := by
  induction vs with
  | nil => simp [linMin]
  | cons a as ih =>
    obtain ⟨h1, h2⟩ := ih
    have hfold : linMin adj (a :: as) w f =
        if adj a w = true then min (f a) (linMin adj as w f) else linMin adj as w f := rfl
    rw [hfold]
    by_cases ha : adj a w = true
    · simp only [ha, ite_true]
      constructor
      · intro v hv _
        rcases List.mem_cons.mp hv with rfl | hv
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (h1 v hv (by assumption))
      · rcases le_total (f a) (linMin adj as w f) with hle | hle
        · rw [min_eq_left hle]
          exact Or.inr ⟨a, ha, rfl⟩
        · rw [min_eq_right hle]
          exact h2
    · simp only [ha]
      constructor
      · intro v hv hvw
        rcases List.mem_cons.mp hv with rfl | hv
        · exact absurd hvw ha
        · exact h1 v hv hvw
      · exact h2

omit [DecidableEq V] in
theorem linMin_spec (adj : V → V → Bool) {vs : List V} (hvs : ∀ x, x ∈ vs) :
    IsMinFind (fun a b => adj a b = true) (linMin adj vs) where
  lower := fun w f v he => (linMin_list adj vs w f).1 v (hvs v) he
  attained := fun w f => (linMin_list adj vs w f).2

/-- The reverse adjacency. -/
def revAdj (adj : V → V → Bool) : V → V → Bool := fun a b => adj b a

/-- An adjacency from a list of edges. -/
def adjOf {n : ℕ} (es : List (Fin n × Fin n)) : Fin n → Fin n → Bool := fun a b => decide ((a, b) ∈ es)

/-- `0 → 1 → 2 → 3`, `0 → 4 → 3`, `3 → 5`, `5 → 2`, with `6` unreachable and `6 → 3`. -/
def exAdj : Fin 7 → Fin 7 → Bool := adjOf [(0, 1), (1, 2), (2, 3), (0, 4), (4, 3), (3, 5), (5, 2), (6, 3)]

/-- The dominator algorithm on the example, with scans for the searches. -/
def exIdom : Fin 7 → Option (Fin 7) :=
  dominators (linSearch exAdj (List.finRange 7)) (linMin exAdj (List.finRange 7)) 14 0

#guard exIdom 0 == none
#guard exIdom 1 == some 0
#guard exIdom 2 == some 0
#guard exIdom 3 == some 0
#guard exIdom 4 == some 0
#guard exIdom 5 == some 3
#guard exIdom 6 == none

/-- Kosaraju on the example: `{2, 3, 5}` is a cycle, and the rest are singletons. -/
def exComps : List (Finset (Fin 7)) :=
  (kosaraju (linSearch exAdj (List.finRange 7)) (linSearch (revAdj exAdj) (List.finRange 7)) 14
    (List.finRange 7)).1

#guard exComps.length == 5
#guard exComps.any (· == {2, 3, 5})

end Dominators
