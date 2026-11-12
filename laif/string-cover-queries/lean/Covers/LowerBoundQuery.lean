import Covers.LowerBound
import Covers.Model

/-!
# The query lower bound, from the OR bound

Binary strings are bit strings `x : Fin n → Bool`, and a query to `x` is a query to the string, so the family of the
notes is literally the OR promise: the zero string is `falseⁿ`, and `singleBit i` is `falseⁿ` with `true` at `i`.
-/

namespace Strings

theorem ofFn_false (n : ℕ) : List.ofFn (fun _ : Fin n => false) = List.replicate n false := by
  simp [List.ofFn_const]

theorem ofFn_singleBit {n : ℕ} (i : Fin n) : List.ofFn (singleBit i) = oneB n i false true := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · by_cases hji : j = i
    · subst hji
      rw [oneB_getElem?_self i.2, List.getElem?_ofFn]
      simp [hj, singleBit]
    · rw [oneB_getElem?_of_ne hj hji, List.getElem?_ofFn]
      have : (⟨j, hj⟩ : Fin n) ≠ i := fun h => hji (congrArg Fin.val h)
      simp [hj, singleBit, this]
  · rw [List.getElem?_eq_none (by simpa using hj), List.getElem?_eq_none (by simpa using hj)]

/-- The string `x` has shortest cover of length other than 1. -/
def NoUnitCover {n : ℕ} (x : Fin n → Bool) : Prop :=
  ∀ C, IsShortestCover C (List.ofFn x) → C.length ≠ 1

open Classical in
/-- `A` tells, with error at most `1/3`, whether the shortest cover of its input has length other than 1. -/
def DecidesNoUnitCover {n T : ℕ} {St : Type} [Fintype St] [DecidableEq St] (A : QAlg (Fin n) T St Bool) : Prop :=
  ∀ x : Fin n → Bool, 2 / 3 ≤ A.prob x (decide (NoUnitCover x))

/-- **The lower bound of the README, on binary strings.** An algorithm that tells whether the shortest cover has length 1
needs `c √n` queries, given the OR lower bound with constant `c`. An algorithm that outputs the shortest cover length
gives such an algorithm with the same queries. -/
theorem cover_lower_bound {c : ℝ} (hOR : ORBound c) {n T : ℕ} (hn : 2 ≤ n) {St : Type} [Fintype St]
    [DecidableEq St] (A : QAlg (Fin n) T St Bool) (hA : DecidesNoUnitCover A) : c * Real.sqrt n ≤ T := by
  classical
  refine hOR n T St _ _ A ?_ fun i => ?_
  · have hno : ¬ NoUnitCover (fun _ : Fin n => false) := fun h => by
      refine h [false] ?_ rfl
      rw [ofFn_false]
      exact replicate_shortestCover (by omega) false
    have := hA (fun _ => false)
    rwa [decide_eq_false hno] at this
  · have hyes : NoUnitCover (singleBit i) := fun C hC => by
      rw [ofFn_singleBit] at hC
      exact oneB_shortest_length_ne_one (by simp) i.2 hn hC
    have := hA (singleBit i)
    rwa [decide_eq_true hyes] at this

end Strings
