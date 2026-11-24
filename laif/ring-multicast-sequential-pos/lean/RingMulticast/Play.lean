import RingMulticast.Structure

/-!
# Myopic sequential play has an outcome in every order

Each player, on arrival, takes its right path when that costs at most its left path, given the players that
arrived before it, and its left path otherwise. This defines choices `play a n t` by recursion on the arrival
time, and they are a result of myopic sequential play in the order t. So `Myopic a n t` is never empty.
-/

open Finset

namespace RingMulticast

/-- The choices of myopic sequential play in the order t, with ties broken to the right. -/
def play (a : ℕ → ℚ) (n : ℕ) (t : ℕ → ℕ) (i : ℕ) : Bool :=
  decide (rightCost a n (before t n i) (fun j => if _ : t j < t i then play a n t j else false) i
    ≤ leftCost a (before t n i) (fun j => if _ : t j < t i then play a n t j else false) i)
termination_by t i

theorem leftCost_congr (a : ℕ → ℚ) (S : Finset ℕ) (c c' : ℕ → Bool) (i : ℕ) (h : ∀ j ∈ S, c j = c' j) :
    leftCost a S c i = leftCost a S c' i := by
  unfold leftCost; exact sum_congr rfl fun k _ => share_congr a S c c' k h

theorem rightCost_congr (a : ℕ → ℚ) (n : ℕ) (S : Finset ℕ) (c c' : ℕ → Bool) (i : ℕ)
    (h : ∀ j ∈ S, c j = c' j) : rightCost a n S c i = rightCost a n S c' i := by
  unfold rightCost; exact sum_congr rfl fun k _ => share_congr a S c c' k h

theorem play_eq (a : ℕ → ℚ) (n : ℕ) (t : ℕ → ℕ) (i : ℕ) :
    play a n t i = decide (rightCost a n (before t n i) (play a n t) i ≤ leftCost a (before t n i) (play a n t) i) := by
  have h : ∀ j ∈ before t n i, (fun j => if _ : t j < t i then play a n t j else false) j = play a n t j := by
    intro j hj
    simp only [before, mem_filter] at hj
    simp [hj.2]
  rw [play, leftCost_congr a _ _ _ i h, rightCost_congr a n _ _ _ i h]

/-- Every order has an outcome of myopic sequential play. -/
theorem exists_myopic (a : ℕ → ℚ) (n : ℕ) (t : ℕ → ℕ) : ∃ c, Myopic a n t c := by
  refine ⟨play a n t, fun i _ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [play_eq] at h
    exact of_decide_eq_true h
  · rw [play_eq] at h
    exact le_of_lt (not_le.1 (of_decide_eq_false h))

end RingMulticast
