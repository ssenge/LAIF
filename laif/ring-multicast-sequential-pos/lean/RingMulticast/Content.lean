import RingMulticast.Mirror

/-!
# The choice of the order matters

On the ring with edge costs 6, 10, 3, 10 (three players, the instance with ratio 26/19 of [1]), the order 0, 1, 2
has a result of myopic sequential play (players 0 and 1 go left, player 2 goes right, ties at players 1 and 2) of
cost 26, while every player going left costs 19, and 3 · 26 > 4 · 19. So the bound of `sequential_pos` does not
hold for every order, and the order it provides is a real choice.
-/

open Finset

namespace RingMulticast

/-- Edge costs 6, 10, 3, 10. -/
def a26 (k : ℕ) : ℚ := if k = 0 then 6 else if k = 1 then 10 else if k = 2 then 3 else if k = 3 then 10 else 0

/-- Players 0 and 1 go left, player 2 goes right. -/
def c26 (j : ℕ) : Bool := decide (j = 2)

theorem myopic_c26 : Myopic a26 3 (fun j => j) c26 := by
  intro i hi
  interval_cases i <;>
    simp (config := {decide := true}) [leftCost, rightCost, share, users, before, usesB, c26, a26, Finset.sum_range_succ,
      Finset.sum_Ico_succ_top, Finset.filter_insert, Finset.range_add_one, Finset.filter_singleton] <;> norm_num

theorem netCost_c26 : netCost a26 3 c26 = 26 := by
  simp (config := {decide := true}) [netCost, users, usesB, c26, a26, Finset.sum_range_succ, Finset.filter_insert, Finset.range_add_one, Finset.filter_singleton]
  norm_num

theorem netCost_left : netCost a26 3 (fun _ => false) = 19 := by
  simp (config := {decide := true}) [netCost, users, usesB, a26, Finset.sum_range_succ, Finset.filter_insert, Finset.range_add_one, Finset.filter_singleton]
  norm_num

/-- Some order has a result of myopic sequential play that costs more than 4/3 of another network. -/
theorem order_matters : ∃ (a : ℕ → ℚ) (t : ℕ → ℕ) (c c' : ℕ → Bool), (∀ k, 0 ≤ a k) ∧
    Set.InjOn t (Set.Iio 3) ∧ Myopic a 3 t c ∧ 4 * netCost a 3 c' < 3 * netCost a 3 c := by
  refine ⟨a26, fun j => j, c26, fun _ => false, fun k => ?_, fun i _ j _ h => h, myopic_c26, ?_⟩
  · unfold a26; split_ifs <;> norm_num
  · rw [netCost_c26, netCost_left]; norm_num

end RingMulticast
