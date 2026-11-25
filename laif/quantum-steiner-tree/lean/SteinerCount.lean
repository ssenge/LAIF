import Mathlib

/-!
# Counting the index states of a balanced split superposition

For `k = 2^m` terminals, exact halving at every node of the unrolled split recursion gives `N m` index states, with
`N (m + 1) = C(2^(m+1), 2^m) · (N m)²`: one split at the root and an independent superposition for each half. One
binomial coefficient per level gives `S (m + 1) = C(2^(m+1), 2^m) · S m` instead.

* `N_eq_factorial`: `N m = (2^m)!`.
* `S_le`: `S m ≤ 4^(2^m)`, so one coefficient per level is at most `4^k`.
* `four_pow_lt_N`: `4^(2^m) < N m` for `m ≥ 4`, that is `k! > 4^k` from `k = 16` on.
* `N_three_lt_four_pow`: the reverse strict inequality at `m = 3`, so the range `m ≥ 4` is needed.
* `S_two`, `N_two`: `S 2 = 12` and `N 2 = 24`.
-/

namespace SteinerCount

open Nat

/-- Index states of the superposition with one split per node. -/
def N : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 ^ (m + 1)).choose (2 ^ m) * N m ^ 2

/-- One binomial coefficient per level. -/
def S : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 ^ (m + 1)).choose (2 ^ m) * S m

theorem N_eq_factorial (m : ℕ) : N m = (2 ^ m)! := by
  induction m with
  | zero => simp [N]
  | succ m ih =>
    have hle : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsub : 2 ^ (m + 1) - 2 ^ m = 2 ^ m := by rw [pow_succ]; omega
    have h := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at h
    rw [N, ih, ← h]; ring

theorem S_le (m : ℕ) : S m ≤ 4 ^ (2 ^ m) := by
  have key : S m ≤ 2 ^ (2 ^ (m + 1)) := by
    induction m with
    | zero => simp [S]
    | succ m ih =>
      calc S (m + 1) = (2 ^ (m + 1)).choose (2 ^ m) * S m := rfl
        _ ≤ 2 ^ (2 ^ (m + 1)) * 2 ^ (2 ^ (m + 1)) :=
            Nat.mul_le_mul (Nat.choose_le_two_pow _ _) ih
        _ = 2 ^ (2 ^ (m + 1 + 1)) := by rw [← pow_add, pow_succ 2 (m + 1)]; ring_nf
  calc S m ≤ 2 ^ (2 ^ (m + 1)) := key
    _ = 4 ^ (2 ^ m) := by rw [pow_succ, pow_mul']; norm_num

theorem four_pow_lt_N (m : ℕ) (hm : 4 ≤ m) : 4 ^ (2 ^ m) < N m := by
  induction m, hm using Nat.le_induction with
  | base => rw [N_eq_factorial]; decide
  | succ m _ ih =>
    have hpos : 0 < (2 ^ (m + 1)).choose (2 ^ m) :=
      Nat.choose_pos (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc 4 ^ (2 ^ (m + 1)) = (4 ^ (2 ^ m)) ^ 2 := by rw [pow_succ, pow_mul]
      _ < N m ^ 2 := Nat.pow_lt_pow_left ih (by norm_num)
      _ ≤ (2 ^ (m + 1)).choose (2 ^ m) * N m ^ 2 := Nat.le_mul_of_pos_left _ hpos
      _ = N (m + 1) := rfl

/-- Non-vacuity of `four_pow_lt_N`: the bound fails at `m = 3` (`8! = 40320 < 4^8 = 65536`), so `m ≥ 4` is needed. -/
theorem N_three_lt_four_pow : N 3 < 4 ^ (2 ^ 3) := by rw [N_eq_factorial]; decide

/-- Non-vacuity of `S_le` and `N_eq_factorial`: small values, `S 2 = 12 ≤ 4^4` and `N 2 = 24 = 4!`. -/
theorem S_two : S 2 = 12 := by decide

theorem N_two : N 2 = 24 := by decide

end SteinerCount
