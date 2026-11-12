import Mathlib

/-!
# Testing concatenations of two palindromes by a hidden reflection

A word `w` of length `n` (read on the positions `0, ..., n - 1`) lies in `L_REV` if it is `u u^r v v^r` with
`u, v` nonempty. This file proves the combinatorial and Fourier facts behind a tester that finds the axis of
the reflection from coset states:

* `lrev_iff_axis`: for even `n`, `w ∈ L_REV` iff `w` is symmetric about an odd axis `c` with `c + 3 ≤ n`.
* `axisSym_iff_zmod`: the same symmetry read on `ZMod n`.
* `mismatch_le_two_dist`: the number of positions `i` with `x i ≠ x (c - i)` is at most twice the Hamming
  distance from `x` to any word symmetric about `c`.
* `mismatch_shift_axis`, `mismatch_shift_cyclic`: on a word symmetric about `c` (or a shift by `s`), the
  mismatches of another axis `c'` (shift `s'`) are the positions where `x i ≠ x (i + (c - c'))`.
* `dft_reflect`, `dft_shift`: the second half of the coset state has the first half's Fourier coefficient times
  the phase `ψ (-(k c))`.
* `fourier_autocorr`: summed over the values `v`, the products of the Fourier coefficients of the level sets,
  weighted by `ψ (k d)`, give `n` times the number of `a` with `x a = x (a + d)`.
* `union_const`, `union_const_shift`, `check_consts`: the constants of the error bounds.
-/

namespace PalinTest

open Finset

/-- `w` read on `0, ..., n - 1` is `u u^r v v^r` with `|u| = p ≥ 1` and `|v| = q ≥ 1`: an even palindrome of
length `2p` followed by an even palindrome of length `2q`. -/
def LRev {α : Type*} (n : ℕ) (w : ℕ → α) : Prop :=
  ∃ p q, 0 < p ∧ 0 < q ∧ n = 2 * p + 2 * q ∧
    (∀ i < 2 * p, w i = w (2 * p - 1 - i)) ∧
    (∀ i < 2 * q, w (2 * p + i) = w (2 * p + 2 * q - 1 - i))

/-- The cyclic word `w` of length `n` is symmetric about the axis `c`: `w i = w (c - i mod n)`. -/
def AxisSym {α : Type*} (n c : ℕ) (w : ℕ → α) : Prop :=
  ∀ i < n, w i = w ((c + n - i) % n)

theorem lrev_iff_axis {α : Type*} (n : ℕ) (hn : Even n) (w : ℕ → α) :
    LRev n w ↔ ∃ c, c % 2 = 1 ∧ c + 3 ≤ n ∧ AxisSym n c w := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl, h1, h2⟩
    refine ⟨2 * p - 1, by omega, by omega, fun i hi => ?_⟩
    by_cases hi' : i < 2 * p
    · have e : (2 * p - 1 + (2 * p + 2 * q) - i) % (2 * p + 2 * q) = 2 * p - 1 - i := by
        rw [show 2 * p - 1 + (2 * p + 2 * q) - i = (2 * p - 1 - i) + (2 * p + 2 * q) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [e]; exact h1 i hi'
    · have e : (2 * p - 1 + (2 * p + 2 * q) - i) % (2 * p + 2 * q) = 2 * p + 2 * q - 1 - (i - 2 * p) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [e]
      have := h2 (i - 2 * p) (by omega)
      rwa [show 2 * p + (i - 2 * p) = i by omega] at this
  · rintro ⟨c, hc, hcn, hs⟩
    obtain ⟨r, hr⟩ := hn
    refine ⟨(c + 1) / 2, (n - c - 1) / 2, by omega, by omega, by omega, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hs i (by omega)]; congr 1
      rw [show c + n - i = (c - i) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hs (2 * ((c + 1) / 2) + i) (by omega)]; congr 1
      rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem axisSym_iff_zmod {α : Type*} (n c : ℕ) [NeZero n] (w : ℕ → α) :
    AxisSym n c w ↔ ∀ j : ZMod n, w j.val = w ((c : ZMod n) - j).val := by
  have key : ∀ j : ZMod n, ((c : ZMod n) - j).val = (c + n - j.val) % n := by
    intro j
    have hj := ZMod.val_lt j
    rw [← ZMod.val_natCast n (c + n - j.val)]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  constructor
  · intro h j; rw [key]; exact h j.val (ZMod.val_lt j)
  · intro h i hi
    have := h (i : ZMod n)
    rwa [key, ZMod.val_natCast, Nat.mod_eq_of_lt hi] at this

variable {n : ℕ} [NeZero n] {α : Type*} [DecidableEq α]

/-- Soundness of the classical check: the mismatched positions of the axis `c` number at most twice the
distance from `x` to any word `y` symmetric about `c`. -/
theorem mismatch_le_two_dist (c : ZMod n) (x y : ZMod n → α) (hy : ∀ i, y i = y (c - i)) :
    (univ.filter fun i => x i ≠ x (c - i)).card ≤ 2 * (univ.filter fun i => x i ≠ y i).card := by
  set D := univ.filter fun i => x i ≠ y i
  have hsub : (univ.filter fun i => x i ≠ x (c - i)) ⊆ D ∪ D.image (fun j => c - j) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_union, mem_image, D, mem_filter, mem_univ, true_and]
    by_cases h1 : x i = y i
    · by_cases h2 : x (c - i) = y (c - i)
      · exact absurd (by rw [h1, h2, ← hy i]) hi
      · exact Or.inr ⟨c - i, h2, sub_sub_cancel c i⟩
    · exact Or.inl h1
  calc _ ≤ (D ∪ D.image (fun j => c - j)).card := card_le_card hsub
    _ ≤ D.card + (D.image (fun j => c - j)).card := card_union_le _ _
    _ ≤ D.card + D.card := Nat.add_le_add_left card_image_le _
    _ = 2 * D.card := by ring

/-- On a word symmetric about `c`, the axis `c'` fails exactly where `x i ≠ x (i + (c - c'))`. -/
theorem mismatch_shift_axis (c c' : ZMod n) (x : ZMod n → α) (hx : ∀ i, x i = x (c - i)) :
    (univ.filter fun i => x i ≠ x (c' - i)) = (univ.filter fun i => x i ≠ x (i + (c - c'))) := by
  refine filter_congr fun i _ => ?_
  rw [hx (c' - i), show c - (c' - i) = i + (c - c') by ring]

/-- On `y i = x (i + s)`, the shift `s'` fails exactly where `x (i + s) ≠ x (i + s')`. -/
theorem mismatch_shift_cyclic (s s' : ZMod n) (x y : ZMod n → α) (hy : ∀ i, y i = x (i + s)) :
    (univ.filter fun i => y i ≠ x (i + s')) = (univ.filter fun i => x (i + s) ≠ x (i + s')) := by
  refine filter_congr fun i _ => ?_
  rw [hy i]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod n) ℂ)

/-- The reflected half of the coset state: if `x` is symmetric about `c`, the Fourier coefficient of the level
set `{j : x (-j) = v}` is the one of `{a : x a = v}` times `ψ (-(k c))`. -/
theorem dft_reflect (c k : ZMod n) (x : ZMod n → α) (hx : ∀ i, x i = x (c - i)) (v : α) :
    ∑ j, (if x (-j) = v then ψ (k * j) else 0) = ψ (-(k * c)) * ∑ a, (if x a = v then ψ (k * a) else 0) := by
  rw [← Equiv.sum_comp (Equiv.addRight c) (fun a => if x a = v then ψ (k * a) else 0), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  show _ = ψ (-(k * c)) * (if x (j + c) = v then ψ (k * (j + c)) else 0)
  have h1 : x (-j) = x (j + c) := by rw [hx (-j)]; ring_nf
  have h2 : ψ (k * j) = ψ (-(k * c)) * ψ (k * (j + c)) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  by_cases h : x (j + c) = v
  · simp only [h1, h, if_true, h2]
  · simp only [h1, h, if_false, mul_zero]

/-- The shifted half of the coset state: if `y i = x (i + s)`, the Fourier coefficient of `{j : y j = v}` is the
one of `{a : x a = v}` times `ψ (-(k s))`. -/
theorem dft_shift (s k : ZMod n) (x y : ZMod n → α) (hy : ∀ i, y i = x (i + s)) (v : α) :
    ∑ j, (if y j = v then ψ (k * j) else 0) = ψ (-(k * s)) * ∑ a, (if x a = v then ψ (k * a) else 0) := by
  rw [← Equiv.sum_comp (Equiv.addRight s) (fun a => if x a = v then ψ (k * a) else 0), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  show _ = ψ (-(k * s)) * (if x (j + s) = v then ψ (k * (j + s)) else 0)
  have h2 : ψ (k * j) = ψ (-(k * s)) * ψ (k * (j + s)) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  by_cases h : x (j + s) = v
  · simp only [hy j, h, if_true, h2]
  · simp only [hy j, h, if_false, mul_zero]

/-- The law of the Fourier sample is the autocorrelation: summed over the values `v`, the products of the
Fourier coefficients of the level set `{a : x a = v}` at `k` and `-k`, weighted by `ψ (k d)`, give
`n · #{a : x a = x (a + d)}`. -/
theorem fourier_autocorr [Fintype α] (x : ZMod n → α) (d : ZMod n) :
    ∑ v : α, ∑ k : ZMod n, (∑ a, if x a = v then ψ (k * a) else 0) *
      (∑ a, if x a = v then ψ (-(k * a)) else 0) * ψ (k * d) =
      n * (univ.filter fun a => x a = x (a + d)).card := by
  have orth : ∀ t : ZMod n, ∑ k : ZMod n, ψ (k * t) = if t = 0 then (n : ℂ) else 0 := by
    intro t
    rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar n), ZMod.card]
    split_ifs <;> simp
  have step : ∀ v : α, ∑ k : ZMod n, (∑ a, if x a = v then ψ (k * a) else 0) *
      (∑ a, if x a = v then ψ (-(k * a)) else 0) * ψ (k * d) =
      ∑ a, ∑ b, if x a = v ∧ x b = v then (if a - b + d = 0 then (n : ℂ) else 0) else 0 := by
    intro v
    have : ∀ k : ZMod n, (∑ a, if x a = v then ψ (k * a) else 0) *
        (∑ a, if x a = v then ψ (-(k * a)) else 0) * ψ (k * d) =
        ∑ a, ∑ b, if x a = v ∧ x b = v then ψ (k * (a - b + d)) else 0 := by
      intro k
      rw [sum_mul_sum, sum_mul]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun b _ => ?_
      split_ifs with h1 h2 h3 h3 <;> try simp_all
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; ring_nf
    rw [sum_congr rfl fun k _ => this k, sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    by_cases h : x a = v ∧ x b = v
    · simp only [ite_cond_eq_true _ _ (eq_true h)]; exact orth _
    · simp [h]
  rw [sum_congr rfl fun v _ => step v]
  have inner : ∀ v : α, (∑ a, ∑ b, if x a = v ∧ x b = v then (if a - b + d = 0 then (n : ℂ) else 0) else 0) =
      ∑ a, if x a = v ∧ x (a + d) = v then (n : ℂ) else 0 := by
    intro v
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single (a + d)]
    · simp
    · intro b hb
      have : a - b + d ≠ 0 := by intro h; exact hb (by linear_combination -h)
      simp [this]
  rw [sum_congr rfl fun v _ => inner v, sum_comm]
  rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single (x a)]
  · by_cases h : x a = x (a + d) <;> simp [h, eq_comm]
  · intro v hv; simp [Ne.symm hv]

/-- Union bound of the axis comparison: with `T ≥ 58 ln(3n)/(3ε)`, the at most `n/2` bad axes, each beating the
true axis with probability at most `e^{-3Tε/58}`, do so with total probability at most `1/6`. -/
theorem union_const (n : ℕ) (hn : 0 < n) (ε T : ℝ) (hε : 0 < ε)
    (hT : 58 * Real.log (3 * n) / (3 * ε) ≤ T) :
    (n : ℝ) / 2 * Real.exp (-(3 * T * ε / 58)) ≤ 1 / 6 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (3 * n) ≤ 3 * T * ε / 58 := by
    rw [div_le_iff₀ (by positivity)] at hT; linarith
  have h2 : Real.exp (-(3 * T * ε / 58)) ≤ 1 / (3 * n) := by
    rw [one_div, ← Real.exp_log (by positivity : (0 : ℝ) < 3 * n), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  calc (n : ℝ) / 2 * Real.exp (-(3 * T * ε / 58)) ≤ n / 2 * (1 / (3 * n)) := by gcongr
    _ = 1 / 6 := by field_simp; ring

/-- Union bound for cyclic shifts: with `T ≥ 116 ln(6n)/(3ε)`, the at most `n` bad shifts, each beating the true
shift with probability at most `e^{-3Tε/116}`, do so with total probability at most `1/6`. -/
theorem union_const_shift (n : ℕ) (hn : 0 < n) (ε T : ℝ) (hε : 0 < ε)
    (hT : 116 * Real.log (6 * n) / (3 * ε) ≤ T) :
    (n : ℝ) * Real.exp (-(3 * T * ε / 116)) ≤ 1 / 6 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (6 * n) ≤ 3 * T * ε / 116 := by
    rw [div_le_iff₀ (by positivity)] at hT; linarith
  have h2 : Real.exp (-(3 * T * ε / 116)) ≤ 1 / (6 * n) := by
    rw [one_div, ← Real.exp_log (by positivity : (0 : ℝ) < 6 * n), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  calc (n : ℝ) * Real.exp (-(3 * T * ε / 116)) ≤ n * (1 / (6 * n)) := by gcongr
    _ = 1 / 6 := by field_simp

/-- The two tails of the classical check: `e^{-8/3} < 1/10` and `e^{-2} < 1/6`. -/
theorem check_consts : Real.exp (-(8 / 3)) < 1 / 10 ∧ Real.exp (-2) < 1 / 6 := by
  have e1 := Real.exp_one_gt_d9
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have e23 : 2 / 3 + 1 ≤ Real.exp (2 / 3) := Real.add_one_le_exp _
  have e83 : Real.exp (8 / 3) = Real.exp 2 * Real.exp (2 / 3) := by rw [← Real.exp_add]; norm_num
  have h2 : 7 < Real.exp 2 := by rw [e2]; nlinarith
  constructor
  · rw [Real.exp_neg, e83]
    have : 10 < Real.exp 2 * Real.exp (2 / 3) := by nlinarith
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num; linarith
  · rw [Real.exp_neg, inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num; linarith

end PalinTest
