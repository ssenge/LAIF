import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Counting steps of the bounds for energy-constrained inner product estimation

The number of photon-number states of `m` modes with total photon number at most `K` is
`C(K + m, m)`. This file proves the bounds on it used in the lower bound
`Ω(((E - 1/2)/(100 ε))^{m/2}/ε)` and in the total-photon cutoff, and the scalar facts of the
proofs.
-/

namespace CVInner

/-- `C(K + m, m) = ∏_{j < m} (K + j + 1)/(j + 1)`. -/
theorem choose_eq_prod (K m : ℕ) :
    ((K + m).choose m : ℝ) = ∏ j ∈ Finset.range m, ((K : ℝ) + j + 1) / (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    have h := Nat.add_one_mul_choose_eq (K + m) m
    have h' : ((K + m + 1 : ℕ) : ℝ) * ((K + m).choose m : ℝ) =
        ((K + m + 1).choose (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h
    have e : K + (m + 1) = K + m + 1 := by ring
    rw [e]
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    push_cast at h'
    linarith

/-- `(1 + K/m)^m ≤ C(K + m, m)`. -/
theorem pow_le_choose (K m : ℕ) (hm : 0 < m) :
    (1 + (K : ℝ) / m) ^ m ≤ ((K + m).choose m : ℝ) := by
  rw [choose_eq_prod]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc (1 + (K : ℝ) / m) ^ m = ∏ _j ∈ Finset.range m, (1 + (K : ℝ) / m) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range m, ((K : ℝ) + j + 1) / (j + 1) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro j hj
        have hj' : (j : ℝ) + 1 ≤ m := by
          have := Finset.mem_range.mp hj; exact_mod_cast this
        have e : ((K : ℝ) + j + 1) / (j + 1) = 1 + (K : ℝ) / (j + 1) := by field_simp; ring
        rw [e]
        have : (K : ℝ) / m ≤ (K : ℝ) / (j + 1) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg K) (by positivity) hj'
        linarith

/-- `C(N - 1 + m, m) ≤ N^m` for `N ≥ 1`: the total-photon cutoff never exceeds the per-mode one. -/
theorem choose_le_pow (N m : ℕ) (hN : 1 ≤ N) : ((N - 1 + m).choose m : ℝ) ≤ (N : ℝ) ^ m := by
  rw [choose_eq_prod]
  calc ∏ j ∈ Finset.range m, (((N - 1 : ℕ) : ℝ) + j + 1) / (j + 1)
      ≤ ∏ _j ∈ Finset.range m, (N : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro j _
        rw [div_le_iff₀ (by positivity)]
        have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub hN]; simp
        rw [this]
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith [Nat.cast_nonneg (α := ℝ) j]
    _ = (N : ℝ) ^ m := by rw [Finset.prod_const, Finset.card_range]

/-- The shell size: with `b = m (E - 1/2)` and `K = ⌊b/(100 ε)⌋`, `1 + K/m ≥ (E - 1/2)/(100 ε)`. -/
theorem shell_base (m : ℕ) (hm : 0 < m) (E ε : ℝ) (hε : 0 < ε) (hE : 1 / 2 < E) :
    (E - 1 / 2) / (100 * ε) ≤ 1 + (⌊(m : ℝ) * (E - 1 / 2) / (100 * ε)⌋₊ : ℝ) / m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 ≤ (m : ℝ) * (E - 1 / 2) / (100 * ε) := by
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hfl := Nat.lt_floor_add_one ((m : ℝ) * (E - 1 / 2) / (100 * ε))
  set K := (⌊(m : ℝ) * (E - 1 / 2) / (100 * ε)⌋₊ : ℝ)
  have hK : (m : ℝ) * ((E - 1 / 2) / (100 * ε)) - 1 ≤ K := by
    have : (m : ℝ) * ((E - 1 / 2) / (100 * ε)) = (m : ℝ) * (E - 1 / 2) / (100 * ε) := by ring
    linarith
  rw [← sub_nonneg]
  have e : 1 + K / m - (E - 1 / 2) / (100 * ε) =
      (K - ((m : ℝ) * ((E - 1 / 2) / (100 * ε)) - 1) - 1 + m) / m := by
    field_simp; ring
  rw [e]
  apply div_nonneg _ (by linarith)
  linarith

/-- The small-dimension instance: for `0 < ε ≤ 10⁻⁴` the two states
`√(1 - a)|0⟩ + √a|1⟩`, `a ∈ {50ε, 53ε}`, have fidelity at least `1 - ε/20`. -/
theorem fallback_fidelity (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) :
    1 - ε / 20 ≤ (Real.sqrt ((1 - 50 * ε) * (1 - 53 * ε)) + Real.sqrt 2650 * ε) ^ 2 := by
  have hs : (51.478 : ℝ) ≤ Real.sqrt 2650 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hab : 0 ≤ (1 - 50 * ε) * (1 - 53 * ε) := by nlinarith
  have hr : 1 - 52 * ε ≤ Real.sqrt ((1 - 50 * ε) * (1 - 53 * ε)) := by
    rw [Real.le_sqrt (by nlinarith) hab]; nlinarith
  have h1 := Real.sq_sqrt hab
  have h2 : Real.sqrt 2650 ^ 2 = 2650 := Real.sq_sqrt (by norm_num)
  have hsq0 : 0 ≤ Real.sqrt ((1 - 50 * ε) * (1 - 53 * ε)) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt 2650 := Real.sqrt_nonneg _
  nlinarith [mul_le_mul hr hs (by norm_num) hsq0]

/-- The cutoff tail: with `N_c = ⌈4b/ε⌉` and `b > 0`, `b/N_c ≤ ε/4`. -/
theorem cutoff_tail (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    b / (⌈4 * b / ε⌉₊ : ℝ) ≤ ε / 4 := by
  have h := Nat.le_ceil (4 * b / ε)
  have hpos : 0 < 4 * b / ε := by positivity
  have hN : 0 < (⌈4 * b / ε⌉₊ : ℝ) := lt_of_lt_of_le hpos h
  rw [div_le_iff₀ hN]
  have : 4 * b ≤ ε * (⌈4 * b / ε⌉₊ : ℝ) := by
    rw [div_le_iff₀ hε] at h; linarith
  linarith

end CVInner
