import Mathlib

/-!
# Max 2-SAT and Max 2-CSP in terms of the number of constraints: the constants

The quantum bounds are the square roots of the classical ones. These certificates check the rounded
bases and the weights of the cubic separator algorithm.

- `maxtwosat_cert`: `2 ^ (11 / 139) ≤ 1.0564`, as `2 ^ 11 ≤ 1.0564 ^ 139`. The weight of Max 2-SAT is
  `0.15820` up to its last printed digit, below `22 / 139 = 0.15827`.
- `maxtwocsp_cert`: `2 ^ (9 / 100) ≤ 1.0644`, `2 ^ (7 / 80) ≤ 1.0626` and `2 ^ (1 / 10) ≤ 1.0718`, as
  integer powers.
- `smc_weights`: the weights `(w_r, w_s, w_{s,2}, w_b, w_c) = (1/5, 7/10, 3/5, 1/5, 1/10)` satisfy the
  linear constraints of the measure of the cubic separator algorithm, with the separator constant at
  `1/6`, and give `w_r * (2/3) = 2/15` and `1/8 + (3/8) * (2/15) = 7/40`.
-/

/-- The base for Max 2-SAT: `2 ^ (11 / 139) ≤ 1.0564`. -/
theorem maxtwosat_cert : (2 : ℝ) ^ 11 ≤ (10564 / 10000) ^ 139 ∧ (15820 : ℚ) / 100000 ≤ 22 / 139 := by
  norm_num

/-- The bases for Max 2-CSP: general, maximum degree 4, and cubic in terms of vertices. -/
theorem maxtwocsp_cert :
    (2 : ℝ) ^ 9 ≤ (10644 / 10000) ^ 100 ∧ (2 : ℝ) ^ 7 ≤ (10626 / 10000) ^ 80 ∧
      (2 : ℝ) ≤ (10718 / 10000) ^ 10 := by norm_num

/-- The weights of the cubic separator algorithm satisfy its constraints. -/
theorem smc_weights (wr ws ws2 wb wc : ℚ) (hr : wr = 1 / 5) (hs : ws = 7 / 10) (hs2 : ws2 = 3 / 5)
    (hb : wb = 1 / 5) (hc : wc = 1 / 10) :
    -wb + wc ≤ 0 ∧ -ws + ws2 ≤ 0 ∧ -wr + wc ≤ 0 ∧ -wr + wb - wc ≤ 0 ∧
      (1 / 6) * ws + (5 / 12) * wr ≤ wr ∧
      -ws2 + ws - wb + wc ≤ 0 ∧ -ws2 + ws - wr + wc ≤ 0 ∧ -ws2 + ws - wr + wb - wc ≤ 0 ∧
      -ws + wr ≤ 0 ∧ -ws + wc ≤ 0 ∧ -ws + wb - wc ≤ 0 ∧
      1 - 2 * ws + ws2 - wr ≤ 0 ∧ 1 - ws - wr - wb + wc ≤ 0 ∧ 1 - ws - wr - wc ≤ 0 ∧
      -wr + wb ≤ 0 ∧ 1 - ws - 2 * wr - wc + wb ≤ 0 ∧ 1 - ws - 2 * wr + wc ≤ 0 ∧
      wr * (2 / 3) = 2 / 15 ∧ (1 : ℚ) / 8 + (3 / 8) * (2 / 15) = 7 / 40 := by
  subst hr hs hs2 hb hc
  norm_num
