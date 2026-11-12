import Mathlib

/-!
# Scalar steps of the rank-sensitive bounds for shadow U-statistics

* `cd_lt_three`, `scalar_moment_le`, `operator_moment_le`: the constant `c_d = (3d + 4)/(d + 2) < 3`
  and the scalar arithmetic that turns the exact third moments of one shadow into the bounds
  `E[X C X] ⪯ c_d tr(C) I` and `E |tr(X M)|² ≤ c_d ‖M‖₂²`.
* `power_trace_le`, `chain_product_le`: `tr A^{2e} ≤ s Δ^{2e}` for `s` eigenvalues in `[0, Δ]`,
  and the product `∏ ‖B_i‖₂² ≤ s^j Δ^{2(k-j)}` when the exponents add up to `k - j`.
* `avg_sq_le`: the mean square of an average is at most the average of the mean squares.
* `order_term_le`, `geom_tail_le`: the order-`j` term of the variance bound in the entropy
  corollary and the geometric sum over the orders `j ≥ 2`.
-/

namespace ShadowUStat

open Finset

theorem cd_lt_three (d : ℝ) (hd : 0 ≤ d) : (3 * d + 4) / (d + 2) < 3 := by
  rw [div_lt_iff₀ (by linarith)]; linarith

/-- The scalar bound: with `F = ‖M‖₂²`, `T = tr((M M† + M† M) ρ) ≤ 2F`, `x = |t|² + 2 Re(t ū)
≥ -|u|²` and `|u|² ≤ F`, the second moment is at most `c_d F`. -/
theorem scalar_moment_le (d F T x u2 : ℝ) (hd : 0 ≤ d) (hT : T ≤ 2 * F) (hx : -u2 ≤ x)
    (hu : u2 ≤ F) :
    (d + 1) / (d + 2) * (F + T) - x / (d + 2) ≤ (3 * d + 4) / (d + 2) * F := by
  have h2 : 0 < d + 2 := by linarith
  rw [div_mul_eq_mul_div, div_sub_div_same, div_mul_eq_mul_div, div_le_div_iff_of_pos_right h2]
  nlinarith

/-- The operator bound in eigenvalue form: with `a = tr C`, the terms `tr C (I + ρ) + tr(C ρ) I`
are at most `3a` and `-(C + C ρ + ρ C) ⪯ ρ C ρ` is at most `a`. -/
theorem operator_moment_le (d a y z : ℝ) (hd : 0 ≤ d) (hy : y ≤ 3 * a) (hz : z ≤ a) :
    (d + 1) / (d + 2) * y + z / (d + 2) ≤ (3 * d + 4) / (d + 2) * a := by
  have h2 : 0 < d + 2 := by linarith
  rw [div_mul_eq_mul_div, ← add_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right h2]
  nlinarith

/-- `tr A^{2e} ≤ s Δ^{2e}` for `s` eigenvalues in `[0, Δ]`. -/
theorem power_trace_le (s e : ℕ) (Δ : ℝ) (lam : Fin s → ℝ) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∀ i, lam i ≤ Δ) : ∑ i, lam i ^ (2 * e) ≤ s * Δ ^ (2 * e) := by
  calc ∑ i, lam i ^ (2 * e) ≤ ∑ _i : Fin s, Δ ^ (2 * e) :=
        sum_le_sum fun i _ => pow_le_pow_left₀ (h0 i) (h1 i) _
    _ = s * Δ ^ (2 * e) := by simp

/-- The product of the norms in a chain: if `0 ≤ b i ≤ s Δ^{2 e_i}` and `∑ e_i = k - j`, then
`∏ b_i ≤ s^j Δ^{2(k-j)}`. -/
theorem chain_product_le (j m : ℕ) (s Δ : ℝ) (e : Fin j → ℕ)
    (he : ∑ i, e i = m) (b : Fin j → ℝ) (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ i, b i ≤ s * Δ ^ (2 * e i)) : ∏ i, b i ≤ s ^ j * Δ ^ (2 * m) := by
  calc ∏ i, b i ≤ ∏ i, (s * Δ ^ (2 * e i)) :=
        prod_le_prod₀ (fun i _ => hb0 i) (fun i _ => hb i)
    _ = s ^ j * Δ ^ (2 * m) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
          ← mul_sum, he]

/-- Convexity: `(∑ w_i a_i)² ≤ ∑ w_i a_i²` for weights `w ≥ 0` with `∑ w_i = 1`. -/
theorem avg_sq_le {ι : Type*} (S : Finset ι) (w a : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hsum : ∑ i ∈ S, w i = 1) : (∑ i ∈ S, w i * a i) ^ 2 ≤ ∑ i ∈ S, w i * a i ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * a i)
  have e1 : ∀ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * a i) = w i * a i := by
    intro i hi; rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have e2 : ∀ i ∈ S, Real.sqrt (w i) ^ 2 = w i := fun i hi => Real.sq_sqrt (hw i hi)
  have e3 : ∀ i ∈ S, (Real.sqrt (w i) * a i) ^ 2 = w i * a i ^ 2 := by
    intro i hi; rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3, hsum, one_mul] at h
  exact h

/-- The order-`j` term (`j = i + 1`) of the variance bound in the entropy corollary: if
`S Δ^i ≤ c'` and `(N/L)^{i+1} ≤ C`, then `(c s)^{i+1} S² / C ≤ c'² (c s L/N) β^i` with
`β = c s L / (N Δ²)`. -/
theorem order_term_le (i : ℕ) (c s L N Δ S c' Cn : ℝ) (hc : 0 < c) (hs : 0 < s) (hL : 0 < L)
    (hN : 0 < N) (hΔ : 0 < Δ) (hS0 : 0 ≤ S) (hS : S * Δ ^ i ≤ c') (hC : (N / L) ^ (i + 1) ≤ Cn) :
    (c * s) ^ (i + 1) * S ^ 2 / Cn ≤ c' ^ 2 * (c * s * L / N) * (c * s * L / (N * Δ ^ 2)) ^ i := by
  have hC0 : 0 < (N / L) ^ (i + 1) := by positivity
  have hCn : 0 < Cn := lt_of_lt_of_le hC0 hC
  have hSq : (S * Δ ^ i) ^ 2 ≤ c' ^ 2 :=
    pow_le_pow_left₀ (by positivity) hS 2
  calc (c * s) ^ (i + 1) * S ^ 2 / Cn ≤ (c * s) ^ (i + 1) * S ^ 2 / (N / L) ^ (i + 1) :=
        div_le_div_of_nonneg_left (by positivity) hC0 hC
    _ = (S * Δ ^ i) ^ 2 * ((c * s * L / N) * (c * s * L / (N * Δ ^ 2)) ^ i) := by
        have hΔi : Δ ^ i ≠ 0 := by positivity
        have hNi : N ^ i ≠ 0 := by positivity
        have hLi : L ^ i ≠ 0 := by positivity
        rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, pow_succ, pow_succ, pow_succ]
        field_simp
        ring
    _ ≤ c' ^ 2 * ((c * s * L / N) * (c * s * L / (N * Δ ^ 2)) ^ i) := by gcongr
    _ = c' ^ 2 * (c * s * L / N) * (c * s * L / (N * Δ ^ 2)) ^ i := by ring

/-- The orders `j ≥ 2` add up to at most `1` times the first factor: `∑_{1 ≤ i < L} β^i ≤ 1`
for `0 ≤ β ≤ 1/2`. -/
theorem geom_tail_le (β : ℝ) (L : ℕ) (h0 : 0 ≤ β) (h1 : β ≤ 1 / 2) :
    ∑ i ∈ Ico 1 L, β ^ i ≤ 1 := by
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := L) h0 (by linarith)
  have : β ^ 1 / (1 - β) ≤ 1 := by
    rw [pow_one, div_le_one (by linarith)]; linarith
  linarith

end ShadowUStat
