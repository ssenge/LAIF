import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Frequency moments: the moment gap and the distinguishing step

* `sum_eval_eq_zero`: if the moments of `ν` of order below `k` vanish, so does `∑ ν(a) p(a)` for every
  polynomial `p` of natural degree below `k`.
* `moment_gap` (Lemma 1): if `ν` lives on `0, …, k` and its moments of order below `k` vanish, then
  `∑ ν(a) a^k = k! ν(k)`.
* `below_threshold`, `above_threshold`: an estimate within relative error `(φ₁ - φ₀)/(4 φ₁)` separates
  `F ≤ N (φ₀ + δ)` from `F ≥ N (φ₁ - δ)` at `N (φ₀ + φ₁)/2`, with `δ = (φ₁ - φ₀)/8`.
* `exponent_gt`: for `k ≥ 3`, `a_k = (2^{k-1} - 1)/(2^k - 1)` exceeds `1/3` and `1/2 - 1/(2k)`.
-/

open Polynomial Finset

namespace FreqMom

theorem sum_eval_eq_zero {k : ℕ} (ν : ℕ → ℚ) (s : Finset ℕ)
    (h : ∀ j < k, ∑ a ∈ s, ν a * (a : ℚ) ^ j = 0) (p : ℚ[X]) (hp : p.natDegree < k) :
    ∑ a ∈ s, ν a * p.eval (a : ℚ) = 0 := by
  simp_rw [eval_eq_sum_range' hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := h j (Finset.mem_range.mp hj)
  calc ∑ a ∈ s, ν a * (p.coeff j * (a : ℚ) ^ j) = p.coeff j * ∑ a ∈ s, ν a * (a : ℚ) ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    _ = 0 := by rw [hj', mul_zero]

/-- **Lemma 1.** A signed measure `ν` on `0, …, k` whose moments of order below `k` vanish has
`k`-th moment `k! ν(k)`. -/
theorem moment_gap (k : ℕ) (ν : ℕ → ℚ)
    (h : ∀ j < k, ∑ a ∈ range (k + 1), ν a * (a : ℚ) ^ j = 0) :
    ∑ a ∈ range (k + 1), ν a * (a : ℚ) ^ k = ν k * k.factorial := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  set D : ℚ[X] := descPochhammer ℚ k with hD
  set q : ℚ[X] := X ^ k - D with hq
  have hDm : D.Monic := monic_descPochhammer ℚ k
  have hDdeg : D.natDegree = k := descPochhammer_natDegree ℚ k
  have hqdeg : q.natDegree < k := by
    by_cases h0 : q = 0
    · rw [h0, natDegree_zero]; exact hk
    · have hd : (X ^ k : ℚ[X]).degree = D.degree := by
        rw [degree_X_pow, degree_eq_natDegree hDm.ne_zero, hDdeg]
      have hlt := degree_sub_lt hd (pow_ne_zero k X_ne_zero)
        (by rw [leadingCoeff_X_pow, hDm.leadingCoeff])
      rw [degree_X_pow] at hlt
      exact (natDegree_lt_iff_degree_lt h0).mpr hlt
  have hsplit : ∀ a : ℕ, (a : ℚ) ^ k = q.eval (a : ℚ) + (a.descFactorial k : ℚ) := by
    intro a
    rw [← descPochhammer_eval_eq_descFactorial ℚ a k, ← hD, hq, eval_sub, eval_pow, eval_X]
    ring
  have h1 : ∑ a ∈ range (k + 1), ν a * (a : ℚ) ^ k =
      ∑ a ∈ range (k + 1), ν a * q.eval (a : ℚ) +
        ∑ a ∈ range (k + 1), ν a * (a.descFactorial k : ℚ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by rw [hsplit a]; ring)
  rw [h1, sum_eval_eq_zero ν _ h q hqdeg, zero_add, Finset.sum_range_succ,
    Finset.sum_eq_zero (fun a ha => by
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp ha), Nat.cast_zero, mul_zero]),
    zero_add, Nat.descFactorial_self]

/-- An estimate `G ≤ (1 + c) F` of a value `F ≤ N (φ₀ + δ)` lies below `N (φ₀ + φ₁)/2`. -/
theorem below_threshold (N φ₀ φ₁ F G : ℝ) (hN : 0 < N) (h0 : 0 < φ₀) (h01 : φ₀ < φ₁)
    (hF0 : 0 ≤ F) (hF : F ≤ N * (φ₀ + (φ₁ - φ₀) / 8))
    (hG : G ≤ (1 + (φ₁ - φ₀) / (4 * φ₁)) * F) : G < N * (φ₀ + φ₁) / 2 := by
  have h1 : 0 < φ₁ := lt_trans h0 h01
  have hc : 0 ≤ (φ₁ - φ₀) / (4 * φ₁) := div_nonneg (by linarith) (by linarith)
  have hcφ : (φ₁ - φ₀) / (4 * φ₁) * φ₁ = (φ₁ - φ₀) / 4 := by field_simp
  have hF1 : F ≤ N * φ₁ := le_trans hF (by nlinarith)
  have h2 : (φ₁ - φ₀) / (4 * φ₁) * F ≤ N * ((φ₁ - φ₀) / 4) := by
    calc (φ₁ - φ₀) / (4 * φ₁) * F ≤ (φ₁ - φ₀) / (4 * φ₁) * (N * φ₁) :=
          mul_le_mul_of_nonneg_left hF1 hc
      _ = N * ((φ₁ - φ₀) / (4 * φ₁) * φ₁) := by ring
      _ = N * ((φ₁ - φ₀) / 4) := by rw [hcφ]
  nlinarith

/-- An estimate `G ≥ (1 - c) F` of a value `F ≥ N (φ₁ - δ)` lies above `N (φ₀ + φ₁)/2`. -/
theorem above_threshold (N φ₀ φ₁ F G : ℝ) (hN : 0 < N) (h0 : 0 < φ₀) (h01 : φ₀ < φ₁)
    (hF : N * (φ₁ - (φ₁ - φ₀) / 8) ≤ F)
    (hG : (1 - (φ₁ - φ₀) / (4 * φ₁)) * F ≤ G) : N * (φ₀ + φ₁) / 2 < G := by
  have h1 : 0 < φ₁ := lt_trans h0 h01
  have hc1 : (φ₁ - φ₀) / (4 * φ₁) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hc0 : 0 ≤ 1 - (φ₁ - φ₀) / (4 * φ₁) := by linarith
  have hcφ : (φ₁ - φ₀) / (4 * φ₁) * φ₁ = (φ₁ - φ₀) / 4 := by field_simp
  have hlow : (1 - (φ₁ - φ₀) / (4 * φ₁)) * (N * (φ₁ - (φ₁ - φ₀) / 8)) ≤ G :=
    le_trans (mul_le_mul_of_nonneg_left hF hc0) hG
  have hexp : (1 - (φ₁ - φ₀) / (4 * φ₁)) * (N * (φ₁ - (φ₁ - φ₀) / 8)) =
      N * (φ₁ - (φ₁ - φ₀) / 8) - N * ((φ₁ - φ₀) / (4 * φ₁) * φ₁) +
        N * ((φ₁ - φ₀) / (4 * φ₁)) * ((φ₁ - φ₀) / 8) := by ring
  have hpos : 0 ≤ N * ((φ₁ - φ₀) / (4 * φ₁)) * ((φ₁ - φ₀) / 8) := by
    have : 0 ≤ (φ₁ - φ₀) / (4 * φ₁) := div_nonneg (by linarith) (by linarith)
    have : 0 ≤ (φ₁ - φ₀) / 8 := by linarith
    positivity
  rw [hexp, hcφ] at hlow
  nlinarith

/-- For `k ≥ 3` the exponent `a_k = (2^{k-1} - 1)/(2^k - 1)` exceeds `1/3` and `1/2 - 1/(2k)`. -/
theorem exponent_gt (k : ℕ) (hk : 3 ≤ k) :
    (1 : ℚ) / 3 < (2 ^ (k - 1) - 1) / (2 ^ k - 1) ∧
      (1 : ℚ) / 2 - 1 / (2 * k) < (2 ^ (k - 1) - 1) / (2 ^ k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hm : 2 ≤ m := by omega
  have h4 : (4 : ℚ) ≤ 2 ^ m := by
    calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hlt : ((m + 1 : ℕ) : ℚ) + 1 < 2 ^ (m + 1) := by
    have : ∀ n : ℕ, 2 ≤ n → (n : ℚ) + 2 < 2 ^ (n + 1) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih => push_cast at ih ⊢; rw [pow_succ]; linarith
    have := this m hm; push_cast at this ⊢; linarith
  have hpow : (2 : ℚ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hden : (0 : ℚ) < 2 ^ (m + 1) - 1 := by rw [hpow]; linarith
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hden, hpow]; linarith
  · have hk0 : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    rw [show (1 : ℚ) / 2 - 1 / (2 * ((m + 1 : ℕ) : ℚ)) = (((m + 1 : ℕ) : ℚ) - 1) / (2 * ((m + 1 : ℕ) : ℚ)) by
      field_simp]
    rw [div_lt_div_iff₀ (by positivity) hden]
    rw [hpow] at hlt ⊢
    nlinarith

end FreqMom
