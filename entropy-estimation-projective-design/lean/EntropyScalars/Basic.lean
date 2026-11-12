import Mathlib

/-!
# Scalar steps of the entropy estimator near the maximally mixed state

* `remainder_le`: the tail of the series `∑ a ^ k / (k (k - 1))` beyond degree `K`, for
  `0 ≤ a ≤ 1/4`, is at most `(4/3) a ^ (K + 1) / (K (K + 1))`.
* `block_le`: with `n ≥ 30 k` outcomes split into `k` blocks of `⌊n/k⌋`, and `d ≥ 2`,
  `(5/4)(1 + 1/d) / ⌊n/k⌋ ≤ 2k/n`.
* `coef_le`: the variance coefficient of degree `k = m + 2`,
  `(d ^ (k-1) / (k (k-1)))² ∑_{c=1}^{k} C(k,c) (2k/n) ^ c d ^ c r ^ (2(k-c))`, is at most
  `16 (2/15) ^ m / (m + 1)² (d³r²/n + d⁴/n²)` when `2k d³/n ≤ 1/15` and `d r ≤ 1/4`.
* `series_le`: `∑_{j<N} 4 x ^ j / (j + 1) ≤ 5` for `0 ≤ x`, `x² ≤ 2/15`.
* `sq_le`, `tail_le`, `risk_le`: squaring, the remainder at degree `K ≥ log₁₆(n/d)`, and the
  final constant `51`.
-/

namespace EntropyScalars

open Finset

/-- Tail of the entropy series beyond degree `K`. -/
theorem remainder_le (a : ℝ) (K N : ℕ) (ha : 0 ≤ a) (ha4 : a ≤ 1 / 4) (hK : 1 ≤ K) :
    ∑ k ∈ Ico (K + 1) N, a ^ k / ((k : ℝ) * ((k : ℝ) - 1))
      ≤ 4 / 3 * a ^ (K + 1) / ((K : ℝ) * ((K : ℝ) + 1)) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) * ((K : ℝ) + 1) := by positivity
  calc ∑ k ∈ Ico (K + 1) N, a ^ k / ((k : ℝ) * ((k : ℝ) - 1))
      ≤ ∑ k ∈ Ico (K + 1) N, a ^ k / ((K : ℝ) * ((K : ℝ) + 1)) := by
        apply sum_le_sum
        intro k hk
        have hkr : (K : ℝ) + 1 ≤ k := by exact_mod_cast (mem_Ico.mp hk).1
        apply div_le_div_of_nonneg_left (pow_nonneg ha _) hKpos
        nlinarith
    _ = (∑ k ∈ Ico (K + 1) N, a ^ k) / ((K : ℝ) * ((K : ℝ) + 1)) := by rw [sum_div]
    _ ≤ (a ^ (K + 1) / (1 - a)) / ((K : ℝ) * ((K : ℝ) + 1)) := by
        apply div_le_div_of_nonneg_right _ hKpos.le
        exact geom_sum_Ico_le_of_lt_one ha (by linarith)
    _ ≤ 4 / 3 * a ^ (K + 1) / ((K : ℝ) * ((K : ℝ) + 1)) := by
        apply div_le_div_of_nonneg_right _ hKpos.le
        rw [div_le_iff₀ (by linarith)]
        have := pow_nonneg ha (K + 1)
        nlinarith [mul_nonneg this (sub_nonneg.mpr ha4)]

/-- Block sizes: `(5/4)(1 + 1/d) / ⌊n/k⌋ ≤ 2k/n` for `n ≥ 30 k` and `d ≥ 2`. -/
theorem block_le (n k : ℕ) (d : ℝ) (hd : 2 ≤ d) (hk : 1 ≤ k) (hn : 30 * k ≤ n) :
    5 / 4 * (1 + 1 / d) / ((n / k : ℕ) : ℝ) ≤ 2 * k / n := by
  have hdm := Nat.div_add_mod' n k
  have hmod := Nat.mod_lt n (by omega : k > 0)
  have hqk : n ≤ (n / k) * k + k := by omega
  have hqr : (n : ℝ) ≤ ((n / k : ℕ) : ℝ) * k + k := by exact_mod_cast hqk
  have hnr : (30 : ℝ) * k ≤ n := by exact_mod_cast hn
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 < ((n / k : ℕ) : ℝ) := by
    have : 1 ≤ n / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by linarith
  have hd' : 1 / d ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  rw [div_le_div_iff₀ hq hn0]
  nlinarith

/-- The term `c = j + 2 ≥ 2` of the variance coefficient, rewritten. -/
theorem term_eq (C k m1 d n r : ℝ) (j l : ℕ) (hk : k ≠ 0) (hm : m1 ≠ 0) (hn : n ≠ 0) :
    (d ^ (j + l + 1) / (k * m1)) ^ 2 * (C * (2 * k / n) ^ (j + 2) * d ^ (j + 2) * r ^ (2 * l))
      = 4 * C / m1 ^ 2 * (2 * k * d ^ 3 / n) ^ j * ((d * r) ^ 2) ^ l * (d ^ 4 / n ^ 2) := by
  rw [div_pow, div_pow, div_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  field_simp
  ring

/-- Variance coefficient of degree `k = m + 2`. -/
theorem coef_le (m : ℕ) (d n r : ℝ) (hd : 0 < d) (hn : 0 < n) (hr : 0 ≤ r)
    (h1 : 2 * ((m : ℝ) + 2) * d ^ 3 / n ≤ 1 / 15) (h2 : d * r ≤ 1 / 4) :
    (d ^ (m + 1) / (((m : ℝ) + 2) * ((m : ℝ) + 1))) ^ 2 *
      ∑ c ∈ Icc 1 (m + 2), (((m + 2).choose c : ℕ) : ℝ) * (2 * ((m : ℝ) + 2) / n) ^ c * d ^ c
        * r ^ (2 * (m + 2 - c))
    ≤ 16 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * (d ^ 3 * r ^ 2 / n + d ^ 4 / n ^ 2) := by
  set k : ℝ := (m : ℝ) + 2 with hkdef
  set A := d ^ 3 * r ^ 2 / n with hAdef
  set B := d ^ 4 / n ^ 2
  have hk0 : k ≠ 0 := by positivity
  have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hw : 0 ≤ d * r := by positivity
  have hu0 : 0 ≤ 2 * k * d ^ 3 / n := by positivity
  have hw2 : (d * r) ^ 2 ≤ 1 / 16 := by nlinarith
  have hm2 : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
  rw [Icc_eq_cons_Ioc (by omega : 1 ≤ m + 2), sum_cons, mul_add]
  -- the term `c = 1`
  have t1 : (d ^ (m + 1) / (k * ((m : ℝ) + 1))) ^ 2 * ((((m + 2).choose 1 : ℕ) : ℝ)
      * (2 * k / n) ^ 1 * d ^ 1 * r ^ (2 * (m + 2 - 1)))
      ≤ 2 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * A := by
    have e : (d ^ (m + 1) / (k * ((m : ℝ) + 1))) ^ 2 * ((((m + 2).choose 1 : ℕ) : ℝ)
        * (2 * k / n) ^ 1 * d ^ 1 * r ^ (2 * (m + 2 - 1)))
        = 2 / ((m : ℝ) + 1) ^ 2 * ((d * r) ^ 2) ^ m * A := by
      rw [Nat.choose_one_right, show 2 * (m + 2 - 1) = 2 * m + 2 by omega]
      push_cast
      rw [← hkdef]
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add, pow_mul, hAdef]
      field_simp
      ring
    rw [e]
    have : ((d * r) ^ 2) ^ m ≤ (2 / 15) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    have h2m : 0 ≤ 2 / ((m : ℝ) + 1) ^ 2 := by positivity
    calc 2 / ((m : ℝ) + 1) ^ 2 * ((d * r) ^ 2) ^ m * A
        ≤ 2 / ((m : ℝ) + 1) ^ 2 * (2 / 15) ^ m * A := by gcongr
      _ = 2 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * A := by ring
  -- the terms `c ≥ 2`
  have t2 : ∑ c ∈ Ioc 1 (m + 2), (d ^ (m + 1) / (k * ((m : ℝ) + 1))) ^ 2 *
      ((((m + 2).choose c : ℕ) : ℝ) * (2 * k / n) ^ c * d ^ c * r ^ (2 * (m + 2 - c)))
      ≤ ∑ c ∈ Ioc 1 (m + 2), (((m + 2).choose c : ℕ) : ℝ) * (4 / ((m : ℝ) + 1) ^ 2
        * (1 / 15) ^ m * B) := by
    apply sum_le_sum
    intro c hc
    obtain ⟨hc1, hc2⟩ := mem_Ioc.mp hc
    obtain ⟨j, rfl⟩ : ∃ j, c = j + 2 := ⟨c - 2, by omega⟩
    obtain ⟨l, hl⟩ : ∃ l, m = j + l := ⟨m - j, by omega⟩
    have hsub : 2 * (m + 2 - (j + 2)) = 2 * l := by omega
    rw [hsub, show m + 1 = j + l + 1 by omega,
      term_eq _ k ((m : ℝ) + 1) d n r j l hk0 hm0 hn.ne']
    have hC : (0 : ℝ) ≤ (((m + 2).choose (j + 2) : ℕ) : ℝ) := by positivity
    have hu : (2 * k * d ^ 3 / n) ^ j ≤ (1 / 15) ^ j := pow_le_pow_left₀ hu0 h1 j
    have hv : ((d * r) ^ 2) ^ l ≤ (1 / 15) ^ l :=
      pow_le_pow_left₀ (by positivity) (by linarith) l
    have h15 : (1 / 15 : ℝ) ^ m = (1 / 15) ^ j * (1 / 15) ^ l := by rw [hl, pow_add]
    rw [h15]
    have e4 : 0 ≤ 4 * (((m + 2).choose (j + 2) : ℕ) : ℝ) / ((m : ℝ) + 1) ^ 2 := by positivity
    calc 4 * (((m + 2).choose (j + 2) : ℕ) : ℝ) / ((m : ℝ) + 1) ^ 2 * (2 * k * d ^ 3 / n) ^ j
          * ((d * r) ^ 2) ^ l * B
        ≤ 4 * (((m + 2).choose (j + 2) : ℕ) : ℝ) / ((m : ℝ) + 1) ^ 2 * (1 / 15) ^ j
          * (1 / 15) ^ l * B := by gcongr
      _ = (((m + 2).choose (j + 2) : ℕ) : ℝ) * (4 / ((m : ℝ) + 1) ^ 2
          * ((1 / 15) ^ j * (1 / 15) ^ l) * B) := by ring
  have hsumC : ∑ c ∈ Ioc 1 (m + 2), (((m + 2).choose c : ℕ) : ℝ) ≤ 2 ^ (m + 2) := by
    have h := Nat.sum_range_choose (m + 2)
    have hs : Ioc 1 (m + 2) ⊆ range (m + 2 + 1) := by
      intro c hc; simp only [mem_Ioc] at hc; simp only [mem_range]; omega
    have : ∑ c ∈ Ioc 1 (m + 2), (m + 2).choose c ≤ 2 ^ (m + 2) := by
      rw [← h]; exact sum_le_sum_of_subset hs
    exact_mod_cast this
  rw [← sum_mul] at t2
  have hfac : 0 ≤ 4 / ((m : ℝ) + 1) ^ 2 * (1 / 15) ^ m * B := by positivity
  have t3 : (∑ c ∈ Ioc 1 (m + 2), (((m + 2).choose c : ℕ) : ℝ)) * (4 / ((m : ℝ) + 1) ^ 2
      * (1 / 15) ^ m * B) ≤ 16 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * B := by
    calc (∑ c ∈ Ioc 1 (m + 2), (((m + 2).choose c : ℕ) : ℝ)) * (4 / ((m : ℝ) + 1) ^ 2
          * (1 / 15) ^ m * B)
        ≤ 2 ^ (m + 2) * (4 / ((m : ℝ) + 1) ^ 2 * (1 / 15) ^ m * B) :=
          mul_le_mul_of_nonneg_right hsumC hfac
      _ = 16 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * B := by
          rw [pow_add, div_pow, div_pow, one_pow]; field_simp; ring
  have hpos : 0 ≤ (2 / 15 : ℝ) ^ m / ((m : ℝ) + 1) ^ 2 * A := by positivity
  rw [mul_sum]
  calc _ ≤ 2 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * A
        + 16 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * B := add_le_add t1 (le_trans t2 t3)
    _ ≤ 16 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * (A + B) := by
        have : 2 * (2 / 15 : ℝ) ^ m / ((m : ℝ) + 1) ^ 2 * A
            ≤ 16 * (2 / 15) ^ m / ((m : ℝ) + 1) ^ 2 * A := by
          rw [mul_div_assoc, mul_div_assoc, mul_assoc, mul_assoc]
          nlinarith
        nlinarith

/-- The sum of the standard deviation bounds: `∑_{j<N} 4 x ^ j / (j + 1) ≤ 5` for
`0 ≤ x`, `x² ≤ 2/15`. -/
theorem series_le (x : ℝ) (hx : 0 ≤ x) (hx2 : x ^ 2 ≤ 2 / 15) (N : ℕ) :
    ∑ j ∈ range N, 4 * x ^ j / ((j : ℝ) + 1) ≤ 5 := by
  have hx1 : x ≤ 3652 / 10000 := by nlinarith
  have hlt : x < 1 := by linarith
  have hnn : ∀ j : ℕ, 0 ≤ 4 * x ^ j / ((j : ℝ) + 1) := fun j => by positivity
  have h3 : ∑ j ∈ range 3, 4 * x ^ j / ((j : ℝ) + 1) = 4 + 2 * x + 4 / 3 * x ^ 2 := by
    simp only [sum_range_succ, sum_range_zero]; push_cast; ring
  have htail : ∑ j ∈ Ico 3 (N + 3), 4 * x ^ j / ((j : ℝ) + 1) ≤ ∑ j ∈ Ico 3 (N + 3), x ^ j := by
    apply sum_le_sum
    intro j hj
    have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
    rw [div_le_iff₀ (by positivity)]
    have := pow_nonneg hx j
    nlinarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 3) (n := N + 3) hx hlt
  have hfin : x ^ 3 / (1 - x) ≤ 1 - 2 * x - 4 / 3 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (3652 / 10000 - x), mul_nonneg (sq_nonneg (3652 / 10000 - x)) hx,
      sub_nonneg.mpr hx1]
  calc ∑ j ∈ range N, 4 * x ^ j / ((j : ℝ) + 1)
      ≤ ∑ j ∈ range (N + 3), 4 * x ^ j / ((j : ℝ) + 1) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) (fun j _ _ => hnn j)
    _ = ∑ j ∈ range 3, 4 * x ^ j / ((j : ℝ) + 1)
        + ∑ j ∈ Ico 3 (N + 3), 4 * x ^ j / ((j : ℝ) + 1) :=
        (sum_range_add_sum_Ico _ (by omega)).symm
    _ ≤ 5 := by rw [h3]; linarith

/-- Squaring the bound on the error in mean square. -/
theorem sq_le (s R : ℝ) : (5 * s + R) ^ 2 ≤ 50 * s ^ 2 + 2 * R ^ 2 := by
  nlinarith [sq_nonneg (5 * s - R)]

/-- The remainder at degree `K` with `16 ^ K ≥ n/d` is below `d³r²/n`. -/
theorem tail_le (d n r : ℝ) (K : ℕ) (hd : 0 < d) (hn : 0 < n) (hr : 0 ≤ r) (h2 : d * r ≤ 1 / 4)
    (hK : n / d ≤ 16 ^ K) : (d * r) ^ (2 * (K + 1)) ≤ d ^ 3 * r ^ 2 / n := by
  have hw : 0 ≤ d * r := by positivity
  have hw2 : (d * r) ^ 2 ≤ 1 / 16 := by nlinarith
  have h16 : ((d * r) ^ 2) ^ K ≤ (1 / 16) ^ K := pow_le_pow_left₀ (by positivity) hw2 K
  have hinv : (1 / 16 : ℝ) ^ K ≤ d / n := by
    rw [one_div_pow, div_le_div_iff₀ (by positivity) hn]
    rw [div_le_iff₀ hd] at hK
    linarith
  calc (d * r) ^ (2 * (K + 1)) = (d * r) ^ 2 * ((d * r) ^ 2) ^ K := by ring
    _ ≤ (d * r) ^ 2 * (d / n) := by gcongr; exact le_trans h16 hinv
    _ = d ^ 3 * r ^ 2 / n := by ring

/-- The final constant: `50 Q + (32/9) X / (K (K + 1))² ≤ 51 Q` for `0 ≤ X ≤ Q` and `K ≥ 2`. -/
theorem risk_le (Q X : ℝ) (K : ℕ) (hK : 2 ≤ K) (hX0 : 0 ≤ X) (hX : X ≤ Q) :
    50 * Q + 32 / 9 * X / ((K : ℝ) * ((K : ℝ) + 1)) ^ 2 ≤ 51 * Q := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h6 : (6 : ℝ) ≤ (K : ℝ) * ((K : ℝ) + 1) := by nlinarith
  have h36 : (36 : ℝ) ≤ ((K : ℝ) * ((K : ℝ) + 1)) ^ 2 := by nlinarith
  have h : 32 / 9 * X / ((K : ℝ) * ((K : ℝ) + 1)) ^ 2 ≤ 32 / 9 * X / 36 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) h36
  linarith

end EntropyScalars
