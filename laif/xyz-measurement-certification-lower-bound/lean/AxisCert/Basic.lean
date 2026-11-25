import Mathlib

/-!
# Scalar facts behind the lower bound for certification with X, Y, Z measurements

The single-qubit state with expectation values 1/√3 along X, Y and Z has outcome probabilities
(1 ± 1/√3)/2 along every one of these axes, and its orthogonal state the reversed ones.

* `per_axis`: the sum over the two outcomes of the geometric means of the two outcome laws is √(2/3).
* `hm_le_gm`, `chi_term`: the leaf term c²/m of the chi-square divergence, with c² ≤ xy and
  m = (x + y)/2, is at most √(xy).
* `mixture_identity`: averaging (1 + q)^{|A|} over a set A that contains each of T copies
  independently with probability p gives (1 + pq)^T.
* `copies_of_bound`, `theorem2_constant`, `chi_binary`: the copy counts of Theorems 1 and 2
  follow from the distance and chi-square bounds.

Non-vacuity: `hm_le_gm_eq`, `chi_term_eq` and `chi_binary_eq` attain equality with nonzero sides,
`distance_hyp_sat` shows that the hypothesis of `copies_of_bound` can hold and fail, and
`bound_exceeds_one` shows that the bound of Theorem 1(a) exceeds 1 at n = 8.
-/

namespace AxisCert

/-- The per-axis factor: Σ_e |⟨e|a⟩||⟨e|ā⟩| = √(2/3). -/
theorem per_axis :
    Real.sqrt (((1 + 1 / Real.sqrt 3) / 2) * ((1 - 1 / Real.sqrt 3) / 2)) +
      Real.sqrt (((1 - 1 / Real.sqrt 3) / 2) * ((1 + 1 / Real.sqrt 3) / 2)) =
      Real.sqrt (2 / 3) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hinv : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, h3]; norm_num
  have hprod : ((1 + 1 / Real.sqrt 3) / 2) * ((1 - 1 / Real.sqrt 3) / 2) = 1 / 6 := by
    calc ((1 + 1 / Real.sqrt 3) / 2) * ((1 - 1 / Real.sqrt 3) / 2)
        = (1 - (1 / Real.sqrt 3) ^ 2) / 4 := by ring
      _ = 1 / 6 := by rw [hinv]; norm_num
  rw [mul_comm ((1 - 1 / Real.sqrt 3) / 2), hprod]
  rw [show (2 / 3 : ℝ) = 2 ^ 2 * (1 / 6) by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

/-- The harmonic mean is at most the geometric mean: 2xy/(x + y) ≤ √(xy). -/
theorem hm_le_gm (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * x * y / (x + y) ≤ Real.sqrt (x * y) := by
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h | h
  · rw [← h, div_zero]; exact Real.sqrt_nonneg _
  · rw [div_le_iff₀ h]
    have hg0 : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
    have hg : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx hy)
    have h1 : Real.sqrt (x * y) ≤ (x + y) / 2 := by
      calc Real.sqrt (x * y) ≤ Real.sqrt (((x + y) / 2) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x - y)])
        _ = (x + y) / 2 := Real.sqrt_sq (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hg0]

/-- The chi-square term of one leaf: c²/m ≤ √(xy) when c² ≤ xy and m = (x + y)/2 > 0. -/
theorem chi_term (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : c ^ 2 ≤ x * y)
    (hm : 0 < x + y) : c ^ 2 / ((x + y) / 2) ≤ Real.sqrt (x * y) := by
  have h1 : c ^ 2 / ((x + y) / 2) = 2 * c ^ 2 / (x + y) := by
    field_simp
  rw [h1]
  calc 2 * c ^ 2 / (x + y) ≤ 2 * x * y / (x + y) := by
        apply div_le_div_of_nonneg_right _ hm.le
        nlinarith
    _ ≤ Real.sqrt (x * y) := hm_le_gm x y hx hy

/-- Averaging (1 + q)^{|A|} over a random set of copies: Σ_j C(T, j) p^j (1 - p)^{T-j} (1 + q)^j
= (1 + pq)^T. -/
theorem mixture_identity (p q : ℝ) (T : ℕ) :
    ∑ j ∈ Finset.range (T + 1), (p * (1 + q)) ^ j * (1 - p) ^ (T - j) * (T.choose j : ℝ) =
      (1 + p * q) ^ T := by
  rw [show 1 + p * q = p * (1 + q) + (1 - p) by ring, add_pow]

/-- A bound (1 + κ)^T ≥ c with c > 0 forces T ≥ ln c/κ. With c = 5/3 and κ = q or 2εq this gives
Theorem 1; with c = 3/2 and κ = s²q it gives Theorem 2. -/
theorem copies_of_bound (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) (T : ℕ) (h : c ≤ (1 + κ) ^ T) :
    Real.log c / κ ≤ T := by
  have hlog : Real.log c ≤ T * Real.log (1 + κ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hc h
  have hl1 : Real.log (1 + κ) ≤ κ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + κ by linarith)
    linarith
  rw [div_le_iff₀ hκ]
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  nlinarith [mul_le_mul_of_nonneg_left hl1 hT]

/-- Theorem 2: with s = 4ε the bound ln(3/2)/(s²q) equals ln(3/2)/(16ε²q). -/
theorem theorem2_constant (ε q : ℝ) :
    Real.log (3 / 2) / ((4 * ε) ^ 2 * q) = Real.log (3 / 2) / (16 * ε ^ 2 * q) := by
  ring

/-- The binary coarse-graining: an event of probability at least 2/3 under one law and at most
1/3 under the other gives chi-square at least 1/2. -/
theorem chi_binary (p r : ℝ) (hp : 2 / 3 ≤ p) (hr0 : 0 < r) (hr : r ≤ 1 / 3) :
    1 / 2 ≤ (p - r) ^ 2 / (r * (1 - r)) := by
  have hd : 0 < r * (1 - r) := by nlinarith
  rw [le_div_iff₀ hd]
  have h1 : 1 / 3 ≤ p - r := by linarith
  have h2 : (1 / 3) * (1 / 3) ≤ (p - r) * (p - r) := mul_le_mul h1 h1 (by norm_num) (by linarith)
  have h3 : 0 ≤ (1 / 3 - r) * (2 / 3 - r) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h2, h3]

/-! ## Non-vacuity -/

theorem hm_le_gm_eq : 2 * (1 : ℝ) * 1 / (1 + 1) = Real.sqrt (1 * 1) := by
  rw [show (1 : ℝ) * 1 = 1 by norm_num, Real.sqrt_one]; norm_num

theorem chi_binary_eq : (1 : ℝ) / 2 = (2 / 3 - 1 / 3) ^ 2 / (1 / 3 * (1 - 1 / 3)) := by norm_num

theorem chi_term_eq : (1 : ℝ) ^ 2 / ((1 + 1) / 2) = Real.sqrt (1 * 1) := by
  rw [show (1 : ℝ) * 1 = 1 by norm_num, Real.sqrt_one]; norm_num

/-- The hypothesis of `copies_of_bound` (c = 5/3, κ = 1/2) holds for some T and fails for others. -/
theorem distance_hyp_sat : (5 / 3 : ℝ) ≤ (1 + 1 / 2) ^ 2 ∧ ¬ ((5 / 3 : ℝ) ≤ (1 + 1 / 2) ^ 1) := by
  constructor <;> norm_num

/-- At n = 8, q = (2/3)^4 and the bound ln(5/3)/q of Theorem 1(a) exceeds 1. -/
theorem bound_exceeds_one : 1 < Real.log (5 / 3) / ((2 / 3 : ℝ) ^ 4) := by
  have he : Real.exp (1 / 2) < 5 / 3 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hl : 1 / 2 < Real.log (5 / 3) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact he
  rw [lt_div_iff₀ (by norm_num)]
  norm_num
  linarith

end AxisCert
