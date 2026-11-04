import Covers.Model
import Covers.Gap
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The query counts of Sections 2 to 5

The charges follow the README, with `Λ = log n` and the failure parameter `δ = n⁻⁶` of Lemma 6. `r` is the constant in "a
sample has at most `r Λ` columns" (with a redraw above that, in the README).

* `searchQ`, `minQ`: a search or minimum finding whose predicate costs `I`, charged `2 I` per call.
* `occQ` is Lemma 4, `sampleQ` is a sample, `testQ` is Lemma 6, `rangeQ` is Lemma 7. Domains are charged at their upper
  bounds, such as `ℓ` for `w ≤ ℓ/8`, since `qS`, `qM` are only bounded above.
* `total_le`: the summation, for `τ` tests per range. `theorem1_cost` has `τ = 1` and `theorem2_cost` has `τ = b Λ`.

What is hypothesized is `GroverCost` and `MinCost`, and the charge itself. What is derived is every bound below.

## The count of a sample

The README says "`log w` phases of `O(log n)` columns, each column `O(√ℓ log n)` queries". One column has a search over the
overlap at `O(√ℓ log n)`, but also two minimum findings at `O(√w log² n)`, since a survivor check reads `O(log n)` columns.
The total `O(√ℓ log³ n)` still holds, because `w` halves between phases, so the minimum findings sum geometrically.
`sampleQ_le` proves that.
-/

open Finset

namespace Strings

variable (M : Primitives)

/-- `log n`. -/
noncomputable def Lam (n : ℕ) : ℝ := Real.log n

/-- The failure parameter `n⁻⁶`. -/
noncomputable def delta (n : ℕ) : ℝ := ((n : ℝ) ^ 6)⁻¹

/-- A search over `N` items with a predicate of cost `I`: compute and uncompute at each call. -/
noncomputable def searchQ (n N : ℕ) (I : ℝ) : ℝ := 2 * M.qS N (delta n) * I

/-- A minimum finding over `N` items with a predicate of cost `I`. -/
noncomputable def minQ (n N : ℕ) (I : ℝ) : ℝ := 2 * M.qM N (delta n) * I

/-- **Lemma 4**: at most 6 blocks with two extremes each, each extreme a minimum finding over at most `ℓ` starts with a
check of `r Λ` columns, and a verification, and two capped first-mismatch searches. -/
noncomputable def occQ (n : ℕ) (r : ℝ) (ℓ : ℕ) : ℝ :=
  12 * minQ M n ℓ (r * Lam n) + 12 * searchQ M n ℓ 1 + 2 * minQ M n (2 * ℓ) 1

/-- **A sample**: phases `j ≤ log₂ ℓ` on `w ≤ ℓ / 2^j` alignments, each of `r Λ` columns. A column has two minimum findings
with a check of `r Λ` columns, and a search over the overlap. -/
noncomputable def sampleQ (n : ℕ) (r : ℝ) (ℓ : ℕ) : ℝ :=
  ∑ j ∈ range (Nat.log 2 ℓ + 1),
    r * Lam n * (2 * minQ M n (ℓ / 2 ^ j) (r * Lam n) + searchQ M n ℓ 1)

/-- **Lemma 6**: a search over the blocks, with a predicate of three calls of Lemma 4. -/
noncomputable def testQ (n : ℕ) (r : ℝ) (ℓ : ℕ) : ℝ :=
  searchQ M n (numBlocks n ℓ) (3 * occQ M n r ℓ)

/-- **Lemma 7**: two calls of Lemma 4 at `L = 2^k`, up to 24 verifications, and two capped first-mismatch searches. -/
noncomputable def rangeQ (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  2 * occQ M n r (2 ^ k) + 24 * searchQ M n (2 * 2 ^ k) 1 + 2 * minQ M n (2 * 2 ^ k) 1

/-- **The outer loop**: for each `k ≤ log₂ n` find the borders, and for each tested length in `T k`, a sample and a
test. -/
noncomputable def totalQ (n : ℕ) (r : ℝ) (T : ℕ → Finset ℕ) : ℝ :=
  ∑ k ∈ range (Nat.log 2 n + 1),
    (rangeQ M n r k + sampleQ M n r (2 ^ k) + ∑ ℓ ∈ T k, (sampleQ M n r ℓ + testQ M n r ℓ))

/-! ## Arithmetic -/

theorem lam_ge_one {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Lam n := by
  unfold Lam
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h2 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem log_one_div_delta {n : ℕ} : Real.log (1 / delta n) = 6 * Lam n := by
  unfold delta Lam
  rw [one_div, inv_inv, Real.log_pow]
  norm_num

theorem delta_pos {n : ℕ} (hn : 3 ≤ n) : 0 < delta n := by
  unfold delta
  have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  positivity

theorem delta_le {n : ℕ} (hn : 3 ≤ n) : delta n ≤ 1 / 2 := by
  unfold delta
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h : (2 : ℝ) ≤ (n : ℝ) ^ 6 := by
    calc (2 : ℝ) ≤ 3 ^ 6 := by norm_num
      _ ≤ (n : ℝ) ^ 6 := by gcongr
  rw [one_div]
  exact inv_anti₀ (by norm_num) h

theorem log2_add_one_le {n : ℕ} (hn : 3 ≤ n) : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Lam n := by
  have h1 := lam_ge_one hn
  have hpow : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Lam n := by
    unfold Lam
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (Nat.log 2 n : ℝ) ≤ 2 * Lam n := by
    have hk : (0 : ℝ) ≤ Nat.log 2 n := by positivity
    nlinarith
  push_cast
  linarith

/-- The geometric sum over ranges: `∑_{k ≤ K} √(2^k) ≤ 4 √(2^K)`. -/
theorem sum_sqrt_pow_le (K : ℕ) :
    ∑ k ∈ range (K + 1), Real.sqrt ((2 : ℝ) ^ k) ≤ 4 * Real.sqrt ((2 : ℝ) ^ K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have e : Real.sqrt ((2 : ℝ) ^ (K + 1)) = Real.sqrt ((2 : ℝ) ^ K) * Real.sqrt 2 := by
      rw [pow_succ, Real.sqrt_mul (by positivity)]
    have h2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have hs : 0 ≤ Real.sqrt ((2 : ℝ) ^ K) := Real.sqrt_nonneg _
    rw [e]
    nlinarith

/-- The geometric sum over phases: `∑_j (3/4)^j ≤ 4`. -/
theorem sum_three_quarters_le (m : ℕ) : ∑ j ∈ range m, ((3 : ℝ) / 4) ^ j ≤ 4 := by
  have h : ∑ j ∈ range m, ((3 : ℝ) / 4) ^ j + 4 * ((3 : ℝ) / 4) ^ m = 4 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [sum_range_succ, pow_succ]
      linarith
  have : (0 : ℝ) ≤ ((3 : ℝ) / 4) ^ m := by positivity
  linarith

/-- `√⌊ℓ / 2^j⌋ ≤ (3/4)^j √ℓ`. -/
theorem sqrt_div_pow_le (ℓ j : ℕ) : Real.sqrt ((ℓ / 2 ^ j : ℕ) : ℝ) ≤ ((3 : ℝ) / 4) ^ j * Real.sqrt ℓ := by
  have hle : ((ℓ / 2 ^ j : ℕ) : ℝ) ≤ ((((3 : ℝ) / 4) ^ j) ^ 2) * ℓ := by
    have h1 : ((ℓ / 2 ^ j : ℕ) : ℝ) ≤ (ℓ : ℝ) / 2 ^ j := by
      have := @Nat.cast_div_le ℝ _ _ _ ℓ (2 ^ j)
      simpa using this
    have h2 : (ℓ : ℝ) / 2 ^ j = ((1 : ℝ) / 2) ^ j * ℓ := by
      rw [one_div, inv_pow]; field_simp
    have h3 : ((1 : ℝ) / 2) ^ j ≤ (((3 : ℝ) / 4) ^ j) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  calc Real.sqrt ((ℓ / 2 ^ j : ℕ) : ℝ) ≤ Real.sqrt ((((3 : ℝ) / 4) ^ j) ^ 2 * ℓ) := Real.sqrt_le_sqrt hle
    _ = ((3 : ℝ) / 4) ^ j * Real.sqrt ℓ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-! ## The charges

Below, `cS, cM` are the constants of `GroverCost`, `MinCost`. The bounds have explicit constants, so that the final
constant visibly depends only on `cS`, `cM`, `r`, `b`. -/

variable {M} {cS cM : ℝ}

theorem searchQ_le (hG : GroverCost M cS) {n N : ℕ} {I : ℝ} (hn : 3 ≤ n) (hN : 1 ≤ N) (hI : 0 ≤ I) :
    searchQ M n N I ≤ 12 * cS * Real.sqrt N * Lam n * I := by
  have h := (hG N (delta n) hN (delta_pos hn) (delta_le hn)).2
  rw [log_one_div_delta] at h
  unfold searchQ
  calc 2 * M.qS N (delta n) * I ≤ 2 * (cS * Real.sqrt N * (6 * Lam n)) * I := by gcongr
    _ = 12 * cS * Real.sqrt N * Lam n * I := by ring

theorem minQ_le (hM : MinCost M cM) {n N : ℕ} {I : ℝ} (hn : 3 ≤ n) (hN : 1 ≤ N) (hI : 0 ≤ I) :
    minQ M n N I ≤ 12 * cM * Real.sqrt N * Lam n * I := by
  have h := (hM N (delta n) hN (delta_pos hn) (delta_le hn)).2
  rw [log_one_div_delta] at h
  unfold minQ
  calc 2 * M.qM N (delta n) * I ≤ 2 * (cM * Real.sqrt N * (6 * Lam n)) * I := by gcongr
    _ = 12 * cM * Real.sqrt N * Lam n * I := by ring

theorem searchQ_nonneg (hG : GroverCost M cS) {n N : ℕ} {I : ℝ} (hn : 3 ≤ n) (hN : 1 ≤ N) (hI : 0 ≤ I) :
    0 ≤ searchQ M n N I :=
  mul_nonneg (mul_nonneg (by norm_num) (hG N (delta n) hN (delta_pos hn) (delta_le hn)).1) hI

theorem minQ_nonneg (hM : MinCost M cM) {n N : ℕ} {I : ℝ} (hn : 3 ≤ n) (hN : 1 ≤ N) (hI : 0 ≤ I) :
    0 ≤ minQ M n N I :=
  mul_nonneg (mul_nonneg (by norm_num) (hM N (delta n) hN (delta_pos hn) (delta_le hn)).1) hI

theorem sqrt_two_mul_le (ℓ : ℕ) : Real.sqrt ((2 * ℓ : ℕ) : ℝ) ≤ 2 * Real.sqrt ℓ := by
  push_cast
  rw [Real.sqrt_mul (by norm_num)]
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)

/-- The constant of Lemma 4. -/
def K₁ (cS cM r : ℝ) : ℝ := 144 * cM * r + 144 * cS + 48 * cM

/-- **Lemma 4, cost.** One call costs `O(√ℓ log² n)`. -/
theorem occQ_le (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n ℓ : ℕ} {r : ℝ}
    (hn : 3 ≤ n) (hℓ : 1 ≤ ℓ) (hr : 0 ≤ r) :
    occQ M n r ℓ ≤ K₁ cS cM r * Real.sqrt ℓ * Lam n ^ 2 := by
  have hL := lam_ge_one hn
  have hL0 : 0 ≤ Lam n := by linarith
  have hs := Real.sqrt_nonneg (ℓ : ℝ)
  have h1 := minQ_le hM (I := r * Lam n) hn hℓ (mul_nonneg hr hL0)
  have h2 := searchQ_le hG (I := 1) hn hℓ zero_le_one
  have h3 := minQ_le hM (N := 2 * ℓ) (I := 1) hn (by omega) zero_le_one
  have h4 : 12 * cM * Real.sqrt ((2 * ℓ : ℕ) : ℝ) * Lam n * 1 ≤ 12 * cM * (2 * Real.sqrt ℓ) * Lam n * 1 := by
    gcongr
    exact sqrt_two_mul_le ℓ
  have hLL : Lam n ≤ Lam n ^ 2 := by nlinarith
  have hA : 0 ≤ cS * Real.sqrt ℓ := mul_nonneg hcS hs
  have hB : 0 ≤ cM * Real.sqrt ℓ := mul_nonneg hcM hs
  unfold occQ K₁
  have e1 : 12 * (12 * cM * Real.sqrt ℓ * Lam n * (r * Lam n)) = 144 * cM * r * Real.sqrt ℓ * Lam n ^ 2 := by ring
  have e2 : cS * Real.sqrt ℓ * Lam n ≤ cS * Real.sqrt ℓ * Lam n ^ 2 := mul_le_mul_of_nonneg_left hLL hA
  have e3 : cM * Real.sqrt ℓ * Lam n ≤ cM * Real.sqrt ℓ * Lam n ^ 2 := mul_le_mul_of_nonneg_left hLL hB
  nlinarith

theorem occQ_nonneg (hG : GroverCost M cS) (hM : MinCost M cM) {n ℓ : ℕ} {r : ℝ} (hn : 3 ≤ n) (hℓ : 1 ≤ ℓ)
    (hr : 0 ≤ r) : 0 ≤ occQ M n r ℓ := by
  have hL0 : 0 ≤ Lam n := by linarith [lam_ge_one hn]
  have h1 := minQ_nonneg hM (I := r * Lam n) hn hℓ (mul_nonneg hr hL0)
  have h2 := searchQ_nonneg hG (I := 1) hn hℓ zero_le_one
  have h3 := minQ_nonneg hM (N := 2 * ℓ) (I := 1) hn (by omega) zero_le_one
  unfold occQ
  linarith

/-- The constant of a sample. -/
def K₂ (cS cM r : ℝ) : ℝ := 192 * cM * r ^ 2 + 36 * cS * r

/-- **A sample costs `O(√ℓ log³ n)`**, for `1 ≤ ℓ ≤ n`. The minimum findings sum geometrically, since `w` halves. -/
theorem sampleQ_le (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n ℓ : ℕ} {r : ℝ}
    (hn : 3 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) (hr : 0 ≤ r) :
    sampleQ M n r ℓ ≤ K₂ cS cM r * Real.sqrt ℓ * Lam n ^ 3 := by
  have hL := lam_ge_one hn
  have hL0 : 0 ≤ Lam n := by linarith
  have hs := Real.sqrt_nonneg (ℓ : ℝ)
  -- one column of phase `j`
  have hcol : ∀ j ∈ range (Nat.log 2 ℓ + 1),
      r * Lam n * (2 * minQ M n (ℓ / 2 ^ j) (r * Lam n) + searchQ M n ℓ 1) ≤
        48 * cM * r ^ 2 * Real.sqrt ℓ * Lam n ^ 3 * ((3 : ℝ) / 4) ^ j +
          12 * cS * r * Real.sqrt ℓ * Lam n ^ 2 := by
    intro j hj
    have hj' : j ≤ Nat.log 2 ℓ := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hpos : 1 ≤ ℓ / 2 ^ j := by
      rw [Nat.one_le_div_iff (by positivity)]
      exact (Nat.pow_le_pow_right (by norm_num) hj').trans (Nat.pow_log_le_self 2 (by omega))
    have h1 := minQ_le hM (N := ℓ / 2 ^ j) (I := r * Lam n) hn hpos (mul_nonneg hr hL0)
    have h2 := searchQ_le hG (I := 1) hn hℓ zero_le_one
    have h3 := sqrt_div_pow_le ℓ j
    have h4 : 12 * cM * Real.sqrt ((ℓ / 2 ^ j : ℕ) : ℝ) * Lam n * (r * Lam n) ≤
        12 * cM * (((3 : ℝ) / 4) ^ j * Real.sqrt ℓ) * Lam n * (r * Lam n) := by
      gcongr
    have hrL : 0 ≤ r * Lam n := mul_nonneg hr hL0
    calc r * Lam n * (2 * minQ M n (ℓ / 2 ^ j) (r * Lam n) + searchQ M n ℓ 1)
        ≤ r * Lam n * (2 * (12 * cM * (((3 : ℝ) / 4) ^ j * Real.sqrt ℓ) * Lam n * (r * Lam n)) +
            12 * cS * Real.sqrt ℓ * Lam n * 1) := by
          apply mul_le_mul_of_nonneg_left _ hrL
          linarith
      _ = 24 * cM * r ^ 2 * Real.sqrt ℓ * Lam n ^ 3 * ((3 : ℝ) / 4) ^ j +
            12 * cS * r * Real.sqrt ℓ * Lam n ^ 2 := by ring
      _ ≤ _ := by
          have : 0 ≤ cM * r ^ 2 * Real.sqrt ℓ * Lam n ^ 3 * ((3 : ℝ) / 4) ^ j := by positivity
          nlinarith
  unfold sampleQ
  refine (sum_le_sum hcol).trans ?_
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hgeo := sum_three_quarters_le (Nat.log 2 ℓ + 1)
  have hcount : ((Nat.log 2 ℓ + 1 : ℕ) : ℝ) ≤ 3 * Lam n := by
    have hmono : Nat.log 2 ℓ ≤ Nat.log 2 n := Nat.log_mono_right hℓn
    have : ((Nat.log 2 ℓ + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hmono
    exact this.trans (log2_add_one_le hn)
  have hA : 0 ≤ 48 * cM * r ^ 2 * Real.sqrt ℓ * Lam n ^ 3 := by positivity
  have hB : 0 ≤ 12 * cS * r * Real.sqrt ℓ * Lam n ^ 2 := by positivity
  calc 48 * cM * r ^ 2 * Real.sqrt ℓ * Lam n ^ 3 * ∑ j ∈ range (Nat.log 2 ℓ + 1), ((3 : ℝ) / 4) ^ j +
        ((Nat.log 2 ℓ + 1 : ℕ) : ℝ) * (12 * cS * r * Real.sqrt ℓ * Lam n ^ 2)
      ≤ 48 * cM * r ^ 2 * Real.sqrt ℓ * Lam n ^ 3 * 4 +
        (3 * Lam n) * (12 * cS * r * Real.sqrt ℓ * Lam n ^ 2) := by
        gcongr
    _ = K₂ cS cM r * Real.sqrt ℓ * Lam n ^ 3 := by unfold K₂; ring

/-- `√(blocks) · √ℓ ≤ 2 √n`, for `1 ≤ ℓ ≤ n`: this is `√(n/ℓ) · √ℓ` in the proof of Lemma 6. -/
theorem sqrt_blocks_mul_le {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    Real.sqrt (numBlocks n ℓ) * Real.sqrt ℓ ≤ 2 * Real.sqrt n := by
  rw [← Real.sqrt_mul (by positivity)]
  have hb := numBlocks_le (n := n) hℓ
  have h1 : numBlocks n ℓ * ℓ ≤ 2 * n + ℓ := by
    calc numBlocks n ℓ * ℓ ≤ (2 * n / ℓ + 1) * ℓ := Nat.mul_le_mul_right _ hb
      _ = 2 * n / ℓ * ℓ + ℓ := by ring
      _ ≤ 2 * n + ℓ := by
        have := Nat.div_mul_le_self (2 * n) ℓ
        omega
  have h2 : ((numBlocks n ℓ : ℝ) * ℓ) ≤ 4 * n := by
    have : numBlocks n ℓ * ℓ ≤ 4 * n := by omega
    exact_mod_cast this
  calc Real.sqrt ((numBlocks n ℓ : ℝ) * ℓ) ≤ Real.sqrt (4 * n) := Real.sqrt_le_sqrt h2
    _ = 2 * Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]

theorem numBlocks_pos (n ℓ : ℕ) : 1 ≤ numBlocks n ℓ := Nat.le_add_left 1 _

/-- The constant of Lemma 6. -/
def K₄ (cS cM r : ℝ) : ℝ := 72 * cS * K₁ cS cM r

/-- **Lemma 6, cost.** Testing `u` costs `O(√n log³ n)` queries. -/
theorem testQ_le (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n ℓ : ℕ} {r : ℝ}
    (hn : 3 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) (hr : 0 ≤ r) :
    testQ M n r ℓ ≤ K₄ cS cM r * Real.sqrt n * Lam n ^ 3 := by
  have hL := lam_ge_one hn
  have hL0 : 0 ≤ Lam n := by linarith
  have hK : 0 ≤ K₁ cS cM r := by unfold K₁; positivity
  have hocc0 := occQ_nonneg hG hM (ℓ := ℓ) hn hℓ hr
  have hocc := occQ_le hG hM hcS hcM (ℓ := ℓ) hn hℓ hr
  have h1 := searchQ_le hG (N := numBlocks n ℓ) (I := 3 * occQ M n r ℓ) hn (numBlocks_pos n ℓ) (by positivity)
  have h2 := sqrt_blocks_mul_le (n := n) hℓ hℓn
  unfold testQ
  refine h1.trans ?_
  calc 12 * cS * Real.sqrt (numBlocks n ℓ) * Lam n * (3 * occQ M n r ℓ)
      ≤ 12 * cS * Real.sqrt (numBlocks n ℓ) * Lam n * (3 * (K₁ cS cM r * Real.sqrt ℓ * Lam n ^ 2)) := by
        gcongr
    _ = 36 * cS * K₁ cS cM r * Lam n ^ 3 * (Real.sqrt (numBlocks n ℓ) * Real.sqrt ℓ) := by ring
    _ ≤ 36 * cS * K₁ cS cM r * Lam n ^ 3 * (2 * Real.sqrt n) := by gcongr
    _ = K₄ cS cM r * Real.sqrt n * Lam n ^ 3 := by unfold K₄; ring

/-- The constant of Lemma 7. -/
def K₃ (cS cM r : ℝ) : ℝ := 2 * K₁ cS cM r + 576 * cS + 48 * cM

/-- **Lemma 7, cost.** A range costs `O(√(2^k) log² n)`. -/
theorem rangeQ_le (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n k : ℕ} {r : ℝ}
    (hn : 3 ≤ n) (hr : 0 ≤ r) :
    rangeQ M n r k ≤ K₃ cS cM r * Real.sqrt ((2 : ℝ) ^ k) * Lam n ^ 2 := by
  have hL := lam_ge_one hn
  have hL0 : 0 ≤ Lam n := by linarith
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; rfl
  have h0 := occQ_le hG hM hcS hcM (ℓ := 2 ^ k) hn hpos hr
  rw [hcast] at h0
  have h1 := searchQ_le hG (N := 2 * 2 ^ k) (I := 1) hn (by omega) zero_le_one
  have h2 := minQ_le hM (N := 2 * 2 ^ k) (I := 1) hn (by omega) zero_le_one
  have h3 := sqrt_two_mul_le (2 ^ k)
  rw [hcast] at h3
  set s := Real.sqrt ((2 : ℝ) ^ k) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h1' : 12 * cS * Real.sqrt ((2 * 2 ^ k : ℕ) : ℝ) * Lam n * 1 ≤ 12 * cS * (2 * s) * Lam n * 1 := by gcongr
  have h2' : 12 * cM * Real.sqrt ((2 * 2 ^ k : ℕ) : ℝ) * Lam n * 1 ≤ 12 * cM * (2 * s) * Lam n * 1 := by gcongr
  have hLL : Lam n ≤ Lam n ^ 2 := by nlinarith
  have e2 : cS * s * Lam n ≤ cS * s * Lam n ^ 2 := mul_le_mul_of_nonneg_left hLL (mul_nonneg hcS hs0)
  have e3 : cM * s * Lam n ≤ cM * s * Lam n ^ 2 := mul_le_mul_of_nonneg_left hLL (mul_nonneg hcM hs0)
  unfold rangeQ K₃
  nlinarith

/-- `√(2^k) ≤ √n` for `k ≤ log₂ n`. -/
theorem sqrt_pow_log_le {n : ℕ} (hn : 3 ≤ n) : Real.sqrt ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.sqrt n := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

/-- The constant of the summation. -/
def Ctot (cS cM r : ℝ) : ℝ := 4 * K₃ cS cM r + 12 * K₂ cS cM r + 3 * K₄ cS cM r

/-- **The summation.** With at most `τ ≥ 1` tested lengths per range, each in its range and at most `n`, the total is
`O(τ √n log⁴ n)`. -/
theorem total_le (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n : ℕ} {r τ : ℝ}
    (hn : 3 ≤ n) (hr : 0 ≤ r) (hτ : 1 ≤ τ) (T : ℕ → Finset ℕ)
    (hT : ∀ k, k ≤ Nat.log 2 n → ∀ ℓ ∈ T k, 2 ^ k ≤ ℓ ∧ ℓ < 2 ^ (k + 1) ∧ ℓ ≤ n)
    (hcard : ∀ k, k ≤ Nat.log 2 n → ((T k).card : ℝ) ≤ τ) :
    totalQ M n r T ≤ Ctot cS cM r * τ * Real.sqrt n * Lam n ^ 4 := by
  have hL := lam_ge_one hn
  have hL0 : 0 ≤ Lam n := by linarith
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hK1 : 0 ≤ K₁ cS cM r := by unfold K₁; positivity
  have hK2 : 0 ≤ K₂ cS cM r := by unfold K₂; positivity
  have hK3 : 0 ≤ K₃ cS cM r := by unfold K₃; positivity
  have hK4 : 0 ≤ K₄ cS cM r := by unfold K₄; positivity
  set K2 := K₂ cS cM r
  set K3 := K₃ cS cM r
  set K4 := K₄ cS cM r
  have hτ0 : 0 ≤ τ := by linarith
  -- one range
  have hone : ∀ k ∈ range (Nat.log 2 n + 1),
      rangeQ M n r k + sampleQ M n r (2 ^ k) + ∑ ℓ ∈ T k, (sampleQ M n r ℓ + testQ M n r ℓ) ≤
        (K3 + 3 * K2 * τ) * Lam n ^ 4 * Real.sqrt ((2 : ℝ) ^ k) + K4 * τ * Real.sqrt n * Lam n ^ 3 := by
    intro k hk
    have hk' : k ≤ Nat.log 2 n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    set s := Real.sqrt ((2 : ℝ) ^ k) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hL2 : Lam n ^ 2 ≤ Lam n ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    have hL3 : Lam n ^ 3 ≤ Lam n ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    have h2n : 2 ^ k ≤ n := (Nat.pow_le_pow_right (by norm_num) hk').trans (Nat.pow_log_le_self 2 (by omega))
    have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; rfl
    have h1 : rangeQ M n r k ≤ K3 * s * Lam n ^ 4 :=
      (rangeQ_le hG hM hcS hcM hn hr).trans (by gcongr)
    have h2 : sampleQ M n r (2 ^ k) ≤ K2 * s * Lam n ^ 4 := by
      have := sampleQ_le hG hM hcS hcM (ℓ := 2 ^ k) hn Nat.one_le_two_pow h2n hr
      rw [hcast] at this
      exact this.trans (by gcongr)
    have h3 : ∀ ℓ ∈ T k, sampleQ M n r ℓ + testQ M n r ℓ ≤
        2 * K2 * s * Lam n ^ 4 + K4 * Real.sqrt n * Lam n ^ 3 := by
      intro ℓ hℓ
      obtain ⟨hℓ1, hℓ2, hℓ3⟩ := hT k hk' ℓ hℓ
      have hℓpos : 1 ≤ ℓ := Nat.one_le_two_pow.trans hℓ1
      have hsqrt : Real.sqrt ℓ ≤ 2 * s := by
        have hle : (ℓ : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
          have : ℓ ≤ 2 * 2 ^ k := by rw [pow_succ] at hℓ2; omega
          exact_mod_cast this
        have h2' : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]
          norm_num
        calc Real.sqrt ℓ ≤ Real.sqrt (2 * (2 : ℝ) ^ k) := Real.sqrt_le_sqrt hle
          _ = Real.sqrt 2 * s := by rw [Real.sqrt_mul (by norm_num)]
          _ ≤ 2 * s := mul_le_mul_of_nonneg_right h2' hs0
      have h4 := sampleQ_le hG hM hcS hcM hn hℓpos hℓ3 hr
      have h5 := testQ_le hG hM hcS hcM hn hℓpos hℓ3 hr
      have h6 : K2 * Real.sqrt ℓ * Lam n ^ 3 ≤ K2 * (2 * s) * Lam n ^ 4 := by gcongr
      linarith
    have hsum : ∑ ℓ ∈ T k, (sampleQ M n r ℓ + testQ M n r ℓ) ≤
        τ * (2 * K2 * s * Lam n ^ 4 + K4 * Real.sqrt n * Lam n ^ 3) := by
      have hbound : 0 ≤ 2 * K2 * s * Lam n ^ 4 + K4 * Real.sqrt n * Lam n ^ 3 := by positivity
      calc _ ≤ ∑ _ℓ ∈ T k, (2 * K2 * s * Lam n ^ 4 + K4 * Real.sqrt n * Lam n ^ 3) := sum_le_sum h3
        _ = ((T k).card : ℝ) * (2 * K2 * s * Lam n ^ 4 + K4 * Real.sqrt n * Lam n ^ 3) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ τ * _ := mul_le_mul_of_nonneg_right (hcard k hk') hbound
    have hA : 0 ≤ K2 * s * Lam n ^ 4 := by positivity
    have hτA : K2 * s * Lam n ^ 4 ≤ τ * (K2 * s * Lam n ^ 4) := le_mul_of_one_le_left hA hτ
    nlinarith
  unfold totalQ
  refine (sum_le_sum hone).trans ?_
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hgeo : ∑ k ∈ range (Nat.log 2 n + 1), Real.sqrt ((2 : ℝ) ^ k) ≤ 4 * Real.sqrt n :=
    (sum_sqrt_pow_le _).trans (by linarith [sqrt_pow_log_le hn])
  have hcount := log2_add_one_le hn
  have hco : 0 ≤ (K3 + 3 * K2 * τ) * Lam n ^ 4 := by positivity
  have hco2 : 0 ≤ K4 * τ * Real.sqrt n * Lam n ^ 3 := by positivity
  calc (K3 + 3 * K2 * τ) * Lam n ^ 4 * ∑ k ∈ range (Nat.log 2 n + 1), Real.sqrt ((2 : ℝ) ^ k) +
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * (K4 * τ * Real.sqrt n * Lam n ^ 3)
      ≤ (K3 + 3 * K2 * τ) * Lam n ^ 4 * (4 * Real.sqrt n) + (3 * Lam n) * (K4 * τ * Real.sqrt n * Lam n ^ 3) := by
        gcongr
    _ = (4 * K3 + 12 * K2 * τ + 3 * K4 * τ) * Real.sqrt n * Lam n ^ 4 := by ring
    _ ≤ (4 * K3 * τ + 12 * K2 * τ + 3 * K4 * τ) * Real.sqrt n * Lam n ^ 4 := by
        have : 4 * K3 ≤ 4 * K3 * τ := le_mul_of_one_le_right (by positivity) hτ
        gcongr
    _ = Ctot cS cM r * τ * Real.sqrt n * Lam n ^ 4 := by unfold Ctot; ring

/-- **Theorem 1, the query count.** Given the search and minimum-finding costs, the shortest cover costs
`O(√n log⁴ n)`: one test per range. The constant depends only on `cS`, `cM`, `r`. -/
theorem theorem1_cost (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n : ℕ} {r : ℝ}
    (hn : 3 ≤ n) (hr : 0 ≤ r) (T : ℕ → Finset ℕ)
    (hT : ∀ k, k ≤ Nat.log 2 n → ∀ ℓ ∈ T k, 2 ^ k ≤ ℓ ∧ ℓ < 2 ^ (k + 1) ∧ ℓ ≤ n)
    (hcard : ∀ k, k ≤ Nat.log 2 n → (T k).card ≤ 1) :
    totalQ M n r T ≤ Ctot cS cM r * Real.sqrt n * Lam n ^ 4 := by
  have := total_le hG hM hcS hcM (τ := 1) hn hr le_rfl T hT (fun k hk => by exact_mod_cast hcard k hk)
  simpa using this

/-- **Theorem 2, the query count.** All covers cost `O(√n log⁵ n)`: at most `b Λ` tests per range, by bisection. -/
theorem theorem2_cost (hG : GroverCost M cS) (hM : MinCost M cM) (hcS : 0 ≤ cS) (hcM : 0 ≤ cM) {n : ℕ} {r b : ℝ}
    (hn : 3 ≤ n) (hr : 0 ≤ r) (hb : 1 ≤ b) (T : ℕ → Finset ℕ)
    (hT : ∀ k, k ≤ Nat.log 2 n → ∀ ℓ ∈ T k, 2 ^ k ≤ ℓ ∧ ℓ < 2 ^ (k + 1) ∧ ℓ ≤ n)
    (hcard : ∀ k, k ≤ Nat.log 2 n → ((T k).card : ℝ) ≤ b * Lam n) :
    totalQ M n r T ≤ Ctot cS cM r * b * Real.sqrt n * Lam n ^ 5 := by
  have hL := lam_ge_one hn
  have hτ : 1 ≤ b * Lam n := by nlinarith
  have := total_le hG hM hcS hcM (τ := b * Lam n) hn hr hτ T hT hcard
  calc _ ≤ _ := this
    _ = Ctot cS cM r * b * Real.sqrt n * Lam n ^ 5 := by ring

/-- **Lemma 6, the coherent error.** Over `T ≤ n` outer iterations, an inner error `δ = n⁻⁶` adds up in norm to at most
`κ T √δ ≤ κ / n²`, where `κ` is the constant in the `O(√δ)` of one iteration. `T ≤ n` holds once `√n polylog n ≤ n`. -/
theorem coherent_error_le {n : ℕ} {T κ : ℝ} (hn : 3 ≤ n) (hT : T ≤ n) (hκ : 0 ≤ κ) :
    κ * T * Real.sqrt (delta n) ≤ κ / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : Real.sqrt (delta n) = ((n : ℝ) ^ 3)⁻¹ := by
    unfold delta
    rw [show (n : ℝ) ^ 6 = ((n : ℝ) ^ 3) ^ 2 by ring, Real.sqrt_inv, Real.sqrt_sq (by positivity)]
  rw [hs]
  calc κ * T * ((n : ℝ) ^ 3)⁻¹ ≤ κ * n * ((n : ℝ) ^ 3)⁻¹ := by gcongr
    _ = κ / (n : ℝ) ^ 2 := by field_simp

/-- **The union bound of Theorem 1.** If `m` calls each fail with probability at most `δ`, and a run with no failed call is
correct, then the run is wrong with probability at most `m δ`. -/
theorem union_bound_failure {Ω : Type*} (μ : PMF Ω) (m : ℕ) (E : ℕ → Set Ω) (good : Set Ω) (δ : ENNReal)
    (hE : ∀ i, i < m → μ.toOuterMeasure (E i) ≤ δ) (hgood : ∀ ω, (∀ i, i < m → ω ∉ E i) → ω ∈ good) :
    μ.toOuterMeasure goodᶜ ≤ m * δ := by
  have hsub : goodᶜ ⊆ ⋃ i ∈ Finset.range m, E i := by
    intro ω hω
    by_contra hno
    apply hω
    apply hgood
    intro i hi hmem
    exact hno (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi)) hmem)
  calc μ.toOuterMeasure goodᶜ ≤ μ.toOuterMeasure (⋃ i ∈ Finset.range m, E i) := μ.toOuterMeasure.mono hsub
    _ ≤ ∑ i ∈ Finset.range m, μ.toOuterMeasure (E i) := MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, δ := Finset.sum_le_sum fun i hi => hE i (Finset.mem_range.1 hi)
    _ = m * δ := by simp

end Strings
