import Mathlib

/-!
# Counting with coin oracles: the elementary steps of the log-free bound

The quantum part of the bound (amplitude estimation and the log-free composition of bounded-error algorithms)
enters as stated hypotheses in the README. This file checks the elementary steps that turn them into the bound.

* `inner_err_lt`: amplitude estimation with `M ≥ 2π/Δ` points has error bound `2π√(p(1−p))/M + π²/M² < Δ`, so it
  puts `p ≥ 1/2 + Δ` and `p ≤ 1/2 − Δ` on the right side of `1/2`.
* `ae_threshold`: with `M ≥ 8π√(a+e)/e`, the error bound `2π√x/M + π²/M²` keeps every `x ≤ a` below `a + e/2` and
  every `x ≥ a + e` above it.
* `eight_div_pi_sq_gt`: the success probability `8/π²` of amplitude estimation exceeds `4/5`.
* `refine_contains`: one stage of the geometric refinement. Answers that are correct outside the gap locate `ρ` in an
  interval of width `2e`.
* `sum_mul_geom_le`, `sum_geom_le`, `refinement_cost`, `sum_delta_le`: the cost of all stages is a constant times
  the cost of the last one, and the error probabilities `δ 2^{-(k+3)}` sum to at most `δ/4`.
-/

open Finset

namespace BernoulliCounting

/-- The success probability `8/π²` of amplitude estimation exceeds `4/5`. -/
theorem eight_div_pi_sq_gt : (4 : ℝ) / 5 < 8 / Real.pi ^ 2 := by
  have h1 : Real.pi < 3.15 := Real.pi_lt_d2
  have h0 : 0 < Real.pi := Real.pi_pos
  have h2 : Real.pi ^ 2 < 9.9225 := by nlinarith
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- `√(x(1−x)) ≤ 1/2`. -/
theorem sqrt_mul_one_sub_le (x : ℝ) : Real.sqrt (x * (1 - x)) ≤ 1 / 2 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [sq_nonneg (x - 1 / 2)]

/-- Inner decision: with `M ≥ 2π/Δ` and `0 < Δ ≤ 1/2`, the amplitude estimation error bound is below `Δ`. -/
theorem inner_err_lt {Δ M p : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 1 / 2) (hM : 2 * Real.pi / Δ ≤ M) :
    2 * Real.pi * Real.sqrt (p * (1 - p)) / M + Real.pi ^ 2 / M ^ 2 < Δ := by
  have hpi := Real.pi_pos
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hM' : 2 * Real.pi ≤ M * Δ := by rwa [div_le_iff₀ hΔ] at hM
  have h1 : Real.pi / M ≤ Δ / 2 := by rw [div_le_iff₀ hMpos]; linarith
  have h1' : 0 ≤ Real.pi / M := by positivity
  have hs := sqrt_mul_one_sub_le p
  have hs0 := Real.sqrt_nonneg (p * (1 - p))
  have e1 : 2 * Real.pi * Real.sqrt (p * (1 - p)) / M = 2 * Real.sqrt (p * (1 - p)) * (Real.pi / M) := by ring
  have e2 : Real.pi ^ 2 / M ^ 2 = (Real.pi / M) ^ 2 := by ring
  rw [e1, e2]
  have h3 : 2 * Real.sqrt (p * (1 - p)) * (Real.pi / M) ≤ Real.pi / M := by nlinarith
  have h4 : (Real.pi / M) ^ 2 ≤ (Δ / 2) ^ 2 := by nlinarith
  nlinarith

/-- Outer decision: with `M ≥ 8π√(a+e)/e`, an estimate within `2π√x/M + π²/M²` of `x` lies below `a + e/2` when
`x ≤ a` and above it when `x ≥ a + e`. -/
theorem ae_threshold {a e M x err : ℝ} (ha : 0 ≤ a) (he : 0 < e) (hx : 0 ≤ x)
    (hM : 8 * Real.pi * Real.sqrt (a + e) / e ≤ M)
    (herr : err ≤ 2 * Real.pi * Real.sqrt x / M + Real.pi ^ 2 / M ^ 2) :
    (x ≤ a → x + err < a + e / 2) ∧ (a + e ≤ x → a + e / 2 < x - err) := by
  have hpi := Real.pi_pos
  set s := Real.sqrt (a + e) with hs
  have hae : 0 < a + e := by linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr hae
  have hs2 : s ^ 2 = a + e := Real.sq_sqrt hae.le
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hM' : 8 * Real.pi * s ≤ M * e := by rwa [div_le_iff₀ he] at hM
  -- r = π / M satisfies 8 s r ≤ e
  set r := Real.pi / M with hr
  have hr0 : 0 < r := by positivity
  have hrs : 8 * s * r ≤ e := by
    have : 8 * s * r = 8 * Real.pi * s / M := by rw [hr]; ring
    rw [this, div_le_iff₀ hMpos]; linarith
  set u := Real.sqrt x with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg x
  have hu2 : u ^ 2 = x := Real.sq_sqrt hx
  have herr' : err ≤ 2 * u * r + r ^ 2 := by
    have : 2 * Real.pi * u / M + Real.pi ^ 2 / M ^ 2 = 2 * u * r + r ^ 2 := by rw [hr]; ring
    linarith
  have hes : e ≤ s ^ 2 := by rw [hs2]; linarith
  have h8 : 0 ≤ 8 * s * r := by positivity
  -- r² ≤ e/64, from (8 s r)² ≤ e² and e ≤ s²
  have hr2 : r ^ 2 ≤ e / 64 := by
    have hsq : (8 * s * r) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ h8 hrs 2
    have hm : e * (64 * r ^ 2) ≤ s ^ 2 * (64 * r ^ 2) := mul_le_mul_of_nonneg_right hes (by positivity)
    have hm2 : e * (64 * r ^ 2) ≤ e * e := by nlinarith
    have := le_of_mul_le_mul_left hm2 he
    linarith
  constructor
  · intro hxa
    have hus : u ≤ s := by rw [hu, hs]; exact Real.sqrt_le_sqrt (by linarith)
    have h1 : 2 * u * r ≤ 2 * s * r := mul_le_mul_of_nonneg_right (by linarith) hr0.le
    linarith
  · intro hxa
    have hd : 0 ≤ u ^ 2 - s ^ 2 := by rw [hu2, hs2]; linarith
    have h1 : 2 * s * u ≤ s ^ 2 + u ^ 2 := by nlinarith [sq_nonneg (u - s)]
    have hA : (8 * s * r) * (2 * s * u) ≤ e * (2 * s * u) :=
      mul_le_mul_of_nonneg_right hrs (by positivity)
    have hB : e * (2 * s * u) ≤ e * (s ^ 2 + u ^ 2) := mul_le_mul_of_nonneg_left h1 he.le
    have hC : e * (u ^ 2 - s ^ 2) ≤ s ^ 2 * (u ^ 2 - s ^ 2) := mul_le_mul_of_nonneg_right hes hd
    have hD : s ^ 2 * (16 * u * r) ≤ s ^ 2 * (2 * e + (u ^ 2 - s ^ 2)) := by nlinarith
    have hE := le_of_mul_le_mul_left hD (by positivity)
    have hx' : x - a - e = u ^ 2 - s ^ 2 := by rw [hu2, hs2]; ring
    have hpos : 0 ≤ x - a - e := by linarith
    nlinarith

/-- One stage of the refinement. Thresholds `l + k e` for `k < n`; the answer is `true` when `ρ ≥ l + k e + e`
and `false` when `ρ ≤ l + k e`, and arbitrary in between. With `next` the largest threshold answered `true`
(or `l` if there is none), `ρ` lies in `[next, next + 2e)`. -/
theorem refine_contains (l e ρ : ℝ) (n : ℕ) (ans : ℕ → Bool) (he : 0 < e) (hn : 0 < n) (hl : l ≤ ρ)
    (hu : ρ < l + n * e)
    (h1 : ∀ k < n, l + k * e + e ≤ ρ → ans k = true) (h0 : ∀ k < n, ρ ≤ l + k * e → ans k = false) :
    let T := (range n).filter (fun k => ans k = true)
    let next := if h : T.Nonempty then l + (T.max' h : ℕ) * e else l
    next ≤ ρ ∧ ρ < next + 2 * e := by
  intro T next
  by_cases hT : T.Nonempty
  · have hnext : next = l + (T.max' hT : ℕ) * e := dif_pos hT
    set k1 := T.max' hT with hk1
    have hk1T : k1 ∈ T := T.max'_mem hT
    have hk1n : k1 < n := (mem_range.mp (mem_filter.mp hk1T).1)
    have hans : ans k1 = true := (mem_filter.mp hk1T).2
    have hlow : l + (k1 : ℝ) * e < ρ := by
      by_contra hc; push_neg at hc
      have := h0 k1 hk1n hc; rw [hans] at this; exact Bool.noConfusion this
    rw [hnext]
    refine ⟨hlow.le, ?_⟩
    by_cases hlast : k1 + 1 < n
    · have hfalse : ans (k1 + 1) = false := by
        by_contra hc
        have hc' : ans (k1 + 1) = true := by simpa using hc
        have hmem : k1 + 1 ∈ T := mem_filter.mpr ⟨mem_range.mpr hlast, hc'⟩
        have := T.le_max' (k1 + 1) hmem
        rw [← hk1] at this; omega
      by_contra hc; push_neg at hc
      have := h1 (k1 + 1) hlast (by push_cast; linarith)
      rw [hfalse] at this; exact Bool.noConfusion this
    · have hk : k1 + 1 = n := by omega
      have : (n : ℝ) = k1 + 1 := by exact_mod_cast hk.symm
      rw [this] at hu; linarith
  · have hnext : next = l := dif_neg hT
    rw [hnext]
    refine ⟨hl, ?_⟩
    by_contra hc; push_neg at hc
    have h0n : (0 : ℕ) < n := hn
    have := h1 0 h0n (by simp; linarith)
    exact hT ⟨0, mem_filter.mpr ⟨mem_range.mpr h0n, this⟩⟩

/-- `∑_{k<n} (k+3) q^k ≤ q/(1−q)² + 3/(1−q)` for `0 ≤ q < 1`. -/
theorem sum_mul_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 3) * q ^ k ≤ q / (1 - q) ^ 2 + 3 / (1 - q) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hs1 : HasSum (fun k : ℕ => (k : ℝ) * q ^ k) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hs2 : HasSum (fun k : ℕ => q ^ k) (1 - q)⁻¹ := hasSum_geometric_of_lt_one hq0 hq1
  have hs : HasSum (fun k : ℕ => ((k : ℝ) + 3) * q ^ k) (q / (1 - q) ^ 2 + 3 * (1 - q)⁻¹) := by
    have := hs1.add (hs2.mul_left 3)
    convert this using 1
    funext k; ring
  have hle := sum_le_hasSum (range n) (fun k _ => by positivity) hs
  calc ∑ k ∈ range n, ((k : ℝ) + 3) * q ^ k ≤ q / (1 - q) ^ 2 + 3 * (1 - q)⁻¹ := hle
    _ = q / (1 - q) ^ 2 + 3 / (1 - q) := by ring

/-- `∑_{k<n} q^k ≤ 1/(1−q)` for `0 ≤ q < 1`. -/
theorem sum_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ k ∈ range n, q ^ k ≤ 1 / (1 - q) := by
  have h := sum_le_hasSum (range n) (fun k _ => by positivity) (hasSum_geometric_of_lt_one hq0 hq1)
  rw [one_div]; exact h

/-- The cost of all stages. Stage `k` from the end repeats its decisions `k + 3 + D` times (`D` for the target
confidence), each of cost `A · P · (1/2)^k + B · R · q^k` with `0 ≤ q < 1`. The total is at most
`(8 + 2D) A P + (q/(1−q)² + (3 + D)/(1−q)) B R`, a constant times the cost of the last stage. -/
theorem refinement_cost {A B q P R D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    ∑ k ∈ range J, ((k : ℝ) + 3 + D) * (A * P * (1 / 2) ^ k + B * R * q ^ k) ≤
      (8 + 2 * D) * A * P + (q / (1 - q) ^ 2 + (3 + D) / (1 - q)) * B * R := by
  have h1 := sum_mul_geom_le (q := 1 / 2) (by norm_num) (by norm_num) J
  have h2 := sum_mul_geom_le hq0 hq1 J
  have g1 := sum_geom_le (q := 1 / 2) (by norm_num) (by norm_num) J
  have g2 := sum_geom_le hq0 hq1 J
  have e : ∑ k ∈ range J, ((k : ℝ) + 3 + D) * (A * P * (1 / 2) ^ k + B * R * q ^ k) =
      A * P * (∑ k ∈ range J, ((k : ℝ) + 3) * (1 / 2) ^ k + D * ∑ k ∈ range J, ((1 : ℝ) / 2) ^ k) +
      B * R * (∑ k ∈ range J, ((k : ℝ) + 3) * q ^ k + D * ∑ k ∈ range J, q ^ k) := by
    simp only [mul_sum, ← sum_add_distrib]; refine sum_congr rfl fun k _ => by ring
  rw [e]
  have h1' : ∑ k ∈ range J, ((k : ℝ) + 3) * (1 / 2) ^ k ≤ 8 := by norm_num at h1 ⊢; linarith
  have g1' : ∑ k ∈ range J, ((1 : ℝ) / 2) ^ k ≤ 2 := by norm_num at g1 ⊢; linarith
  have hAP : 0 ≤ A * P := mul_nonneg hA hP
  have hBR : 0 ≤ B * R := mul_nonneg hB hR
  have i1 : ∑ k ∈ range J, ((k : ℝ) + 3) * (1 / 2) ^ k + D * ∑ k ∈ range J, ((1 : ℝ) / 2) ^ k ≤
      8 + 2 * D := by
    nlinarith [mul_le_mul_of_nonneg_left g1' hD]
  have i2 : ∑ k ∈ range J, ((k : ℝ) + 3) * q ^ k + D * ∑ k ∈ range J, q ^ k ≤
      q / (1 - q) ^ 2 + (3 + D) / (1 - q) := by
    have : (3 + D) / (1 - q) = 3 / (1 - q) + D * (1 / (1 - q)) := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left g2 hD]
  have j1 := mul_le_mul_of_nonneg_left i1 hAP
  have j2 := mul_le_mul_of_nonneg_left i2 hBR
  nlinarith

/-- The error probabilities `δ · 2^{-(k+3)}` of the stages sum to at most `δ/4`. -/
theorem sum_delta_le {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) :
    ∑ k ∈ range J, δ * ((1 : ℝ) / 2) ^ (k + 3) ≤ δ / 4 := by
  have g := sum_geom_le (q := 1 / 2) (by norm_num) (by norm_num) J
  have e : ∑ k ∈ range J, δ * ((1 : ℝ) / 2) ^ (k + 3) = δ / 8 * ∑ k ∈ range J, ((1 : ℝ) / 2) ^ k := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => by ring
  rw [e]
  have g' : ∑ k ∈ range J, ((1 : ℝ) / 2) ^ k ≤ 2 := by norm_num at g ⊢; linarith
  nlinarith [mul_le_mul_of_nonneg_left g' (by positivity : (0 : ℝ) ≤ δ / 8)]

end BernoulliCounting
