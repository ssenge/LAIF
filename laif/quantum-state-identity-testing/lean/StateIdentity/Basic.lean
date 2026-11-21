import Mathlib

/-!
# Scalar steps of quantum state identity testing for every `ε < 1/2`

* `threshold_gap`: with threshold `1/4` and slack `(1 - 2ε)/4`, a pair of fidelity at most `ε`
  gives an antisymmetric acceptance `(1 - ε)/2 > 1/4`, and a pair of fidelity at least `1 - ε`
  gives `ε/2 ≤ 1/4 - (1 - 2ε)/4`.
* `overlap_sq`: the overlap of `√(1-ε)|0⟩ + √ε|1⟩` and `√ε|0⟩ + √(1-ε)|1⟩` squares to `4ε(1-ε)`.
* `helstrom_step`: `(1 - √(1 - f)) / 2 ≤ δ` with `δ < 1/2` forces `f ≤ 4δ(1-δ)`.
* `copies_lower`: `f ^ m ≤ c` with `0 < f < 1` and `0 < c` forces
  `m ≥ log (1/c) / log (1/f)`.
* `log_le_gap`: `log (1/(4ε(1-ε))) ≤ (1-2ε)² / (4ε(1-ε))` for `0 < ε < 1/2`.
* `copies_lower_gap`: the resulting bound `m ≥ 4ε(1-ε) log(1/(4δ(1-δ))) / (1-2ε)²`.
* `gap_compare`: `1 - 2√ε ≤ 1 - 2ε` for `0 ≤ ε ≤ 1`.
-/

namespace StateIdentity

open Real

/-- Threshold and slack for the decision version of threshold search. -/
theorem threshold_gap (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) :
    1 / 4 < (1 - ε) / 2 ∧ ε / 2 ≤ 1 / 4 - (1 - 2 * ε) / 4 ∧ 0 < (1 - 2 * ε) / 4 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Overlap of the two candidate states of the hard pair. -/
theorem overlap_sq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (√(1 - ε) * √ε + √ε * √(1 - ε)) ^ 2 = 4 * ε * (1 - ε) := by
  have ha : (0 : ℝ) ≤ 1 - ε := by linarith
  have e1 : √(1 - ε) * √ε + √ε * √(1 - ε) = 2 * (√(1 - ε) * √ε) := by ring
  rw [e1, mul_pow, mul_pow, sq_sqrt ha, sq_sqrt h0]
  ring

/-- Error of the optimal two-state measurement at most `δ < 1/2` bounds the squared overlap. -/
theorem helstrom_step (f δ : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hδ : δ < 1 / 2)
    (h : (1 - √(1 - f)) / 2 ≤ δ) : f ≤ 4 * δ * (1 - δ) := by
  have hs : 1 - 2 * δ ≤ √(1 - f) := by linarith
  have hpos : 0 ≤ 1 - 2 * δ := by linarith
  have hsq : (1 - 2 * δ) ^ 2 ≤ 1 - f := by
    have := pow_le_pow_left₀ hpos hs 2
    rwa [sq_sqrt (by linarith)] at this
  nlinarith

/-- From `f ^ m ≤ c` to a lower bound on `m`. -/
theorem copies_lower (f c : ℝ) (m : ℕ) (hf0 : 0 < f) (hf1 : f < 1) (hc0 : 0 < c)
    (h : f ^ m ≤ c) : log (1 / c) / log (1 / f) ≤ m := by
  have hlf : 0 < log (1 / f) := log_pos (by rw [lt_div_iff₀ hf0]; linarith)
  rw [div_le_iff₀ hlf]
  have h1 : log (f ^ m) ≤ log c := log_le_log (pow_pos hf0 m) h
  rw [log_pow] at h1
  rw [one_div, log_inv, one_div, log_inv]
  linarith

/-- The logarithm of the inverse squared overlap is at most the gap ratio. -/
theorem log_le_gap (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    log (1 / (4 * ε * (1 - ε))) ≤ (1 - 2 * ε) ^ 2 / (4 * ε * (1 - ε)) := by
  have ha : 0 < 4 * ε * (1 - ε) := by nlinarith
  have hle := log_le_sub_one_of_pos (one_div_pos.mpr ha)
  have : 1 / (4 * ε * (1 - ε)) - 1 = (1 - 2 * ε) ^ 2 / (4 * ε * (1 - ε)) := by
    rw [div_sub_one (ne_of_gt ha)]
    congr 1
    ring
  linarith

/-- Copy lower bound in terms of the gap `1 - 2ε`. -/
theorem copies_lower_gap (ε δ : ℝ) (m : ℕ) (h0 : 0 < ε) (h1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (h : (4 * ε * (1 - ε)) ^ m ≤ 4 * δ * (1 - δ)) :
    4 * ε * (1 - ε) * log (1 / (4 * δ * (1 - δ))) / (1 - 2 * ε) ^ 2 ≤ m := by
  have ha : 0 < 4 * ε * (1 - ε) := by nlinarith
  have ha1 : 4 * ε * (1 - ε) < 1 := by nlinarith
  have hc : 0 < 4 * δ * (1 - δ) := by nlinarith
  have hc1 : 4 * δ * (1 - δ) < 1 := by nlinarith
  have hL : 0 ≤ log (1 / (4 * δ * (1 - δ))) := log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  have hg : 0 < (1 - 2 * ε) ^ 2 := by nlinarith
  have hm := copies_lower _ _ m ha ha1 hc h
  have hlf : 0 < log (1 / (4 * ε * (1 - ε))) := log_pos (by rw [lt_div_iff₀ ha]; linarith)
  have hgap := log_le_gap ε h0 h1
  calc 4 * ε * (1 - ε) * log (1 / (4 * δ * (1 - δ))) / (1 - 2 * ε) ^ 2
      = log (1 / (4 * δ * (1 - δ))) / ((1 - 2 * ε) ^ 2 / (4 * ε * (1 - ε))) := by
        field_simp
    _ ≤ log (1 / (4 * δ * (1 - δ))) / log (1 / (4 * ε * (1 - ε))) :=
        div_le_div_of_nonneg_left hL hlf hgap
    _ ≤ m := hm

/-- The gap `1 - 2ε` is at least `1 - 2√ε`. -/
theorem gap_compare (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : 1 - 2 * √ε ≤ 1 - 2 * ε := by
  have hs : ε ≤ √ε := by
    have h2 : √ε ≤ 1 := sqrt_le_one.mpr h1
    have h3 := mul_self_sqrt h0
    nlinarith [mul_nonneg (sqrt_nonneg ε) (sub_nonneg.mpr h2)]
  linarith

end StateIdentity
