import Mathlib

/-!
# The threshold grid of the approximation

The thresholds are `t_b = m / (1 + ε)^b`. Every height `v` in `[t_B, m]` lies within a factor `1 + ε` above
some threshold (`grid`), so a rectangle of height `v` and width `W` lies under a run of heights at least `t_b` of
length `L ≥ W`, and `v W ≤ (1 + ε) t_b L` (`approx`).
-/

namespace Histogram

theorem grid {m ε v : ℝ} (hm : 0 < m) (hε : 0 < ε) {B : ℕ} (h1 : m / (1 + ε) ^ B ≤ v) (h2 : v ≤ m) :
    ∃ b ≤ B, m / (1 + ε) ^ b ≤ v ∧ v ≤ (1 + ε) * (m / (1 + ε) ^ b) := by
  have hex : ∃ b, m / (1 + ε) ^ b ≤ v := ⟨B, h1⟩
  classical
  refine ⟨Nat.find hex, Nat.find_min' hex h1, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with e | e
  · rw [e]; simp only [pow_zero, div_one]; nlinarith
  · have hlt := Nat.find_min hex (Nat.sub_lt e one_pos)
    push_neg at hlt
    have : (1 + ε) ^ Nat.find hex = (1 + ε) ^ (Nat.find hex - 1) * (1 + ε) := by
      rw [← pow_succ, Nat.sub_add_cancel e]
    rw [this, div_mul_eq_div_div, mul_div_cancel₀ _ (by linarith)]
    exact hlt.le

theorem approx {t v ε : ℝ} {W L : ℕ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hv : v ≤ (1 + ε) * t) (hWL : W ≤ L) :
    v * W ≤ (1 + ε) * (t * L) := by
  have hW : (W : ℝ) ≤ L := by exact_mod_cast hWL
  calc v * W ≤ (1 + ε) * t * W := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg W)
    _ ≤ (1 + ε) * t * L := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (1 + ε) * (t * L) := by ring

end Histogram
