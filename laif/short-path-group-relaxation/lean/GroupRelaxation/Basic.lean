import Mathlib

/-!
# An upper bound on the gain of the generalized short-path algorithm on group walks

For the runtime bound of the generalized short-path algorithm with the spectral-gap condition, the gain over a
quadratic speedup of random-walk search is `α = η (1 − η) |E*| b / (2 Δ_P L)`, where `b < δ / 4`, `δ` is the
spectral gap of the walk, `Δ_P` its stability constant and `L = ln(1 / π(E*))`.

Write every energy as its excess `z = H(y) − E* ≥ 0` over the optimum and put `a = η |E*|`. The truncated cost of the
stability condition is then `θ̃(E* + z) = min(0, z / a − 1)` (`theta`).

* `stability_lower`: the stability condition at an optimum, for any transition row with holding probability `p0`,
  gives `Δ_P ≥ ∑ q(y) min(z_y, a)`.
* `well_lt_max`: the spectral-density condition with `γ > 0` and `π(E*) < 1` leaves a state with excess above `a`.
* `alpha_lt`: for a walk that holds with probability `p0` and otherwise takes a uniformly random move from a nonempty
  multiset of moves with excesses `z_s ∈ [0, M]`, `α < (1/8) (1 − η) (δ / (1 − p0)) M / (Γ_S L)`, where `Γ_S` is the mean
  excess over the moves.
-/

open Finset

namespace GroupRelaxation

/-- The truncated cost `θ̃(E* + z) = min(0, z / a − 1)` for an excess `z` over the optimum and well depth `a`. -/
noncomputable def theta (a z : ℝ) : ℝ := min 0 (z / a - 1)

theorem theta_eq {a : ℝ} (ha : 0 < a) (z : ℝ) : theta a z = min z a / a - 1 := by
  unfold theta
  rcases le_total z a with h | h
  · have h1 : z / a - 1 ≤ 0 := by rw [sub_nonpos, div_le_one ha]; exact h
    rw [min_eq_left h, min_eq_right h1]
  · have h1 : 0 ≤ z / a - 1 := by rw [sub_nonneg, one_le_div ha]; exact h
    rw [min_eq_right h, div_self ha.ne', sub_self, min_eq_left h1]

/-- The stability condition `E_y θ̃(H(y)) ≤ θ̃(H(x*) + Δ)` at an optimum `x*`, for a row that stays at `x*` with
probability `p0` and moves to a state with excess `z s` with probability `q s`, forces `Δ ≥ ∑ q s · min(z s, a)`. -/
theorem stability_lower {ι : Type*} (S : Finset ι) (q z : ι → ℝ) {a p0 Δ : ℝ} (ha : 0 < a)
    (hsum : p0 + ∑ s ∈ S, q s = 1)
    (hstab : p0 * theta a 0 + ∑ s ∈ S, q s * theta a (z s) ≤ theta a Δ) :
    ∑ s ∈ S, q s * min (z s) a ≤ Δ := by
  simp only [theta_eq ha] at hstab
  have key : ∑ s ∈ S, q s * (min (z s) a / a - 1) = (∑ s ∈ S, q s * min (z s) a) / a - ∑ s ∈ S, q s := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [key, min_eq_left ha.le, zero_div] at hstab
  have hmin : min Δ a / a ≤ Δ / a := div_le_div_of_nonneg_right (min_le_left _ _) ha.le
  have h2 : (∑ s ∈ S, q s * min (z s) a) / a ≤ Δ / a := by linarith
  exact (div_le_div_iff_of_pos_right ha).mp h2

/-- For `0 ≤ x ≤ M` and `0 < a ≤ M`, `min(x, a) ≥ x a / M`. -/
theorem mul_div_le_min {x a M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) (ha : 0 < a) (haM : a ≤ M) :
    x * a / M ≤ min x a := by
  have hM : 0 < M := lt_of_lt_of_le ha haM
  rcases le_total x a with h | h
  · rw [min_eq_left h, div_le_iff₀ hM]; exact mul_le_mul_of_nonneg_left haM hx
  · rw [min_eq_right h, div_le_iff₀ hM, mul_comm]; exact mul_le_mul_of_nonneg_left hxM ha.le

/-- The spectral-density condition `π(E ≤ (1 − η) E*) ≤ π(E*) ^ γ`, with `γ > 0` and `0 ≤ π(E*) < 1`, leaves a state
whose excess over the optimum exceeds the well depth `a = η |E*|`. -/
theorem well_lt_max {α : Type*} (X : Finset α) (π z : α → ℝ) {a γ πstar : ℝ} (hπ : ∑ x ∈ X, π x = 1)
    (hdens : ∑ x ∈ X.filter (fun x => z x ≤ a), π x ≤ πstar ^ γ) (h0 : 0 ≤ πstar) (h1 : πstar < 1)
    (hγ : 0 < γ) : ∃ x ∈ X, a < z x := by
  by_contra hne
  push_neg at hne
  have hf : X.filter (fun x => z x ≤ a) = X := Finset.filter_true_of_mem hne
  rw [hf, hπ] at hdens
  exact absurd (Real.rpow_lt_one h0 h1 hγ) (not_lt.mpr hdens)

/-- **Theorem 1.** A walk that holds with probability `p0 < 1` and otherwise takes a uniformly random move from the
nonempty multiset `S` of moves, whose excesses over the optimum lie in `[0, M]` with positive mean `Γ_S`, satisfies
the stability condition with `Δ` at the optimum. With well depth `a = η |E*| ≤ M` and `0 < b < δ / 4`, the gain
`α = η (1 − η) |E*| b / (2 Δ L)` satisfies `α < (1/8) (1 − η) (δ / (1 − p0)) M / (Γ_S L)`. -/
theorem alpha_lt {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (z : ι → ℝ) {M p0 η E b δ L Δ : ℝ}
    (hz0 : ∀ s ∈ S, 0 ≤ z s) (hzM : ∀ s ∈ S, z s ≤ M) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hE : 0 < E) (haM : η * E ≤ M) (hΓ : 0 < ∑ s ∈ S, z s) (hb0 : 0 < b) (hb : b < δ / 4) (hL : 0 < L)
    (hstab : p0 * theta (η * E) 0 + ∑ s ∈ S, (1 - p0) / S.card * theta (η * E) (z s) ≤ theta (η * E) Δ) :
    η * (1 - η) * E * b / (2 * Δ * L) < 1 / 8 * (1 - η) * (δ / (1 - p0)) * M / ((∑ s ∈ S, z s) / S.card * L) := by
  set a := η * E with ha_def
  have ha : 0 < a := mul_pos hη0 hE
  have hM : 0 < M := lt_of_lt_of_le ha haM
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hq : 0 < 1 - p0 := by linarith
  have hsum : p0 + ∑ s ∈ S, (1 - p0) / S.card = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp; ring
  have hlow := stability_lower S (fun _ => (1 - p0) / S.card) z ha hsum hstab
  set G := (∑ s ∈ S, z s) / S.card with hG
  have hGpos : 0 < G := div_pos hΓ hc
  -- the stability constant is at least (1 - p0) G a / M
  have hX : (1 - p0) * G * a / M ≤ Δ := by
    refine le_trans ?_ hlow
    have : (1 - p0) * G * a / M = ∑ s ∈ S, (1 - p0) / S.card * (z s * a / M) := by
      rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul, hG]; field_simp
    rw [this]
    refine Finset.sum_le_sum fun s hs => ?_
    exact mul_le_mul_of_nonneg_left (mul_div_le_min (hz0 s hs) (hzM s hs) ha haM) (div_nonneg hq.le hc.le)
  have h1η : 0 < 1 - η := by linarith
  have hXpos : 0 < (1 - p0) * G * a / M := div_pos (mul_pos (mul_pos hq hGpos) ha) hM
  have hΔ : 0 < Δ := lt_of_lt_of_le hXpos hX
  have hnum : 0 ≤ η * (1 - η) * E * b := (mul_pos (mul_pos (mul_pos hη0 h1η) hE) hb0).le
  have hden : 0 < 2 * (1 - p0) * G * L := mul_pos (mul_pos (mul_pos two_pos hq) hGpos) hL
  calc η * (1 - η) * E * b / (2 * Δ * L)
      ≤ η * (1 - η) * E * b / (2 * ((1 - p0) * G * a / M) * L) := by
        apply div_le_div_of_nonneg_left hnum (mul_pos (mul_pos two_pos hXpos) hL)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by norm_num)) hL.le
    _ = (1 - η) * b * M / (2 * (1 - p0) * G * L) := by
        rw [ha_def]; field_simp
    _ < (1 - η) * (δ / 4) * M / (2 * (1 - p0) * G * L) := by
        apply div_lt_div_of_pos_right _ hden
        exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hb h1η) hM
    _ = 1 / 8 * (1 - η) * (δ / (1 - p0)) * M / (G * L) := by
        field_simp; ring

end GroupRelaxation
