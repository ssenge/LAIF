import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# The recurrence of Theorem 3

`Γ(r, c) ≤ 2 κ √c + √(1 + Γ(r₁, c₁)² + Γ(r₂, c₂)²)` with `r₁ + r₂ = r - 1`, `c₁ + c₂ = c + 1` solves to
`Γ(r, c) ≤ (2 κ + 1) ⌈log₂(r + 1)⌉ √(c + r)`. `recurrence_step` is the inductive step, used also in
`Monge.Decision` on the actual `γ`.
-/

namespace Monge

/-- `ℓ(r) = ⌈log₂(r + 1)⌉`. -/
def ell (r : ℕ) : ℕ := Nat.clog 2 (r + 1)

@[simp] theorem ell_zero : ell 0 = 0 := by simp [ell]

/-- Halving the rows lowers `ℓ` by one. -/
theorem ell_halve {r r' : ℕ} (hr : 1 ≤ r) (h : r' ≤ r / 2) : ell r' + 1 ≤ ell r := by
  have hpos : 0 < ell r := Nat.clog_pos (by norm_num) (by omega)
  have hle : r + 1 ≤ 2 ^ ell r := Nat.le_pow_clog (by norm_num) _
  obtain ⟨e, he⟩ : ∃ e, ell r = e + 1 := ⟨ell r - 1, by omega⟩
  rw [he, pow_succ] at hle
  have : r' + 1 ≤ 2 ^ e := by omega
  have h2 : ell r' ≤ e := Nat.clog_le_of_le_pow this
  omega

/-- The inductive step of the notes. -/
theorem recurrence_step {κ X₁ X₂ : ℝ} {r c r₁ r₂ c₁ c₂ : ℕ} (hκ : 0 ≤ κ) (hr : 1 ≤ r)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (h₁ : X₁ ≤ (2 * κ + 1) * ell r₁ * √((c₁ : ℝ) + r₁))
    (h₂ : X₂ ≤ (2 * κ + 1) * ell r₂ * √((c₂ : ℝ) + r₂))
    (hr₁ : r₁ ≤ r / 2) (hr₂ : r₂ ≤ r / 2) (hsum : c₁ + r₁ + (c₂ + r₂) = c + r) :
    2 * κ * √(c : ℝ) + √(1 + X₁ ^ 2 + X₂ ^ 2) ≤ (2 * κ + 1) * ell r * √((c : ℝ) + r) := by
  set a := 2 * κ + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  have hl₁ := ell_halve hr hr₁
  have hl₂ := ell_halve hr hr₂
  obtain ⟨e, he⟩ : ∃ e, ell r = e + 1 := ⟨ell r - 1, by omega⟩
  have hl₁' : (ell r₁ : ℝ) ≤ e := by
    have : ell r₁ ≤ e := by omega
    exact_mod_cast this
  have hl₂' : (ell r₂ : ℝ) ≤ e := by
    have : ell r₂ ≤ e := by omega
    exact_mod_cast this
  have he0 : (0 : ℝ) ≤ e := by positivity
  set W := √((c : ℝ) + r) with hW
  have hW2 : W ^ 2 = (c : ℝ) + r := Real.sq_sqrt (by positivity)
  have hW1 : 1 ≤ W := by
    apply Real.one_le_sqrt.mpr
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ c := by positivity
    linarith
  -- the two squares, each against `(a e)² (c_i + r_i)`
  have hsq : ∀ {X : ℝ} {l ci ri : ℕ}, 0 ≤ X → (l : ℝ) ≤ e →
      X ≤ a * l * √((ci : ℝ) + ri) → X ^ 2 ≤ (a * e) ^ 2 * ((ci : ℝ) + ri) := by
    intro X l ci ri hX hl hle
    have h0 : (0 : ℝ) ≤ (ci : ℝ) + ri := by positivity
    have h1 : X ≤ a * e * √((ci : ℝ) + ri) :=
      hle.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl ha0) (Real.sqrt_nonneg _))
    have h2 := pow_le_pow_left₀ hX h1 2
    rwa [mul_pow, Real.sq_sqrt h0] at h2
  have hs₁ := hsq hX₁ hl₁' h₁
  have hs₂ := hsq hX₂ hl₂' h₂
  have hsum' : ((c₁ : ℝ) + r₁) + ((c₂ : ℝ) + r₂) = (c : ℝ) + r := by exact_mod_cast hsum
  have hroot : √(1 + X₁ ^ 2 + X₂ ^ 2) ≤ 1 + a * e * W := by
    apply Real.sqrt_le_iff.mpr
    have h0 : 0 ≤ a * e * W := by positivity
    refine ⟨by positivity, ?_⟩
    have : X₁ ^ 2 + X₂ ^ 2 ≤ (a * e) ^ 2 * W ^ 2 := by
      rw [hW2, ← hsum', mul_add]
      linarith
    nlinarith
  have hc : √(c : ℝ) ≤ W := by
    apply Real.sqrt_le_sqrt
    have : (0 : ℝ) ≤ r := by positivity
    linarith
  rw [he]
  push_cast
  have h1 : 2 * κ * √(c : ℝ) ≤ 2 * κ * W := mul_le_mul_of_nonneg_left hc (by positivity)
  have hexpand : a * ((e : ℝ) + 1) * W = a * e * W + (2 * κ + 1) * W := by
    rw [ha]
    ring
  rw [hexpand]
  nlinarith

/-- **The recurrence solution.** Let `Γ` be nonnegative with `Γ(0, c) = 0`, and suppose that for all
`r, c ≥ 1` there is a split of the columns with `c₁ + c₂ = c + 1`, `c₁, c₂ ≥ 1`, for which the
recursive inequality holds, with `r₁ = ⌊(r - 1) / 2⌋` and `r₂ = ⌊r / 2⌋`. Then
`Γ(r, c) ≤ (2 κ + 1) ⌈log₂(r + 1)⌉ √(c + r)` for all `c ≥ 1`. -/
theorem recurrence_solution {κ : ℝ} (hκ : 0 ≤ κ) (Γ : ℕ → ℕ → ℝ) (h0 : ∀ r c, 0 ≤ Γ r c)
    (hbase : ∀ c, Γ 0 c = 0)
    (hrec : ∀ r c, 1 ≤ r → 1 ≤ c → ∃ c₁ c₂, 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ c₁ + c₂ = c + 1 ∧
      Γ r c ≤ 2 * κ * √(c : ℝ) +
        √(1 + Γ ((r - 1) / 2) c₁ ^ 2 + Γ (r - 1 - (r - 1) / 2) c₂ ^ 2)) (r c : ℕ) (hc : 1 ≤ c) :
    Γ r c ≤ (2 * κ + 1) * ell r * √((c : ℝ) + r) := by
  induction r using Nat.strong_induction_on generalizing c with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [hbase]
    · obtain ⟨c₁, c₂, hc₁, hc₂, hsum, hle⟩ := hrec r c hr hc
      refine hle.trans (recurrence_step hκ hr (h0 _ _) (h0 _ _) (ih _ (by omega) _ hc₁)
        (ih _ (by omega) _ hc₂) (by omega) (by omega) (by omega))

end Monge
