import Mathlib

/-! Arithmetic core of Lemma 4 of `laif/quantum-gomory-hu`. -/

namespace GHMatrix

/-- With `N = h + s` and `3 ≤ s < h`, let `a = |S ∩ L|`, `b = |S ∩ R|`, `a₂ = |S ∩ L₂|` and
`b₂ = |S ∩ R₂|`. If both sides of the cut have at least two vertices, the count
`a(N − a) + b(N − b) + a₂(h − b₂) + b₂(h − a₂)` of crossing edges inside the cliques `L`, `R` and
between `L₂` and `R₂` is at least `Δ = 2h + s − 1`. Stated over `ℤ`. -/
theorem arith (h s a b a₂ b₂ : ℤ) (hs : 3 ≤ s) (hsh : s < h)
    (ha0 : 0 ≤ a₂) (hb0 : 0 ≤ b₂) (ha2a : a₂ ≤ a) (hb2b : b₂ ≤ b) (ha2h : a₂ ≤ h) (hb2h : b₂ ≤ h)
    (ha1 : a ≤ a₂ + s) (hb1 : b ≤ b₂ + s)
    (hS : 2 ≤ a + b) (hT : a + b + 2 ≤ 2 * (h + s)) :
    2 * h + s - 1 ≤ a * (h + s - a) + b * (h + s - b) + a₂ * (h - b₂) + b₂ * (h - a₂) := by
  have hA : 0 ≤ a₂ * (h - b₂) := mul_nonneg ha0 (by linarith)
  have hB : 0 ≤ b₂ * (h - a₂) := mul_nonneg hb0 (by linarith)
  have hhh : 0 ≤ (h - 1) * (h - 2) := mul_nonneg (by linarith) (by linarith)
  rcases (show a = 0 ∨ a = h + s ∨ (1 ≤ a ∧ a ≤ h + s - 1) by omega) with hA0 | hAN | ⟨hA1, hA2⟩ <;>
  rcases (show b = 0 ∨ b = h + s ∨ (1 ≤ b ∧ b ≤ h + s - 1) by omega) with hB0 | hBN | ⟨hB1, hB2⟩
  · omega
  · -- S = R
    have e1 : a₂ = 0 := by omega
    have e2 : b₂ = h := by omega
    rw [hA0, hBN, e1, e2]; nlinarith
  · -- S inside R, splitting it
    have e1 : a₂ = 0 := by omega
    rw [hA0, e1]
    have q1 := mul_nonneg (show (0:ℤ) ≤ b - 1 by linarith) (show (0:ℤ) ≤ h + s - 1 - b by linarith)
    rcases (show b = h + s - 1 ∨ (2 ≤ b ∧ b ≤ h + s - 2) by omega) with e | ⟨f1, f2⟩
    · have q2 := mul_nonneg (show (0:ℤ) ≤ b₂ - 1 by omega) (show (0:ℤ) ≤ h by linarith)
      nlinarith
    · have q2 := mul_nonneg (show (0:ℤ) ≤ b - 2 by linarith) (show (0:ℤ) ≤ h + s - 2 - b by linarith)
      have q3 := mul_nonneg hb0 (show (0:ℤ) ≤ h by linarith)
      nlinarith
  · -- S = L
    have e1 : b₂ = 0 := by omega
    have e2 : a₂ = h := by omega
    rw [hAN, hB0, e1, e2]; nlinarith
  · omega
  · -- S contains L and splits R
    have e2 : a₂ = h := by omega
    rw [hAN, e2]
    have q1 := mul_nonneg (show (0:ℤ) ≤ b - 1 by linarith) (show (0:ℤ) ≤ h + s - 1 - b by linarith)
    rcases (show b = 1 ∨ (2 ≤ b ∧ b ≤ h + s - 2) by omega) with e | ⟨f1, f2⟩
    · have q2 := mul_nonneg (show (0:ℤ) ≤ h - b₂ - 1 by omega) (show (0:ℤ) ≤ h by linarith)
      nlinarith
    · have q2 := mul_nonneg (show (0:ℤ) ≤ b - 2 by linarith) (show (0:ℤ) ≤ h + s - 2 - b by linarith)
      have q3 := mul_nonneg (show (0:ℤ) ≤ h - b₂ by linarith) (show (0:ℤ) ≤ h by linarith)
      nlinarith
  · -- S inside L, splitting it
    have e1 : b₂ = 0 := by omega
    rw [hB0, e1]
    have q1 := mul_nonneg (show (0:ℤ) ≤ a - 1 by linarith) (show (0:ℤ) ≤ h + s - 1 - a by linarith)
    rcases (show a = h + s - 1 ∨ (2 ≤ a ∧ a ≤ h + s - 2) by omega) with e | ⟨f1, f2⟩
    · have q2 := mul_nonneg (show (0:ℤ) ≤ a₂ - 1 by omega) (show (0:ℤ) ≤ h by linarith)
      nlinarith
    · have q2 := mul_nonneg (show (0:ℤ) ≤ a - 2 by linarith) (show (0:ℤ) ≤ h + s - 2 - a by linarith)
      have q3 := mul_nonneg ha0 (show (0:ℤ) ≤ h by linarith)
      nlinarith
  · -- S contains R and splits L
    have e2 : b₂ = h := by omega
    rw [hBN, e2]
    have q1 := mul_nonneg (show (0:ℤ) ≤ a - 1 by linarith) (show (0:ℤ) ≤ h + s - 1 - a by linarith)
    rcases (show a = 1 ∨ (2 ≤ a ∧ a ≤ h + s - 2) by omega) with e | ⟨f1, f2⟩
    · have q2 := mul_nonneg (show (0:ℤ) ≤ h - a₂ - 1 by omega) (show (0:ℤ) ≤ h by linarith)
      nlinarith
    · have q2 := mul_nonneg (show (0:ℤ) ≤ a - 2 by linarith) (show (0:ℤ) ≤ h + s - 2 - a by linarith)
      have q3 := mul_nonneg (show (0:ℤ) ≤ h - a₂ by linarith) (show (0:ℤ) ≤ h by linarith)
      nlinarith
  · -- both cliques split
    have q1 := mul_nonneg (show (0:ℤ) ≤ a - 1 by linarith) (show (0:ℤ) ≤ h + s - 1 - a by linarith)
    have q2 := mul_nonneg (show (0:ℤ) ≤ b - 1 by linarith) (show (0:ℤ) ≤ h + s - 1 - b by linarith)
    nlinarith

end GHMatrix
