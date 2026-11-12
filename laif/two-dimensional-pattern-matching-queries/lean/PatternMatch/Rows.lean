import Mathlib

/-!
# Windows of a block and rows as letters

Texts and patterns are maps `ℕ → ℕ → α`. `Occ T P m₁ m₂ r c` says that the `m₁ × m₂` pattern `P` occurs in `T` at
`(r, c)`.

* `occ_window` (Section 8): an occurrence at `B + s` makes the text on `B + C`, with `C = [b₁ - 1, m₁) × [b₂ - 1, m₂)`,
  equal to the window of `s`.
* `star_mono`: condition (★) for `(b₁, b₂)` gives it for every smaller pair.
* `occ_unique` (Section 8): under (★), a block has at most one start that is an occurrence.
* `occ_iff_rows` (Section 9): `P` occurs at `(r, c)` iff the string of its rows occurs in the string of the rows of the
  strip `[c, c + m₂)` at `r`, so the lemmas of `KnownPattern` apply with rows as letters.
-/

namespace PatternMatch.Rows

variable {α : Type*}

/-- The `m₁ × m₂` pattern `P` occurs in `T` at `(r, c)`. -/
def Occ (T P : ℕ → ℕ → α) (m₁ m₂ r c : ℕ) : Prop :=
  ∀ i < m₁, ∀ j < m₂, T (r + i) (c + j) = P i j

/-- Condition (★): the copies of `P` with shifts in `[0, b₁) × [0, b₂)` are pairwise distinct on
`C = [b₁ - 1, m₁) × [b₂ - 1, m₂)`. -/
def Star (P : ℕ → ℕ → α) (m₁ m₂ b₁ b₂ : ℕ) : Prop :=
  ∀ s₁ s₂ t₁ t₂, s₁ < b₁ → s₂ < b₂ → t₁ < b₁ → t₂ < b₂ →
    (∀ z₁ z₂, b₁ - 1 ≤ z₁ → z₁ < m₁ → b₂ - 1 ≤ z₂ → z₂ < m₂ → P (z₁ - s₁) (z₂ - s₂) = P (z₁ - t₁) (z₂ - t₂)) →
    s₁ = t₁ ∧ s₂ = t₂

/-- An occurrence at `B + s` makes the text on `B + C` equal to the window of `s`. -/
theorem occ_window {T P : ℕ → ℕ → α} {m₁ m₂ b₁ b₂ B₁ B₂ s₁ s₂ : ℕ} (hs₁ : s₁ < b₁) (hs₂ : s₂ < b₂)
    (h : Occ T P m₁ m₂ (B₁ + s₁) (B₂ + s₂)) :
    ∀ z₁ z₂, b₁ - 1 ≤ z₁ → z₁ < m₁ → b₂ - 1 ≤ z₂ → z₂ < m₂ → T (B₁ + z₁) (B₂ + z₂) = P (z₁ - s₁) (z₂ - s₂) := by
  intro z₁ z₂ h1 h2 h3 h4
  have e := h (z₁ - s₁) (by omega) (z₂ - s₂) (by omega)
  have e1 : B₁ + s₁ + (z₁ - s₁) = B₁ + z₁ := by omega
  have e2 : B₂ + s₂ + (z₂ - s₂) = B₂ + z₂ := by omega
  rwa [e1, e2] at e

/-- Condition (★) for `(b₁, b₂)` gives it for every smaller pair: the shifts shrink and the cells grow. -/
theorem star_mono {P : ℕ → ℕ → α} {m₁ m₂ b₁ b₂ b₁' b₂' : ℕ} (h : Star P m₁ m₂ b₁ b₂) (h1 : b₁' ≤ b₁)
    (h2 : b₂' ≤ b₂) : Star P m₁ m₂ b₁' b₂' := by
  intro s₁ s₂ t₁ t₂ hs₁ hs₂ ht₁ ht₂ hw
  exact h s₁ s₂ t₁ t₂ (by omega) (by omega) (by omega) (by omega)
    fun z₁ z₂ a b c d => hw z₁ z₂ (by omega) b (by omega) d

/-- **Section 8.** Under (★), two occurrences in the block of `B` have the same shift. -/
theorem occ_unique {T P : ℕ → ℕ → α} {m₁ m₂ b₁ b₂ B₁ B₂ s₁ s₂ t₁ t₂ : ℕ} (hstar : Star P m₁ m₂ b₁ b₂)
    (hs₁ : s₁ < b₁) (hs₂ : s₂ < b₂) (ht₁ : t₁ < b₁) (ht₂ : t₂ < b₂)
    (hs : Occ T P m₁ m₂ (B₁ + s₁) (B₂ + s₂)) (ht : Occ T P m₁ m₂ (B₁ + t₁) (B₂ + t₂)) :
    s₁ = t₁ ∧ s₂ = t₂ :=
  hstar s₁ s₂ t₁ t₂ hs₁ hs₂ ht₁ ht₂ fun z₁ z₂ a b c d =>
    (occ_window hs₁ hs₂ hs z₁ z₂ a b c d).symm.trans (occ_window ht₁ ht₂ ht z₁ z₂ a b c d)

/-- **Section 9.** `P` occurs at `(r, c)` iff the rows of `P`, as letters of type `Fin m₂ → α`, occur at `r` in the
string of the rows of the strip `[c, c + m₂)`. -/
theorem occ_iff_rows {T P : ℕ → ℕ → α} {m₁ m₂ r c : ℕ} :
    Occ T P m₁ m₂ r c ↔
      ∀ i < m₁, (fun j : Fin m₂ => T (r + i) (c + j)) = (fun j : Fin m₂ => P i j) := by
  constructor
  · intro h i hi
    funext j
    exact h i hi j j.2
  · intro h i hi j hj
    exact congrFun (h i hi) ⟨j, hj⟩

end PatternMatch.Rows
