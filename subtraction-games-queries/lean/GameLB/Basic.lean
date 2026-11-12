import Mathlib

/-!
# Subtraction games compute a parity of ORs

A subtraction game on the positions `0, …, n` is given by `g j i`, which says that from `j` stones one may move to
`i < j` stones. A position wins iff some move reaches a losing position (`win_iff`).

The game `emb s x` has a pool of `s` positions without moves, then the position `u₀ = s`, and for every stage `t`
the five positions `bₜ < Nₜ < Aₜ < Bₜ < uₜ₊₁` at `s + 5t + 1, …, s + 5t + 5`. The position `bₜ` moves to the pool
position `i` iff `x t i`, and the other four positions have two fixed moves each, forming an exclusive or of the
values of `uₜ` and `bₜ`. So the position `s + 5k` wins iff an odd number of the rows `x 0, …, x (k - 1)` contain a
one (`win_top`).
-/

namespace GameLB

/-- The value of a position: it wins iff some move reaches a losing position. -/
def win (g : ℕ → ℕ → Bool) (j : ℕ) : Bool :=
  decide (∃ i : Fin j, g j i = true ∧ win g i = false)
termination_by j
decreasing_by all_goals exact Fin.isLt _

theorem win_iff (g : ℕ → ℕ → Bool) (j : ℕ) :
    win g j = true ↔ ∃ i < j, g j i = true ∧ win g i = false := by
  rw [win]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, i.isLt, h1, h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨⟨i, hi⟩, h1, h2⟩

/-- A position with no moves loses. -/
theorem win_of_none {g : ℕ → ℕ → Bool} {j : ℕ} (h : ∀ i, g j i = false) : win g j = false := by
  cases hw : win g j
  · rfl
  · obtain ⟨i, -, hi, -⟩ := (win_iff g j).1 hw
    rw [h i] at hi
    exact absurd hi (by decide)

/-- A position with exactly the moves to `a` and `b` is the NAND of their values. -/
theorem win_two {g : ℕ → ℕ → Bool} {j a b : ℕ} (ha : a < j) (hb : b < j)
    (h : ∀ i, g j i = true ↔ (i = a ∨ i = b)) : win g j = (!win g a || !win g b) := by
  apply Bool.eq_iff_iff.2
  rw [win_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨i, -, hi, hw⟩
    rcases (h i).1 hi with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  · rintro (hw | hw)
    · exact ⟨a, ha, (h a).2 (Or.inl rfl), hw⟩
    · exact ⟨b, hb, (h b).2 (Or.inr rfl), hw⟩

/-- The embedding of the rows `x t` into a subtraction game, with a pool of `s` positions. -/
def emb (s : ℕ) (x : ℕ → ℕ → Bool) (j i : ℕ) : Bool :=
  if j < s then false
  else if (j - s) % 5 = 0 then (decide (s + 5 ≤ j) && (i == j - 2 || i == j - 1))
  else if (j - s) % 5 = 1 then (decide (i < s) && x ((j - s) / 5) i)
  else if (j - s) % 5 = 2 then (i == j - 2 || i == j - 1)
  else if (j - s) % 5 = 3 then (i == j - 3 || i == j - 1)
  else (i == j - 3 || i == j - 2)

/-- Every move of the embedding goes down. -/
theorem emb_lt {s : ℕ} {x : ℕ → ℕ → Bool} {j i : ℕ} (h : emb s x j i = true) : i < j := by
  unfold emb at h
  split_ifs at h with h0 h1 h2 h3 h4 <;> simp at h <;> omega

theorem pool_lose (s : ℕ) (x : ℕ → ℕ → Bool) {j : ℕ} (hj : j < s) : win (emb s x) j = false :=
  win_of_none (fun i => by simp [emb, hj])

theorem start_lose (s : ℕ) (x : ℕ → ℕ → Bool) : win (emb s x) s = false :=
  win_of_none (fun i => by simp [emb])

/-- The position `bₜ` wins iff the row `x t` has a one. -/
theorem b_win (s : ℕ) (x : ℕ → ℕ → Bool) (t : ℕ) :
    win (emb s x) (s + 5 * t + 1) = decide (∃ i < s, x t i = true) := by
  have e1 : ¬ s + 5 * t + 1 < s := by omega
  have e2 : (s + 5 * t + 1 - s) % 5 = 1 := by omega
  have e3 : (s + 5 * t + 1 - s) / 5 = t := by omega
  apply Bool.eq_iff_iff.2
  rw [win_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨i, -, hi, -⟩
    simp [emb, e1, e2, e3] at hi
    exact ⟨i, hi.1, hi.2⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, by omega, ?_, pool_lose s x hi⟩
    simp [emb, e1, e2, e3, hi, hx]

/-- The parity of the number of rows among `x 0, …, x (t - 1)` that contain a one. -/
def par (s : ℕ) (x : ℕ → ℕ → Bool) : ℕ → Bool
  | 0 => false
  | t + 1 => xor (par s x t) (decide (∃ i < s, x t i = true))

/-- **The embedding.** The position `s + 5t` wins iff an odd number of the rows `x 0, …, x (t - 1)` contain a
one. -/
theorem win_top (s : ℕ) (x : ℕ → ℕ → Bool) (t : ℕ) : win (emb s x) (s + 5 * t) = par s x t := by
  induction t with
  | zero => simpa [par] using start_lose s x
  | succ t ih =>
    set u := s + 5 * t with hu
    have mN : ∀ i, emb s x (u + 2) i = true ↔ (i = u ∨ i = u + 1) := by
      intro i
      have e1 : ¬ u + 2 < s := by omega
      have e2 : (u + 2 - s) % 5 = 2 := by omega
      simp [emb, e1, e2] <;> omega
    have mA : ∀ i, emb s x (u + 3) i = true ↔ (i = u ∨ i = u + 2) := by
      intro i
      have e1 : ¬ u + 3 < s := by omega
      have e2 : (u + 3 - s) % 5 = 3 := by omega
      simp [emb, e1, e2] <;> omega
    have mB : ∀ i, emb s x (u + 4) i = true ↔ (i = u + 1 ∨ i = u + 2) := by
      intro i
      have e1 : ¬ u + 4 < s := by omega
      have e2 : (u + 4 - s) % 5 = 4 := by omega
      simp [emb, e1, e2] <;> omega
    have mU : ∀ i, emb s x (u + 5) i = true ↔ (i = u + 3 ∨ i = u + 4) := by
      intro i
      have e1 : ¬ u + 5 < s := by omega
      have e2 : (u + 5 - s) % 5 = 0 := by omega
      have e3 : s + 5 ≤ u + 5 := by omega
      simp [emb, e1, e2, e3] <;> omega
    have wN := win_two (by omega) (by omega) mN
    have wA := win_two (by omega) (by omega) mA
    have wB := win_two (by omega) (by omega) mB
    have wU := win_two (by omega) (by omega) mU
    have wb : win (emb s x) (u + 1) = decide (∃ i < s, x t i = true) := b_win s x t
    rw [show s + 5 * (t + 1) = u + 5 by omega, wU, wA, wB, wN, wb, ih]
    simp only [par]
    cases par s x t <;> cases decide (∃ i < s, x t i = true) <;> rfl

end GameLB
