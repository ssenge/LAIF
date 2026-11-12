import GameLB.Basic
import GameLB.Adversary

/-!
# Bridges

* `inL_eq`: the lexicographically first maximal independent set, built greedily, is the set of losing positions of
  the game with the same matrix.
* `win_weight`: for the inputs with at most one one per row, encoded as in `GameLB.Adversary` and read as a matrix by
  `toMat`, the top position of the game of `GameLB.Basic` wins iff the number of nonempty rows is odd.
-/

namespace GameLB

open Finset

/-- Greedy membership: `j` joins iff none of its neighbours `i < j` has joined. -/
def inL (G : ℕ → ℕ → Bool) (j : ℕ) : Bool :=
  decide (∀ i : Fin j, G j i = true → inL G i = false)
termination_by j
decreasing_by all_goals exact Fin.isLt _

theorem inL_eq (G : ℕ → ℕ → Bool) (j : ℕ) : inL G j = !win G j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    apply Bool.eq_iff_iff.2
    rw [inL, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, win_iff]
    constructor
    · rintro h ⟨i, hi, hg, hw⟩
      have := h ⟨i, hi⟩ hg
      rw [ih i hi, hw] at this
      exact absurd this (by decide)
    · intro h i hg
      rw [ih i i.isLt]
      cases hw : win G i
      · exact absurd ⟨i, i.isLt, hg, hw⟩ h
      · rfl

variable {k s : ℕ}

/-- The matrix of an input with at most one one per row. -/
def toMat (y : Fin k → Option (Fin s)) (t i : ℕ) : Bool :=
  decide (∃ (h : t < k) (h' : i < s), y ⟨t, h⟩ = some ⟨i, h'⟩)

theorem row_toMat (y : Fin k → Option (Fin s)) (t : ℕ) :
    (∃ i < s, toMat y t i = true) ↔ ∃ h : t < k, y ⟨t, h⟩ ≠ none := by
  simp only [toMat, decide_eq_true_eq]
  constructor
  · rintro ⟨i, -, h, h', e⟩
    exact ⟨h, by rw [e]; simp⟩
  · rintro ⟨h, e⟩
    obtain ⟨⟨i, hi⟩, hv⟩ := Option.ne_none_iff_exists'.1 e
    exact ⟨i, hi, h, hi, hv⟩

/-- The nonempty rows among the first `t`. -/
def wUpTo (y : Fin k → Option (Fin s)) (t : ℕ) : ℕ :=
  (univ.filter (fun r : Fin k => r.val < t ∧ y r ≠ none)).card

theorem wUpTo_succ (y : Fin k → Option (Fin s)) (t : ℕ) :
    wUpTo y (t + 1) = wUpTo y t + if (∃ h : t < k, y ⟨t, h⟩ ≠ none) then 1 else 0 := by
  unfold wUpTo
  split_ifs with hr
  · obtain ⟨h, e⟩ := hr
    have : univ.filter (fun r : Fin k => r.val < t + 1 ∧ y r ≠ none) =
        insert ⟨t, h⟩ (univ.filter (fun r : Fin k => r.val < t ∧ y r ≠ none)) := by
      ext r
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hrt : r.val = t
        · left; exact Fin.ext hrt
        · right; exact ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by simp, e⟩
        · exact ⟨by omega, h2⟩
    rw [this, card_insert_of_notMem (by simp)]
  · have : univ.filter (fun r : Fin k => r.val < t + 1 ∧ y r ≠ none) =
        univ.filter (fun r : Fin k => r.val < t ∧ y r ≠ none) := by
      ext r
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_contra hrt
        have hrt' : r.val = t := by omega
        apply hr
        refine ⟨hrt' ▸ r.isLt, ?_⟩
        have hr' : (⟨t, hrt' ▸ r.isLt⟩ : Fin k) = r := Fin.ext hrt'.symm
        rw [hr']
        exact h2
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [this, add_zero]

theorem par_toMat (y : Fin k → Option (Fin s)) (t : ℕ) :
    par s (toMat y) t = decide (Odd (wUpTo y t)) := by
  induction t with
  | zero => simp [par, wUpTo]
  | succ t ih =>
    rw [par, ih, wUpTo_succ]
    have hrow := row_toMat y t
    by_cases hr : ∃ h : t < k, y ⟨t, h⟩ ≠ none
    · have h1 : decide (∃ i < s, toMat y t i = true) = true := decide_eq_true (hrow.2 hr)
      rw [h1, if_pos hr]
      simp [Nat.odd_add_one, ← Nat.not_even_iff_odd]
    · have h1 : decide (∃ i < s, toMat y t i = true) = false := decide_eq_false (fun h => hr (hrow.1 h))
      rw [h1, if_neg hr, add_zero, Bool.xor_false]

theorem wUpTo_k (y : Fin k → Option (Fin s)) : wUpTo y k = weight y := by
  unfold wUpTo weight
  congr 1
  ext r
  simp [r.isLt]

/-- **The bridge.** On the inputs with at most one one per row, the top position of the game of `GameLB.Basic` wins
iff the number of nonempty rows is odd. -/
theorem win_weight (y : Fin k → Option (Fin s)) :
    win (emb s (toMat y)) (s + 5 * k) = decide (Odd (weight y)) := by
  rw [win_top, par_toMat, wUpTo_k]

end GameLB
