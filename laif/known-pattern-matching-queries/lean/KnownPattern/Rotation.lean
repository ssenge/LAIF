import KnownPattern.Basic

/-!
# The exclusion rule for minimal substrings

Strings are maps `s : ℕ → α` into a linear order. The key of a start `e` for the length `L` is the window
`s[e, e + L)` in lexicographic order, followed by `e`.

* `window_lt_of_diff`, `window_eq_of_agree`: the lexicographic order of two windows is decided at their first
  difference.
* `keys_along_run` (Lemma 1, second part): along an arithmetic progression of starts with step `p` inside a run of
  period `p` that ends at `r` with a letter `s r ≠ s (r - p)`, the keys first increase with equal windows and then
  all increase or all decrease.
* `min_at_ends`: a sequence that increases up to an index and decreases after it attains its least value at an end.
* `exclusion_rule`: so the least key along the progression is at its first or its last element.
-/

namespace KnownPattern

variable {α : Type*} [LinearOrder α]

/-- The window `s[e, e + L)` in lexicographic order. -/
def window (s : ℕ → α) (L e : ℕ) : Lex (Fin L → α) := toLex (fun i => s (e + i))

/-- The key of a start: its window, then the start itself. -/
def key (s : ℕ → α) (L e : ℕ) : Lex (Lex (Fin L → α) × ℕ) := toLex (window s L e, e)

theorem window_lt_of_diff {s : ℕ → α} {L e e' i : ℕ} (hi : i < L) (hagree : ∀ j < i, s (e + j) = s (e' + j))
    (hlt : s (e + i) < s (e' + i)) : window s L e < window s L e' :=
  ⟨⟨i, hi⟩, fun j hj => hagree j.1 hj, hlt⟩

theorem window_eq_of_agree {s : ℕ → α} {L e e' : ℕ} (hagree : ∀ j < L, s (e + j) = s (e' + j)) :
    window s L e = window s L e' := by
  unfold window
  congr 1
  funext i
  exact hagree i i.2

theorem key_lt_of_window_lt {s : ℕ → α} {L e e' : ℕ} (h : window s L e < window s L e') : key s L e < key s L e' :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

theorem key_lt_of_window_eq {s : ℕ → α} {L e e' : ℕ} (h : window s L e = window s L e') (hee : e < e') :
    key s L e < key s L e' :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h, hee⟩)

/-- **One step along a run.** Let `s` have period `p > 0` on `[e, r)`, with `e + p ≤ r`. If `e + p + L ≤ r`, the
windows of `e` and `e + p` are equal. Otherwise their first difference is at the offset `r - p - e`, between the
letters `s (r - p)` and `s r`. -/
theorem step_along_run {s : ℕ → α} {e p r L : ℕ} (hp : HasPeriod s e r p) (her : e + p ≤ r) :
    (e + p + L ≤ r → window s L e = window s L (e + p)) ∧
    (r < e + p + L → s (r - p) < s r → key s L e < key s L (e + p)) ∧
    (r < e + p + L → s r < s (r - p) → key s L (e + p) < key s L e) := by
  have agree : ∀ j, e + p + j < r → s (e + j) = s (e + p + j) := by
    intro j hj
    have := hp (e + j) (by omega) (by omega)
    rw [this]; congr 1; omega
  refine ⟨fun h => window_eq_of_agree fun j hj => agree j (by omega), fun h hlt => ?_, fun h hlt => ?_⟩
  · apply key_lt_of_window_lt
    refine window_lt_of_diff (i := r - p - e) (by omega) (fun j hj => agree j (by omega)) ?_
    have h1 : e + (r - p - e) = r - p := by omega
    have h2 : e + p + (r - p - e) = r := by omega
    rw [h1, h2]; exact hlt
  · apply key_lt_of_window_lt
    refine window_lt_of_diff (i := r - p - e) (by omega) (fun j hj => (agree j (by omega)).symm) ?_
    have h1 : e + (r - p - e) = r - p := by omega
    have h2 : e + p + (r - p - e) = r := by omega
    rw [h1, h2]; exact hlt

/-- **Least value at an end.** If `f` increases on `[0, j₀]` and decreases on `[j₀, k]`, its least value on `[0, k]`
is `f 0` or `f k`. -/
theorem min_at_ends {β : Type*} [LinearOrder β] (f : ℕ → β) (k j₀ : ℕ)
    (hinc : ∀ j < k, j < j₀ → f j < f (j + 1)) (hdec : ∀ j < k, j₀ ≤ j → f (j + 1) < f j) :
    ∀ j ≤ k, min (f 0) (f k) ≤ f j := by
  intro j hj
  by_cases h : j ≤ j₀
  · have : ∀ i, i ≤ j → f 0 ≤ f i := by
      intro i
      induction i with
      | zero => intro _; exact le_rfl
      | succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hinc i (by omega) (by omega)))
    exact le_trans (min_le_left _ _) (this j le_rfl)
  · have : ∀ d, j + d ≤ k → f (j + d) ≤ f j := by
      intro d
      induction d with
      | zero => intro _; exact le_rfl
      | succ d ih =>
        intro hd
        have := hdec (j + d) (by omega) (by omega)
        exact le_trans (le_of_lt (by simpa [add_assoc] using this)) (ih (by omega))
    have := this (k - j) (by omega)
    rw [show j + (k - j) = k by omega] at this
    exact le_trans (min_le_right _ _) this

/-- **Exclusion rule.** Let `s` have period `p > 0` on `[a, r)`, with `a + k p + p ≤ r` when `k > 0`, and let `r` end
the run: `r ≥ n` or `s r ≠ s (r - p)`, where the windows of all starts `a + j p`, `j ≤ k`, end by `n`. Then the least
key over the starts `a + j p`, `j ≤ k`, is the key of `a` or of `a + k p`. -/
theorem exclusion_rule {s : ℕ → α} {a p k r n L : ℕ} (hp0 : 0 < p) (hp : HasPeriod s a r p)
    (hkr : a + k * p ≤ r) (hn : a + k * p + L ≤ n) (hend : n ≤ r ∨ s r ≠ s (r - p)) :
    ∀ j ≤ k, min (key s L a) (key s L (a + k * p)) ≤ key s L (a + j * p) := by
  set f : ℕ → Lex (Lex (Fin L → α) × ℕ) := fun j => key s L (a + j * p) with hf
  have step : ∀ j < k, (a + j * p + p + L ≤ r → f j < f (j + 1)) ∧
      (r < a + j * p + p + L → s (r - p) < s r → f j < f (j + 1)) ∧
      (r < a + j * p + p + L → s r < s (r - p) → f (j + 1) < f j) := by
    intro j hj
    have hjk : (j + 1) * p ≤ k * p := Nat.mul_le_mul_right p hj
    have hrun : HasPeriod s (a + j * p) r p := hp.mono (by omega) le_rfl
    have e1 : a + (j + 1) * p = a + j * p + p := by ring
    obtain ⟨h1, h2, h3⟩ := step_along_run (L := L) hrun (by rw [← e1]; omega)
    refine ⟨fun h => ?_, fun h hlt => ?_, fun h hlt => ?_⟩
    · simp only [hf]; rw [e1]
      exact key_lt_of_window_eq (h1 h) (by omega)
    · simp only [hf]; rw [e1]; exact h2 h hlt
    · simp only [hf]; rw [e1]; exact h3 h hlt
  -- j₀: the first j whose comparison reaches past r
  rcases hend with hnr | hne
  · -- the run reaches the end: all windows along the progression are equal, keys increase
    have := min_at_ends f k k (fun j hj _ => (step j hj).1 (by
      have : (j + 1) * p ≤ k * p := Nat.mul_le_mul_right p hj
      have e1 : (j + 1) * p = j * p + p := by ring
      omega)) (fun j hj h => absurd hj (by omega))
    simpa [hf] using this
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- s r < s (r - p): keys increase while windows are equal, then decrease
      classical
      let P : ℕ → Prop := fun j => r < a + j * p + p + L
      by_cases hex : ∃ j, P j
      · obtain ⟨j₀, hspec, hmin⟩ : ∃ j₀, P j₀ ∧ ∀ j < j₀, ¬ P j :=
          ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
        have := min_at_ends f k j₀
          (fun j hj hj0 => (step j hj).1 (by
            have := hmin j hj0
            simp only [P, not_lt] at this; exact this))
          (fun j hj hj0 => (step j hj).2.2 (by
            have : j₀ * p ≤ j * p := Nat.mul_le_mul_right p hj0
            simp only [P] at hspec; omega) hlt)
        simpa [hf] using this
      · push_neg at hex
        have := min_at_ends f k k (fun j hj _ => (step j hj).1 (by
            have := hex j; simp only [P, not_lt] at this; exact this))
          (fun j hj h => absurd hj (by omega))
        simpa [hf] using this
    · -- s (r - p) < s r: keys increase all along
      have := min_at_ends f k k (fun j hj _ => by
          by_cases h : a + j * p + p + L ≤ r
          · exact (step j hj).1 h
          · exact (step j hj).2.1 (by omega) hgt)
        (fun j hj h => absurd hj (by omega))
      simpa [hf] using this

end KnownPattern
