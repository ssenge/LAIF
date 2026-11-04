import Monge.TotallyMonotone

/-!
# The hard family (Theorem 2, upper part)

`M_h[i, j] = -(i - j)²` off the diagonal and `M_h[i, i] = h_i`. It is inverse Monge for every `h`,
its maximum is `OR(h)`, and one entry reveals at most one bit of `h`. The notes check adjacent
blocks; here all blocks are checked directly.
-/

namespace Monge

variable {n : ℕ}

/-- The hard matrix for `h ∈ {0,1}^n`. -/
noncomputable def hard (h : Fin n → Bool) (i j : Fin n) : ℝ :=
  if i = j then (if h i then 1 else 0) else -((i : ℝ) - j) ^ 2

theorem hard_diag (h : Fin n → Bool) (i : Fin n) : hard h i i = if h i then 1 else 0 := by
  simp [hard]

theorem hard_off (h : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    hard h i j = -((i : ℝ) - j) ^ 2 := by
  simp [hard, hij]

private theorem bit_bounds (b : Bool) :
    (0 : ℝ) ≤ (if b then 1 else 0) ∧ (if b then 1 else 0 : ℝ) ≤ 1 := by
  cases b <;> simp

private theorem cast_succ_le {i i' : Fin n} (h : i < i') : (i : ℝ) + 1 ≤ i' := by
  have : (i : ℕ) + 1 ≤ i' := h
  exact_mod_cast this

/-- `M_h` is inverse Monge, for every `h` and all blocks. -/
theorem hard_inverseMonge (h : Fin n → Bool) : InverseMonge (hard h) := by
  intro i i' j j' hi hj
  have hi1 := cast_succ_le hi
  have hj1 := cast_succ_le hj
  have hab : (1 : ℝ) ≤ ((i' : ℝ) - i) * ((j' : ℝ) - j) := by nlinarith
  by_cases h1 : i = j'
  · -- `(i, j')` is on the diagonal, so the three other cells are off the diagonal
    subst h1
    have h2 : i ≠ j := hj.ne'
    have h3 : i' ≠ i := hi.ne'
    have h4 : i' ≠ j := (hj.trans hi).ne'
    rw [hard_diag, hard_off h h2, hard_off h h3, hard_off h h4]
    have := (bit_bounds (h i)).2
    nlinarith
  · by_cases h2 : i' = j
    · subst h2
      have h3 : i ≠ i' := hi.ne
      have h4 : i' ≠ j' := hj.ne
      rw [hard_off h h1, hard_diag, hard_off h h3, hard_off h h4]
      have := (bit_bounds (h i')).2
      nlinarith
    · -- both anti-diagonal cells are off the diagonal, and diagonal cells only help
      rw [hard_off h h1, hard_off h h2]
      have key : ∀ a b : Fin n, -((a : ℝ) - b) ^ 2 ≤ hard h a b := by
        intro a b
        by_cases hab' : a = b
        · subst hab'
          rw [hard_diag]
          have := (bit_bounds (h a)).1
          simp only [sub_self]
          nlinarith
        · rw [hard_off h hab']
      have k1 := key i j
      have k2 := key i' j'
      nlinarith

theorem hard_totallyMonotone (h : Fin n → Bool) : TotallyMonotone (hard h) :=
  (hard_inverseMonge h).totallyMonotone

/-- `OR(h)` as a real number. -/
noncomputable def orValue (h : Fin n → Bool) : ℝ := by
  classical exact if ∃ i, h i = true then 1 else 0

/-- Every entry is at most `OR(h)`. -/
theorem hard_le_or (h : Fin n → Bool) (i j : Fin n) : hard h i j ≤ orValue h := by
  have h0 : (0 : ℝ) ≤ orValue h := by
    unfold orValue
    split_ifs <;> norm_num
  by_cases hij : i = j
  · subst hij
    rw [hard_diag]
    cases hb : h i
    · simpa using h0
    · have : orValue h = 1 := by
        unfold orValue
        rw [ite_eq_left ⟨i, hb⟩]
      simp [this]
  · rw [hard_off h hij]
    nlinarith [sq_nonneg ((i : ℝ) - j)]

/-- `OR(h)` is attained. This needs one diagonal cell, so `n ≥ 1`; in particular it holds for
`n ≥ 2`. -/
theorem or_attained (h : Fin n → Bool) (hn : 0 < n) : ∃ i j, hard h i j = orValue h := by
  by_cases hex : ∃ i, h i = true
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, i, ?_⟩
    have : orValue h = 1 := by
      unfold orValue
      rw [ite_eq_left ⟨i, hi⟩]
    simp [hard_diag, hi, this]
  · refine ⟨⟨0, hn⟩, ⟨0, hn⟩, ?_⟩
    have h0 : orValue h = 0 := by
      unfold orValue
      rw [ite_eq_right hex]
    have hb : h ⟨0, hn⟩ = false := by
      cases hb : h ⟨0, hn⟩
      · rfl
      · exact absurd ⟨_, hb⟩ hex
    simp [hard_diag, hb, h0]

/-- The maximum of `M_h` is exactly `OR(h)`. -/
theorem hard_isGreatest (h : Fin n → Bool) (hn : 0 < n) :
    IsGreatest (Set.range fun q : Fin n × Fin n => hard h q.1 q.2) (orValue h) := by
  constructor
  · obtain ⟨i, j, hij⟩ := or_attained h hn
    exact ⟨(i, j), hij⟩
  · rintro _ ⟨q, rfl⟩
    exact hard_le_or h q.1 q.2

/-- `orValue` really is the OR: it is `1` exactly when some bit is set. -/
theorem orValue_eq_one_iff (h : Fin n → Bool) : orValue h = 1 ↔ ∃ i, h i = true := by
  unfold orValue
  split_ifs with hex <;> simp [hex]

/-- One entry of `M_h` depends on at most one bit of `h`. So a query to `M_h` is answered with at
most one query to `h`, which is what transfers the lower bounds for `OR`. -/
theorem hard_entry_eq_of_bit_eq {h h' : Fin n → Bool} (i j : Fin n) (hb : h i = h' i) :
    hard h i j = hard h' i j := by
  simp [hard, hb]

end Monge
