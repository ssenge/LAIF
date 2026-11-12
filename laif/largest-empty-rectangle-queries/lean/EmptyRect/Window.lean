import Mathlib

/-!
# Lattice cells, corner boxes and fronts

Every run of `d` consecutive rows contains exactly one row divisible by `d` (`lattice_unique`), so every rectangle of
`d` rows and `h` columns contains exactly one lattice cell, and a rectangle with at least `D` rows and at least
`H` columns contains a cell of the lattice of spacing `(D, H)` (`lattice_exists`). A cell at signed distance `x` from the lattice cell lies in
the rectangle with offset `a` iff a one-sided condition holds (`mem_rect_iff`). In a quadrant, only the front of the
one-cells matters: every one-cell lies above a front point (`exists_front_le`), and the front of a region splits into
the front of its upper rows and the front of its lower rows left of the least column of the upper rows
(`front_split`). In the lower-bound grids, a run of `d` rows that avoids every row `d` modulo `d + 1` starts at a
multiple of `d + 1` (`block_start`).
-/

open Finset

namespace EmptyRect

/-- **Lemma 1.** Among `d` consecutive naturals exactly one is divisible by `d`. -/
theorem lattice_unique {d : ℕ} (hd : 0 < d) (r : ℕ) : ∃! i, r ≤ i ∧ i < r + d ∧ d ∣ i := by
  set q := (r + d - 1) / d
  have h1 : q * d ≤ r + d - 1 := Nat.div_mul_le_self _ _
  have h2 : r + d - 1 < (q + 1) * d := by
    have := Nat.lt_div_mul_add (a := r + d - 1) hd
    simpa [q, Nat.succ_mul] using this
  have h2' : r + d - 1 < q * d + d := by simpa [Nat.succ_mul] using h2
  refine ⟨q * d, ⟨by omega, by omega, dvd_mul_left _ _⟩, ?_⟩
  rintro i ⟨hi1, hi2, ⟨b, rfl⟩⟩
  have e3 : q * d = d * q := mul_comm _ _
  rcases lt_trichotomy b q with hb | hb | hb
  · have e1 : d * (b + 1) ≤ d * q := Nat.mul_le_mul_left d hb
    have e2 : d * (b + 1) = d * b + d := by ring
    omega
  · rw [hb, mul_comm]
  · have e1 : d * (q + 1) ≤ d * b := Nat.mul_le_mul_left d hb
    have e2 : d * (q + 1) = d * q + d := by ring
    omega

/-- For the shape classes: among `d ≥ D` consecutive naturals at least one is divisible by `D`. -/
theorem lattice_exists {D d : ℕ} (hD : 0 < D) (hDd : D ≤ d) (r : ℕ) : ∃ i, r ≤ i ∧ i < r + d ∧ D ∣ i := by
  obtain ⟨i, ⟨h1, h2, h3⟩, -⟩ := lattice_unique hD r
  exact ⟨i, h1, by omega, h3⟩

/-- **Lemma 2.** With `0 ≤ a < d`, the row at signed distance `x` from the lattice row lies in the rows `[-a, d - a)`
iff `a ≤ d - 1 - x` for `x ≥ 0`, and `a ≥ -x` for `x < 0`. -/
theorem mem_rect_iff {a d x : ℤ} (ha : 0 ≤ a) (had : a < d) :
    (-a ≤ x ∧ x ≤ d - 1 - a) ↔ ((0 ≤ x → a ≤ d - 1 - x) ∧ (x < 0 → -x ≤ a)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun _ => by omega, fun _ => by omega⟩
  · rintro ⟨h1, h2⟩
    by_cases hx : 0 ≤ x
    · have := h1 hx
      omega
    · have := h2 (by omega)
      omega

/-- The front: one-cells with no other one-cell at smaller or equal distances in both coordinates. -/
def front (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := S.filter fun p => ∀ q ∈ S, q ≤ p → q = p

theorem mem_front {S : Finset (ℕ × ℕ)} {p : ℕ × ℕ} : p ∈ front S ↔ p ∈ S ∧ ∀ q ∈ S, q ≤ p → q = p := by
  simp [front]

/-- Every one-cell lies above a point of the front, so a corner box of a one-cell is inside the box of a front
point. -/
theorem exists_front_le (S : Finset (ℕ × ℕ)) : ∀ p ∈ S, ∃ t ∈ front S, t ≤ p := by
  suffices h : ∀ k, ∀ p ∈ S, p.1 + p.2 = k → ∃ t ∈ front S, t ≤ p from fun p hp => h _ p hp rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp hk
    by_cases hf : ∀ q ∈ S, q ≤ p → q = p
    · exact ⟨p, mem_front.2 ⟨hp, hf⟩, le_rfl⟩
    · push Not at hf
      obtain ⟨q, hq, hqp, hne⟩ := hf
      have h1 : q.1 ≤ p.1 := hqp.1
      have h2 : q.2 ≤ p.2 := hqp.2
      have hlt : q.1 + q.2 < k := by
        rcases Nat.lt_or_ge q.1 p.1 with h | h
        · omega
        · have e1 : q.1 = p.1 := le_antisymm h1 h
          have : q.2 ≠ p.2 := fun e => hne (Prod.ext e1 e)
          omega
      obtain ⟨t, ht, htq⟩ := ih _ hlt q hq rfl
      exact ⟨t, ht, htq.trans hqp⟩

/-- **The split of a front.** If every one-cell in the rows below `mid` has column at least `m`, and every one-cell
in the other rows with column at least `m` lies above a one-cell of the rows below `mid`, then the front is the front of
the rows below `mid` together with the front of the other rows left of column `m`. -/
theorem front_split (S : Finset (ℕ × ℕ)) (mid m : ℕ)
    (htop : ∀ q ∈ S, q.1 < mid → m ≤ q.2)
    (hdom : ∀ q ∈ S, mid ≤ q.1 → m ≤ q.2 → ∃ t ∈ S, t.1 < mid ∧ t ≤ q) :
    front S = front (S.filter (·.1 < mid)) ∪ front ((S.filter (mid ≤ ·.1)).filter (·.2 < m)) := by
  ext p
  simp only [mem_union, mem_front, mem_filter]
  constructor
  · rintro ⟨hp, hmin⟩
    by_cases h : p.1 < mid
    · exact Or.inl ⟨⟨hp, h⟩, fun q hq hqp => hmin q hq.1 hqp⟩
    · right
      have hpm : p.2 < m := by
        by_contra hc
        obtain ⟨t, ht, htm, htp⟩ := hdom p hp (by omega) (by omega)
        have := hmin t ht htp
        rw [this] at htm
        exact h htm
      exact ⟨⟨⟨hp, by omega⟩, hpm⟩, fun q hq hqp => hmin q hq.1.1 hqp⟩
  · rintro (⟨⟨hp, h⟩, hmin⟩ | ⟨⟨⟨hp, h⟩, hpm⟩, hmin⟩)
    · refine ⟨hp, fun q hq hqp => hmin q ⟨hq, lt_of_le_of_lt hqp.1 h⟩ hqp⟩
    · refine ⟨hp, fun q hq hqp => ?_⟩
      by_cases hq1 : q.1 < mid
      · have := htop q hq hq1
        have : q.2 ≤ p.2 := hqp.2
        omega
      · exact hmin q ⟨⟨hq, by omega⟩, lt_of_le_of_lt hqp.2 hpm⟩ hqp

/-- In the lower-bound grids the rows `d` modulo `d + 1` are all ones. A run of `d` rows avoiding them starts at a
multiple of `d + 1`, so it is one of the blocks. -/
theorem block_start {d r : ℕ} (h : ∀ i, r ≤ i → i < r + d → i % (d + 1) ≠ d) : (d + 1) ∣ r := by
  have hdr := Nat.div_add_mod r (d + 1)
  set q := r / (d + 1)
  set t := r % (d + 1)
  have ht : t < d + 1 := Nat.mod_lt _ (by omega)
  by_contra hne
  have ht0 : t ≠ 0 := fun e => hne (Nat.dvd_of_mod_eq_zero e)
  apply h ((d + 1) * q + d) (by omega) (by omega)
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

end EmptyRect
