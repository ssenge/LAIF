import EmptyRect.Window

/-!
# The window test from the four fronts

Cells of the window are given by their signed distances `z = (x, y)` from the lattice cell. The rectangle with
offset `(a, b)` holds the cells with `-a ≤ x ≤ d - 1 - a` and `-b ≤ y ≤ h - 1 - b` (`InRect`). The window splits into
four quadrants by the signs of `x` and `y` (`Quad`), and each quadrant is read in distances `(|x|, |y|)`. The
rectangle with offset `(a, b)` contains no one-cell of the window iff it contains no front point of any of the
four quadrants (`empty_iff_fronts`, and `rect_empty_iff_fronts` for the window of a grid). So the test needs the
four fronts only.
-/

open Finset

namespace EmptyRect

/-- The cell at signed distances `z` lies in the rectangle with offset `(a, b)`. -/
def InRect (d h a b : ℤ) (z : ℤ × ℤ) : Prop :=
  -a ≤ z.1 ∧ z.1 ≤ d - 1 - a ∧ -b ≤ z.2 ∧ z.2 ≤ h - 1 - b

/-- The quadrant of `z` given by the signs `e`: `e.1` iff `x ≥ 0`, `e.2` iff `y ≥ 0`. -/
def Quad (e : Bool × Bool) (z : ℤ × ℤ) : Prop := (0 ≤ z.1 ↔ e.1 = true) ∧ (0 ≤ z.2 ↔ e.2 = true)

instance (e : Bool × Bool) (z : ℤ × ℤ) : Decidable (Quad e z) := by unfold Quad; infer_instance

/-- Distances from the lattice cell. -/
def dist (z : ℤ × ℤ) : ℕ × ℕ := (z.1.natAbs, z.2.natAbs)

/-- The cell of quadrant `e` at distances `t`. -/
def lift (e : Bool × Bool) (t : ℕ × ℕ) : ℤ × ℤ :=
  (if e.1 then (t.1 : ℤ) else -(t.1 : ℤ), if e.2 then (t.2 : ℤ) else -(t.2 : ℤ))

/-- The front of the one-cells `S` in quadrant `e`, in distances. -/
def qfront (S : Finset (ℤ × ℤ)) (e : Bool × Bool) : Finset (ℕ × ℕ) := front ((S.filter (Quad e)).image dist)

theorem lift_dist {e : Bool × Bool} {z : ℤ × ℤ} (hz : Quad e z) : lift e (dist z) = z := by
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨z1, z2⟩ := z
  simp only [lift, dist, Prod.mk.injEq]
  constructor
  · cases he : e.1
    · simp only [Bool.false_eq_true, ite_false]
      have : z1 < 0 := by rw [he] at h1; simp at h1; omega
      omega
    · simp only [ite_true]
      have : 0 ≤ z1 := by rw [he] at h1; simpa using h1
      omega
  · cases he : e.2
    · simp only [Bool.false_eq_true, ite_false]
      have : z2 < 0 := by rw [he] at h2; simp at h2; omega
      omega
    · simp only [ite_true]
      have : 0 ≤ z2 := by rw [he] at h2; simpa using h2
      omega

/-- A cell of the same quadrant at smaller or equal distances than a cell of the rectangle lies in it too, since the
rectangle contains the lattice cell. -/
theorem inRect_of_le {d h a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (had : a < d) (hbh : b < h) {e : Bool × Bool}
    {z : ℤ × ℤ} (hz : Quad e z) (hin : InRect d h a b z) {t : ℕ × ℕ} (ht : t ≤ dist z) :
    InRect d h a b (lift e t) := by
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨z1, z2⟩ := z
  obtain ⟨t1, t2⟩ := t
  obtain ⟨ht1, ht2⟩ := ht
  simp only [dist] at ht1 ht2
  obtain ⟨i1, i2, i3, i4⟩ := hin
  simp only at i1 i2 i3 i4 h1 h2
  have c1 : (t1 : ℤ) ≤ z1.natAbs := by exact_mod_cast ht1
  have c2 : (t2 : ℤ) ≤ z2.natAbs := by exact_mod_cast ht2
  simp only [InRect, lift]
  cases he1 : e.1 <;> cases he2 : e.2 <;> simp only [he1, he2, Bool.false_eq_true, iff_false, iff_true,
    not_le, ite_true, ite_false] at h1 h2 ⊢
  all_goals
    first
    | (rw [Int.ofNat_natAbs_of_nonpos (by omega)] at c1)
    | (rw [Int.natAbs_of_nonneg (by omega)] at c1)
  all_goals
    first
    | (rw [Int.ofNat_natAbs_of_nonpos (by omega)] at c2)
    | (rw [Int.natAbs_of_nonneg (by omega)] at c2)
  all_goals omega

/-- **The window test.** The rectangle with offset `(a, b)` contains no cell of `S` iff it contains no front point
of any of the four quadrants. -/
theorem empty_iff_fronts (S : Finset (ℤ × ℤ)) {d h a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (had : a < d)
    (hbh : b < h) :
    (∀ z ∈ S, ¬ InRect d h a b z) ↔ ∀ e : Bool × Bool, ∀ t ∈ qfront S e, ¬ InRect d h a b (lift e t) := by
  constructor
  · intro hS e t ht
    obtain ⟨z, hz, rfl⟩ := mem_image.1 (mem_front.1 ht).1
    obtain ⟨hzS, hzq⟩ := mem_filter.1 hz
    rw [lift_dist hzq]
    exact hS z hzS
  · intro hF z hzS hin
    set e : Bool × Bool := (decide (0 ≤ z.1), decide (0 ≤ z.2))
    have hq : Quad e z := by simp [Quad, e]
    have hmem : dist z ∈ (S.filter (Quad e)).image dist := mem_image.2 ⟨z, mem_filter.2 ⟨hzS, hq⟩, rfl⟩
    obtain ⟨t, ht, hle⟩ := exists_front_le _ (dist z) hmem
    exact hF e t ht (inRect_of_le ha hb had hbh hq hin hle)

/-- Every cell of a rectangle with offset `(a, b)`, `0 ≤ a < d`, `0 ≤ b < h`, lies in the window `|x| < d`,
`|y| < h`. -/
theorem inRect_window {d h a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (had : a < d) (hbh : b < h) {z : ℤ × ℤ}
    (hz : InRect d h a b z) : z ∈ Ioo (-d) d ×ˢ Ioo (-h) h := by
  obtain ⟨i1, i2, i3, i4⟩ := hz
  simp only [mem_product, mem_Ioo]
  omega

/-- **The window test for a grid.** With `W` the one-cells of the window of `g` (cells at distances `|x| < d`,
`|y| < h` from the lattice cell), the rectangle with offset `(a, b)` is empty iff no front point of the four
quadrants of `W` lies in it. -/
theorem rect_empty_iff_fronts (g : ℤ × ℤ → Prop) [DecidablePred g] {d h a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (had : a < d) (hbh : b < h) :
    (∀ z, InRect d h a b z → ¬ g z) ↔
      ∀ e : Bool × Bool, ∀ t ∈ qfront ((Ioo (-d) d ×ˢ Ioo (-h) h).filter g) e, ¬ InRect d h a b (lift e t) := by
  rw [← empty_iff_fronts _ ha hb had hbh]
  constructor
  · intro H z hz hin
    exact H z hin (mem_filter.1 hz).2
  · intro H z hin hg
    exact H z (mem_filter.2 ⟨inRect_window ha hb had hbh hin, hg⟩) hin

end EmptyRect
