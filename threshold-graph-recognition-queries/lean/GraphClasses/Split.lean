import GraphClasses.Nested

/-!
# The exact split (Lemma 3) and the balance arithmetic (Lemma 4)

`x` is a pivot row and `w` a pivot column. `R₀, R₁` are the rows split by column `w`, and `C₀, C₁` the columns split
by row `x`. The survivors of a block are the rows and the columns that are not constant on it: Trim removes exactly
the others, in one pass relative to the block given.
-/

open Finset

namespace GraphClasses

variable {R C : Type*}

/-- The rows of `A` with value `v` in column `w`. -/
def rowsAt (M : R → C → Bool) (A : Finset R) (w : C) (v : Bool) : Finset R := A.filter fun r => M r w = v

/-- The columns of `B` with value `v` in row `x`. -/
def colsAt (M : R → C → Bool) (B : Finset C) (x : R) (v : Bool) : Finset C := B.filter fun c => M x c = v

/-- The rows of the block that have both a `1` and a `0` on it. -/
def survR (M : R → C → Bool) (A : Finset R) (B : Finset C) : Finset R :=
  A.filter fun r => (∃ c ∈ B, M r c = true) ∧ ∃ c ∈ B, M r c = false

/-- The columns of the block that have both a `1` and a `0` on it. -/
def survC (M : R → C → Bool) (A : Finset R) (B : Finset C) : Finset C :=
  B.filter fun c => (∃ r ∈ A, M r c = true) ∧ ∃ r ∈ A, M r c = false

theorem survR_subset (M : R → C → Bool) (A : Finset R) (B : Finset C) : survR M A B ⊆ A := filter_subset _ _

theorem survC_subset (M : R → C → Bool) (A : Finset R) (B : Finset C) : survC M A B ⊆ B := filter_subset _ _

section Split

variable {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ} {x : R} {w : C}

theorem mem_rowsAt_true (h : PositionsOn M A B p q) (hw : w ∈ B) {r : R} :
    r ∈ rowsAt M A w true ↔ r ∈ A ∧ q w < p r := by
  simp only [rowsAt, mem_filter]
  exact and_congr_right fun hr => h.2.2 r hr w hw

theorem mem_rowsAt_false (h : PositionsOn M A B p q) (hw : w ∈ B) {r : R} :
    r ∈ rowsAt M A w false ↔ r ∈ A ∧ p r < q w := by
  simp only [rowsAt, mem_filter]
  exact and_congr_right fun hr => h.false_iff hr hw

theorem mem_colsAt_true (h : PositionsOn M A B p q) (hx : x ∈ A) {c : C} :
    c ∈ colsAt M B x true ↔ c ∈ B ∧ q c < p x := by
  simp only [colsAt, mem_filter]
  exact and_congr_right fun hc => h.2.2 x hx c hc

theorem mem_colsAt_false (h : PositionsOn M A B p q) (hx : x ∈ A) {c : C} :
    c ∈ colsAt M B x false ↔ c ∈ B ∧ p x < q c := by
  simp only [colsAt, mem_filter]
  exact and_congr_right fun hc => h.false_iff hx hc

/-- What the positions say about a surviving row of a sub-block. -/
theorem survR_bounds (h : PositionsOn M A B p q) {A' : Finset R} {B' : Finset C} (hA : A' ⊆ A) (hB : B' ⊆ B)
    {r : R} (hr : r ∈ survR M A' B') :
    r ∈ A' ∧ (∃ c ∈ B', q c < p r) ∧ ∃ c ∈ B', p r < q c := by
  obtain ⟨hrA, ⟨c, hc, hm⟩, d, hd, hn⟩ := mem_filter.1 hr
  exact ⟨hrA, ⟨c, hc, (h.2.2 r (hA hrA) c (hB hc)).1 hm⟩, d, hd, (h.false_iff (hA hrA) (hB hd)).1 hn⟩

/-- What the positions say about a surviving column of a sub-block. -/
theorem survC_bounds (h : PositionsOn M A B p q) {A' : Finset R} {B' : Finset C} (hA : A' ⊆ A) (hB : B' ⊆ B)
    {c : C} (hc : c ∈ survC M A' B') :
    c ∈ B' ∧ (∃ r ∈ A', q c < p r) ∧ ∃ r ∈ A', p r < q c := by
  obtain ⟨hcB, ⟨r, hr, hm⟩, s, hs, hn⟩ := mem_filter.1 hc
  exact ⟨hcB, ⟨r, hr, (h.2.2 r (hA hr) c (hB hcB)).1 hm⟩, s, hs, (h.false_iff (hA hs) (hB hcB)).1 hn⟩

theorem rowsAt_subset (M : R → C → Bool) (A : Finset R) (w : C) (v : Bool) : rowsAt M A w v ⊆ A := filter_subset _ _

theorem colsAt_subset (M : R → C → Bool) (B : Finset C) (x : R) (v : Bool) : colsAt M B x v ⊆ B := filter_subset _ _

/-- **Lemma 3, case `M[x, w] = 1`, that is `q(w) < p(x)`.** The recorded block is `0`; each listed row or column is
constant as claimed, ties included; and the survivors lie in `(-∞, q w)`, `(q w, p x)`, `(p x, ∞)`. -/
theorem lemma3_pos (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) (hxw : M x w = true) :
    (∀ r ∈ rowsAt M A w false, ∀ c ∈ colsAt M B x false, M r c = false) ∧
    (∀ c ∈ colsAt M B x true, q w ≤ q c → ∀ r ∈ rowsAt M A w false, M r c = false) ∧
    (∀ r ∈ rowsAt M A w true, p x ≤ p r → ∀ c ∈ colsAt M B x true, M r c = true) ∧
    (∀ c ∈ colsAt M B x true, q c ≤ q w → ∀ r ∈ rowsAt M A w true, M r c = true) ∧
    (∀ r ∈ rowsAt M A w true, p r ≤ p x → ∀ c ∈ colsAt M B x false, M r c = false) ∧
    (∀ r ∈ survR M (rowsAt M A w false) (colsAt M B x true), p r < q w) ∧
    (∀ c ∈ survC M (rowsAt M A w false) (colsAt M B x true), q c < q w) ∧
    (∀ r ∈ survR M (rowsAt M A w true) (colsAt M B x true), q w < p r ∧ p r < p x) ∧
    (∀ c ∈ survC M (rowsAt M A w true) (colsAt M B x true), q w < q c ∧ q c < p x) ∧
    (∀ r ∈ survR M (rowsAt M A w true) (colsAt M B x false), p x < p r) ∧
    (∀ c ∈ survC M (rowsAt M A w true) (colsAt M B x false), p x < q c) := by
  have hqp : q w < p x := (h.2.2 x hx w hw).1 hxw
  have hRA := rowsAt_subset M A w
  have hCB := colsAt_subset M B x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr c hc
    have h1 := ((mem_rowsAt_false h hw).1 hr).2
    have h2 := ((mem_colsAt_false h hx).1 hc).2
    exact (h.false_iff (hRA _ hr) (hCB _ hc)).2 (by omega)
  · intro c hc hle r hr
    have h1 := ((mem_rowsAt_false h hw).1 hr).2
    exact (h.false_iff (hRA _ hr) (hCB _ hc)).2 (by omega)
  · intro r hr hle c hc
    have h2 := ((mem_colsAt_true h hx).1 hc).2
    exact (h.2.2 r (hRA _ hr) c (hCB _ hc)).2 (by omega)
  · intro c hc hle r hr
    have h1 := ((mem_rowsAt_true h hw).1 hr).2
    exact (h.2.2 r (hRA _ hr) c (hCB _ hc)).2 (by omega)
  · intro r hr hle c hc
    have h2 := ((mem_colsAt_false h hx).1 hc).2
    exact (h.false_iff (hRA _ hr) (hCB _ hc)).2 (by omega)
  · intro r hr
    have ⟨h1, _, _⟩ := survR_bounds h (hRA _) (hCB _) hr
    exact ((mem_rowsAt_false h hw).1 h1).2
  · intro c hc
    have ⟨_, ⟨r, hr, h1⟩, _⟩ := survC_bounds h (hRA _) (hCB _) hc
    have h2 := ((mem_rowsAt_false h hw).1 hr).2
    omega
  · intro r hr
    have ⟨h1, _, c, hc, h2⟩ := survR_bounds h (hRA _) (hCB _) hr
    have h3 := ((mem_rowsAt_true h hw).1 h1).2
    have h4 := ((mem_colsAt_true h hx).1 hc).2
    omega
  · intro c hc
    have ⟨h1, _, r, hr, h2⟩ := survC_bounds h (hRA _) (hCB _) hc
    have h3 := ((mem_colsAt_true h hx).1 h1).2
    have h4 := ((mem_rowsAt_true h hw).1 hr).2
    omega
  · intro r hr
    have ⟨_, ⟨c, hc, h2⟩, _⟩ := survR_bounds h (hRA _) (hCB _) hr
    have h4 := ((mem_colsAt_false h hx).1 hc).2
    omega
  · intro c hc
    have ⟨h1, _, _⟩ := survC_bounds h (hRA _) (hCB _) hc
    exact ((mem_colsAt_false h hx).1 h1).2

/-- **Lemma 3, case `M[x, w] = 0`, that is `p(x) < q(w)`.** The recorded block is `1`; each listed row or column is
constant as claimed, ties included; and the survivors lie in `(-∞, p x)`, `(p x, q w)`, `(q w, ∞)`. -/
theorem lemma3_neg (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) (hxw : M x w = false) :
    (∀ r ∈ rowsAt M A w true, ∀ c ∈ colsAt M B x true, M r c = true) ∧
    (∀ r ∈ rowsAt M A w false, p x ≤ p r → ∀ c ∈ colsAt M B x true, M r c = true) ∧
    (∀ r ∈ rowsAt M A w false, p r ≤ p x → ∀ c ∈ colsAt M B x false, M r c = false) ∧
    (∀ c ∈ colsAt M B x false, q w ≤ q c → ∀ r ∈ rowsAt M A w false, M r c = false) ∧
    (∀ c ∈ colsAt M B x false, q c ≤ q w → ∀ r ∈ rowsAt M A w true, M r c = true) ∧
    (∀ r ∈ survR M (rowsAt M A w false) (colsAt M B x true), p r < p x) ∧
    (∀ c ∈ survC M (rowsAt M A w false) (colsAt M B x true), q c < p x) ∧
    (∀ r ∈ survR M (rowsAt M A w false) (colsAt M B x false), p x < p r ∧ p r < q w) ∧
    (∀ c ∈ survC M (rowsAt M A w false) (colsAt M B x false), p x < q c ∧ q c < q w) ∧
    (∀ r ∈ survR M (rowsAt M A w true) (colsAt M B x false), q w < p r) ∧
    (∀ c ∈ survC M (rowsAt M A w true) (colsAt M B x false), q w < q c) := by
  have hpq : p x < q w := (h.false_iff hx hw).1 hxw
  have hRA := rowsAt_subset M A w
  have hCB := colsAt_subset M B x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr c hc
    have h1 := ((mem_rowsAt_true h hw).1 hr).2
    have h2 := ((mem_colsAt_true h hx).1 hc).2
    exact (h.2.2 r (hRA _ hr) c (hCB _ hc)).2 (by omega)
  · intro r hr hle c hc
    have h2 := ((mem_colsAt_true h hx).1 hc).2
    exact (h.2.2 r (hRA _ hr) c (hCB _ hc)).2 (by omega)
  · intro r hr hle c hc
    have h2 := ((mem_colsAt_false h hx).1 hc).2
    exact (h.false_iff (hRA _ hr) (hCB _ hc)).2 (by omega)
  · intro c hc hle r hr
    have h1 := ((mem_rowsAt_false h hw).1 hr).2
    exact (h.false_iff (hRA _ hr) (hCB _ hc)).2 (by omega)
  · intro c hc hle r hr
    have h1 := ((mem_rowsAt_true h hw).1 hr).2
    exact (h.2.2 r (hRA _ hr) c (hCB _ hc)).2 (by omega)
  · intro r hr
    have ⟨_, _, c, hc, h2⟩ := survR_bounds h (hRA _) (hCB _) hr
    have h4 := ((mem_colsAt_true h hx).1 hc).2
    omega
  · intro c hc
    have ⟨h1, _, _⟩ := survC_bounds h (hRA _) (hCB _) hc
    exact ((mem_colsAt_true h hx).1 h1).2
  · intro r hr
    have ⟨h1, ⟨c, hc, h2⟩, _⟩ := survR_bounds h (hRA _) (hCB _) hr
    have h3 := ((mem_rowsAt_false h hw).1 h1).2
    have h4 := ((mem_colsAt_false h hx).1 hc).2
    omega
  · intro c hc
    have ⟨h1, ⟨r, hr, h2⟩, _⟩ := survC_bounds h (hRA _) (hCB _) hc
    have h3 := ((mem_colsAt_false h hx).1 h1).2
    have h4 := ((mem_rowsAt_false h hw).1 hr).2
    omega
  · intro r hr
    have ⟨h1, _, _⟩ := survR_bounds h (hRA _) (hCB _) hr
    exact ((mem_rowsAt_true h hw).1 h1).2
  · intro c hc
    have ⟨_, _, r, hr, h2⟩ := survC_bounds h (hRA _) (hCB _) hc
    have h4 := ((mem_rowsAt_true h hw).1 hr).2
    omega

/-- The three blocks of the split, before trimming. They depend on the value at the pivot. -/
def splitBlocks (M : R → C → Bool) (A : Finset R) (B : Finset C) (x : R) (w : C) :
    (Finset R × Finset C) × (Finset R × Finset C) × (Finset R × Finset C) :=
  if M x w = true then
    ((rowsAt M A w false, colsAt M B x true), (rowsAt M A w true, colsAt M B x true),
      (rowsAt M A w true, colsAt M B x false))
  else
    ((rowsAt M A w false, colsAt M B x true), (rowsAt M A w false, colsAt M B x false),
      (rowsAt M A w true, colsAt M B x false))

/-- The first trimmed block lies below the second, and the second below the third, for rows and columns alike:
there are two thresholds `s < t` separating them. The pivot row and column survive into none of them. -/
theorem split_intervals (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) :
    ∃ s t : ℤ, s < t ∧
      (∀ r ∈ survR M (splitBlocks M A B x w).1.1 (splitBlocks M A B x w).1.2, p r < s) ∧
      (∀ c ∈ survC M (splitBlocks M A B x w).1.1 (splitBlocks M A B x w).1.2, q c < s) ∧
      (∀ r ∈ survR M (splitBlocks M A B x w).2.1.1 (splitBlocks M A B x w).2.1.2, s < p r ∧ p r < t) ∧
      (∀ c ∈ survC M (splitBlocks M A B x w).2.1.1 (splitBlocks M A B x w).2.1.2, s < q c ∧ q c < t) ∧
      (∀ r ∈ survR M (splitBlocks M A B x w).2.2.1 (splitBlocks M A B x w).2.2.2, t < p r) ∧
      (∀ c ∈ survC M (splitBlocks M A B x w).2.2.1 (splitBlocks M A B x w).2.2.2, t < q c) ∧
      ((s = q w ∧ t = p x) ∨ (s = p x ∧ t = q w)) := by
  cases hm : M x w
  · have := lemma3_neg h hx hw hm
    obtain ⟨_, _, _, _, _, a1, a2, a3, a4, a5, a6⟩ := this
    refine ⟨p x, q w, (h.false_iff hx hw).1 hm, ?_⟩
    simp only [splitBlocks, hm, reduceCtorEq, if_false]
    exact ⟨a1, a2, a3, a4, a5, a6, Or.inr (by simp)⟩
  · have := lemma3_pos h hx hw hm
    obtain ⟨_, _, _, _, _, a1, a2, a3, a4, a5, a6⟩ := this
    refine ⟨q w, p x, (h.2.2 x hx w hw).1 hm, ?_⟩
    simp only [splitBlocks, hm, if_true]
    exact ⟨a1, a2, a3, a4, a5, a6, Or.inl (by simp)⟩

/-- **Lemma 3, disjointness.** Each row and each column survives into at most one trimmed block, and the pivots
survive into none. -/
theorem split_disjoint [DecidableEq R] [DecidableEq C] (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) :
    let b := splitBlocks M A B x w
    Disjoint (survR M b.1.1 b.1.2) (survR M b.2.1.1 b.2.1.2) ∧
    Disjoint (survR M b.1.1 b.1.2) (survR M b.2.2.1 b.2.2.2) ∧
    Disjoint (survR M b.2.1.1 b.2.1.2) (survR M b.2.2.1 b.2.2.2) ∧
    Disjoint (survC M b.1.1 b.1.2) (survC M b.2.1.1 b.2.1.2) ∧
    Disjoint (survC M b.1.1 b.1.2) (survC M b.2.2.1 b.2.2.2) ∧
    Disjoint (survC M b.2.1.1 b.2.1.2) (survC M b.2.2.1 b.2.2.2) ∧
    x ∉ survR M b.1.1 b.1.2 ∧ x ∉ survR M b.2.1.1 b.2.1.2 ∧ x ∉ survR M b.2.2.1 b.2.2.2 ∧
    w ∉ survC M b.1.1 b.1.2 ∧ w ∉ survC M b.2.1.1 b.2.1.2 ∧ w ∉ survC M b.2.2.1 b.2.2.2 := by
  intro b
  obtain ⟨s, t, hst, a1, a2, a3, a4, a5, a6, hcase⟩ := split_intervals h hx hw
  have hxne := pos_ne (h.1 x) (h.2.1 w)
  refine ⟨disjoint_left.2 fun r h1 h2 => ?_, disjoint_left.2 fun r h1 h2 => ?_,
    disjoint_left.2 fun r h1 h2 => ?_, disjoint_left.2 fun c h1 h2 => ?_,
    disjoint_left.2 fun c h1 h2 => ?_, disjoint_left.2 fun c h1 h2 => ?_,
    fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have := a1 r h1; have := a3 r h2; omega
  · have := a1 r h1; have := a5 r h2; omega
  · have := a3 r h1; have := a5 r h2; omega
  · have := a2 c h1; have := a4 c h2; omega
  · have := a2 c h1; have := a6 c h2; omega
  · have := a4 c h1; have := a6 c h2; omega
  · have := a1 x h1; omega
  · have := a3 x h1; omega
  · have := a5 x h1; omega
  · have := a2 w h1; omega
  · have := a4 w h1; omega
  · have := a6 w h1; omega

end Split

/-! ## Lemma 4 -/

/-- The elements of `S` strictly below the level `t`. -/
def below {α : Type*} (f : α → ℤ) (S : Finset α) (t : ℤ) : ℕ := (S.filter fun a => f a < t).card

/-- The elements of `S` strictly above the level `t`. -/
def above {α : Type*} (f : α → ℤ) (S : Finset α) (t : ℤ) : ℕ := (S.filter fun a => t < f a).card

/-- **Lemma 4, the arithmetic.** For all ranks in `[1/4, 3/4]`, all four sums are at most `3m/4`. -/
theorem lemma4_arith {a b α β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 1 / 4 ≤ α ∧ α ≤ 3 / 4)
    (hβ : 1 / 4 ≤ β ∧ β ≤ 3 / 4) :
    α * a + β * b ≤ 3 / 4 * (a + b) ∧ α * a + (1 - β) * b ≤ 3 / 4 * (a + b) ∧
    (1 - α) * a + β * b ≤ 3 / 4 * (a + b) ∧ (1 - α) * a + (1 - β) * b ≤ 3 / 4 * (a + b) := by
  obtain ⟨h1, h2⟩ := hα
  obtain ⟨h3, h4⟩ := hβ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_right h1 ha, mul_le_mul_of_nonneg_right h2 ha,
    mul_le_mul_of_nonneg_right h3 hb, mul_le_mul_of_nonneg_right h4 hb]

section Balance

variable {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ} {x : R} {w : C}

/-- The number of rows and columns of a trimmed block. -/
def survSize (M : R → C → Bool) (b : Finset R × Finset C) : ℕ :=
  (survR M b.1 b.2).card + (survC M b.1 b.2).card

/-- The three trimmed blocks are counted by the rows and columns below or above the pivots, according to the
intervals of Lemma 3. In the case `M[x, w] = 1` the blocks hold at most `below + below`, `below + above`,
`above + above`. -/
theorem lemma4_counts_pos (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) (hxw : M x w = true) :
    survSize M (rowsAt M A w false, colsAt M B x true) ≤ below p A (p x) + below q B (q w) ∧
    survSize M (rowsAt M A w true, colsAt M B x true) ≤ below p A (p x) + above q B (q w) ∧
    survSize M (rowsAt M A w true, colsAt M B x false) ≤ above p A (p x) + above q B (q w) := by
  obtain ⟨_, _, _, _, _, a1, a2, a3, a4, a5, a6⟩ := lemma3_pos h hx hw hxw
  have hqp : q w < p x := (h.2.2 x hx w hw).1 hxw
  have hRA := rowsAt_subset M A w
  have hCB := colsAt_subset M B x
  refine ⟨Nat.add_le_add (card_le_card fun r hr => ?_) (card_le_card fun c hc => ?_),
    Nat.add_le_add (card_le_card fun r hr => ?_) (card_le_card fun c hc => ?_),
    Nat.add_le_add (card_le_card fun r hr => ?_) (card_le_card fun c hc => ?_)⟩
  · have h1 := a1 r hr
    exact mem_filter.2 ⟨hRA _ (survR_subset _ _ _ hr), by omega⟩
  · exact mem_filter.2 ⟨hCB _ (survC_subset _ _ _ hc), a2 c hc⟩
  · exact mem_filter.2 ⟨hRA _ (survR_subset _ _ _ hr), (a3 r hr).2⟩
  · exact mem_filter.2 ⟨hCB _ (survC_subset _ _ _ hc), (a4 c hc).1⟩
  · exact mem_filter.2 ⟨hRA _ (survR_subset _ _ _ hr), a5 r hr⟩
  · have h1 := a6 c hc
    exact mem_filter.2 ⟨hCB _ (survC_subset _ _ _ hc), by omega⟩

/-- In the case `M[x, w] = 0` the blocks hold at most `below + below`, `above + below`, `above + above`. -/
theorem lemma4_counts_neg (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) (hxw : M x w = false) :
    survSize M (rowsAt M A w false, colsAt M B x true) ≤ below p A (p x) + below q B (q w) ∧
    survSize M (rowsAt M A w false, colsAt M B x false) ≤ above p A (p x) + below q B (q w) ∧
    survSize M (rowsAt M A w true, colsAt M B x false) ≤ above p A (p x) + above q B (q w) := by
  obtain ⟨_, _, _, _, _, a1, a2, a3, a4, a5, a6⟩ := lemma3_neg h hx hw hxw
  have hpq : p x < q w := (h.false_iff hx hw).1 hxw
  have hRA := rowsAt_subset M A w
  have hCB := colsAt_subset M B x
  refine ⟨Nat.add_le_add (card_le_card fun r hr => ?_) (card_le_card fun c hc => ?_),
    Nat.add_le_add (card_le_card fun r hr => ?_) (card_le_card fun c hc => ?_),
    Nat.add_le_add (card_le_card fun r hr => ?_) (card_le_card fun c hc => ?_)⟩
  · exact mem_filter.2 ⟨hRA _ (survR_subset _ _ _ hr), a1 r hr⟩
  · have h1 := a2 c hc
    exact mem_filter.2 ⟨hCB _ (survC_subset _ _ _ hc), by omega⟩
  · exact mem_filter.2 ⟨hRA _ (survR_subset _ _ _ hr), (a3 r hr).1⟩
  · exact mem_filter.2 ⟨hCB _ (survC_subset _ _ _ hc), (a4 c hc).2⟩
  · have h1 := a5 r hr
    exact mem_filter.2 ⟨hRA _ (survR_subset _ _ _ hr), by omega⟩
  · exact mem_filter.2 ⟨hCB _ (survC_subset _ _ _ hc), a6 c hc⟩

/-- **Lemma 4, ranks.** If the rows below and above the row pivot are bounded by `α a` and `(1 - α) a`, and likewise
for the column pivot with `β`, both in `[1/4, 3/4]`, each of the three trimmed blocks has at most `3m/4` rows and
columns. This is the arithmetic only. How many pivots qualify is counted by `good_card`, which does not go through
`α ∈ [1/4, 3/4]`: that event can have probability below `1/4` for small blocks. -/
theorem lemma4_ranks (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) {α β : ℝ}
    (hα : 1 / 4 ≤ α ∧ α ≤ 3 / 4) (hβ : 1 / 4 ≤ β ∧ β ≤ 3 / 4)
    (h1 : (below p A (p x) : ℝ) ≤ α * A.card) (h2 : (above p A (p x) : ℝ) ≤ (1 - α) * A.card)
    (h3 : (below q B (q w) : ℝ) ≤ β * B.card) (h4 : (above q B (q w) : ℝ) ≤ (1 - β) * B.card) :
    let b := splitBlocks M A B x w
    let m : ℝ := A.card + B.card
    (survSize M b.1 : ℝ) ≤ 3 / 4 * m ∧ (survSize M b.2.1 : ℝ) ≤ 3 / 4 * m ∧ (survSize M b.2.2 : ℝ) ≤ 3 / 4 * m := by
  intro b m
  obtain ⟨e1, e2, e3, e4⟩ := lemma4_arith (a := A.card) (b := B.card) (by positivity) (by positivity) hα hβ
  cases hm : M x w
  · obtain ⟨c1, c2, c3⟩ := lemma4_counts_neg h hx hw hm
    simp only [b, splitBlocks, hm, reduceCtorEq, if_false]
    have c1' : (survSize M (rowsAt M A w false, colsAt M B x true) : ℝ) ≤ below p A (p x) + below q B (q w) := by
      exact_mod_cast c1
    have c2' : (survSize M (rowsAt M A w false, colsAt M B x false) : ℝ) ≤ above p A (p x) + below q B (q w) := by
      exact_mod_cast c2
    have c3' : (survSize M (rowsAt M A w true, colsAt M B x false) : ℝ) ≤ above p A (p x) + above q B (q w) := by
      exact_mod_cast c3
    exact ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨c1, c2, c3⟩ := lemma4_counts_pos h hx hw hm
    simp only [b, splitBlocks, hm, if_true]
    have c1' : (survSize M (rowsAt M A w false, colsAt M B x true) : ℝ) ≤ below p A (p x) + below q B (q w) := by
      exact_mod_cast c1
    have c2' : (survSize M (rowsAt M A w true, colsAt M B x true) : ℝ) ≤ below p A (p x) + above q B (q w) := by
      exact_mod_cast c2
    have c3' : (survSize M (rowsAt M A w true, colsAt M B x false) : ℝ) ≤ above p A (p x) + above q B (q w) := by
      exact_mod_cast c3
    exact ⟨by linarith, by linarith, by linarith⟩

end Balance

/-! ## How many pivots have a good rank -/

/-- A pivot is good if at most three quarters lie strictly below it and at most three quarters strictly above it.
This is the property used in Lemma 4: at most `3a/4` strictly on either side, whatever the ties. -/
def Good {α : Type*} (f : α → ℤ) (S : Finset α) (a : α) : Prop :=
  4 * below f S (f a) ≤ 3 * S.card ∧ 4 * above f S (f a) ≤ 3 * S.card

instance {α : Type*} (f : α → ℤ) (S : Finset α) : DecidablePred (Good f S) := fun _ => by
  unfold Good; infer_instance

/-- At most a quarter of the elements have more than three quarters strictly below them. -/
private theorem bad_high_card {α : Type*} [DecidableEq α] (f : α → ℤ) (S : Finset α) :
    4 * (S.filter fun a => ¬ 4 * below f S (f a) ≤ 3 * S.card).card ≤ S.card := by
  set T := S.filter fun a => ¬ 4 * below f S (f a) ≤ 3 * S.card with hT
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  · obtain ⟨a₀, ha₀, hmin⟩ := exists_min_image T f hne
    have hdis : Disjoint T (S.filter fun a => f a < f a₀) := by
      refine disjoint_left.2 fun a ha hb => ?_
      have := hmin a ha
      have := (mem_filter.1 hb).2
      omega
    have hsub : T ∪ (S.filter fun a => f a < f a₀) ⊆ S :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdis] at hcard
    have hbad := (mem_filter.1 ha₀).2
    simp only [below] at hbad
    omega

/-- At least half the elements of a finite set are good pivots, ties included. -/
theorem good_card {α : Type*} [DecidableEq α] (f : α → ℤ) (S : Finset α) :
    S.card ≤ 2 * (S.filter (Good f S)).card := by
  have h1 := bad_high_card f S
  have h2 := bad_high_card (fun a => - f a) S
  have hab : ∀ a, above f S (f a) = below (fun a => - f a) S (- f a) := by
    intro a
    simp only [above, below]
    congr 1
    ext b
    simp only [mem_filter]
    constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by omega⟩
  have hsub : S ⊆ (S.filter (Good f S)) ∪ (S.filter fun a => ¬ 4 * below f S (f a) ≤ 3 * S.card) ∪
      (S.filter fun a => ¬ 4 * below (fun a => - f a) S (- f a) ≤ 3 * S.card) := by
    intro a ha
    simp only [mem_union, mem_filter, Good, hab]
    tauto
  have hc := card_le_card hsub
  have hu := card_union_le ((S.filter (Good f S)) ∪ (S.filter fun a => ¬ 4 * below f S (f a) ≤ 3 * S.card))
    (S.filter fun a => ¬ 4 * below (fun a => - f a) S (- f a) ≤ 3 * S.card)
  have hu' := card_union_le (S.filter (Good f S)) (S.filter fun a => ¬ 4 * below f S (f a) ≤ 3 * S.card)
  omega

/-- **Lemma 4, the count behind "probability at least 1/4".** At least a quarter of the pivot pairs are good. -/
theorem good_pairs_card [DecidableEq R] [DecidableEq C] (p : R → ℤ) (q : C → ℤ) (A : Finset R) (B : Finset C) :
    A.card * B.card ≤ 4 * (((A ×ˢ B).filter fun e => Good p A e.1 ∧ Good q B e.2).card) := by
  have hprod : (A ×ˢ B).filter (fun e => Good p A e.1 ∧ Good q B e.2) = (A.filter (Good p A)) ×ˢ (B.filter (Good q B)) :=
    filter_product _ _
  rw [hprod, card_product]
  have h1 := good_card p A
  have h2 := good_card q B
  calc A.card * B.card ≤ (2 * (A.filter (Good p A)).card) * (2 * (B.filter (Good q B)).card) :=
        Nat.mul_le_mul h1 h2
    _ = _ := by ring

/-- **Lemma 4, good pivots.** With good pivots each trimmed block has at most `3m/4` rows and columns. -/
theorem lemma4_good {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ} {x : R} {w : C}
    (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) (hgx : Good p A x) (hgw : Good q B w) :
    let b := splitBlocks M A B x w
    4 * survSize M b.1 ≤ 3 * (A.card + B.card) ∧ 4 * survSize M b.2.1 ≤ 3 * (A.card + B.card) ∧
    4 * survSize M b.2.2 ≤ 3 * (A.card + B.card) := by
  intro b
  obtain ⟨g1, g2⟩ := hgx
  obtain ⟨g3, g4⟩ := hgw
  cases hm : M x w
  · obtain ⟨c1, c2, c3⟩ := lemma4_counts_neg h hx hw hm
    simp only [b, splitBlocks, hm, reduceCtorEq, if_false]
    omega
  · obtain ⟨c1, c2, c3⟩ := lemma4_counts_pos h hx hw hm
    simp only [b, splitBlocks, hm, if_true]
    omega

end GraphClasses
