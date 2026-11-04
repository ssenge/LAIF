import Mathlib

/-!
# Nested matrices and positions (Lemma 1)

A matrix is a function `M : R → C → Bool`. A block is a pair of finite sets of rows and columns. The rows of a
block are nested if, as subsets of the columns of the block, they form a chain under inclusion.
-/

open Finset

namespace GraphClasses

variable {R C : Type*}

/-- The rows of `M`, as subsets of the columns, form a chain under inclusion. -/
def Nested (M : R → C → Bool) : Prop :=
  ∀ r s, (∀ c, M r c = true → M s c = true) ∨ (∀ c, M s c = true → M r c = true)

/-- The rows of the block `A × B`, as subsets of `B`, form a chain under inclusion. -/
def NestedOn (M : R → C → Bool) (A : Finset R) (B : Finset C) : Prop :=
  ∀ r ∈ A, ∀ s ∈ A, (∀ c ∈ B, M r c = true → M s c = true) ∨ (∀ c ∈ B, M s c = true → M r c = true)

/-- Integer positions for the block `A × B`, even on rows and odd on columns, with
`M[r, c] = 1 ⇔ p(r) > q(c)`. -/
def PositionsOn (M : R → C → Bool) (A : Finset R) (B : Finset C) (p : R → ℤ) (q : C → ℤ) : Prop :=
  (∀ r, Even (p r)) ∧ (∀ c, Odd (q c)) ∧ ∀ r ∈ A, ∀ c ∈ B, (M r c = true ↔ q c < p r)

theorem NestedOn.mono {M : R → C → Bool} {A A' : Finset R} {B B' : Finset C} (h : NestedOn M A B)
    (hA : A' ⊆ A) (hB : B' ⊆ B) : NestedOn M A' B' := fun r hr s hs =>
  (h r (hA hr) s (hA hs)).imp (fun g c hc => g c (hB hc)) (fun g c hc => g c (hB hc))

theorem PositionsOn.mono {M : R → C → Bool} {A A' : Finset R} {B B' : Finset C} {p : R → ℤ} {q : C → ℤ}
    (h : PositionsOn M A B p q) (hA : A' ⊆ A) (hB : B' ⊆ B) : PositionsOn M A' B' p q :=
  ⟨h.1, h.2.1, fun r hr c hc => h.2.2 r (hA hr) c (hB hc)⟩

/-- A row position and a column position are never equal. -/
theorem pos_ne {a b : ℤ} (ha : Even a) (hb : Odd b) : a ≠ b := by
  rintro rfl
  exact (Int.not_even_iff_odd.mpr hb) ha

/-- An entry is `0` exactly when the row lies below the column. -/
theorem PositionsOn.false_iff {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ}
    (h : PositionsOn M A B p q) {r : R} {c : C} (hr : r ∈ A) (hc : c ∈ B) : M r c = false ↔ p r < q c := by
  have h1 := h.2.2 r hr c hc
  have h2 := pos_ne (h.1 r) (h.2.1 c)
  constructor
  · intro hm
    have h3 : ¬ q c < p r := fun hlt => by simpa [hm] using h1.2 hlt
    omega
  · intro hlt
    cases hm : M r c
    · rfl
    · have := h1.1 hm
      omega

/-- Positions give nested rows. -/
theorem PositionsOn.nestedOn {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ}
    (h : PositionsOn M A B p q) : NestedOn M A B := by
  intro r hr s hs
  rcases le_total (p r) (p s) with hle | hle
  · left
    intro c hc hm
    have := (h.2.2 r hr c hc).1 hm
    exact (h.2.2 s hs c hc).2 (by omega)
  · right
    intro c hc hm
    have := (h.2.2 s hs c hc).1 hm
    exact (h.2.2 r hr c hc).2 (by omega)

/-- The size of a row inside the block. -/
private def rowSize (M : R → C → Bool) (B : Finset C) (r : R) : ℕ := (B.filter fun c => M r c = true).card

/-- The smallest size of a row of the block containing `c`, or `|B| + 1` if there is none. -/
private noncomputable def colLevel (M : R → C → Bool) (A : Finset R) (B : Finset C) (c : C) : ℕ :=
  sInf {k | (∃ r ∈ A, M r c = true ∧ k = rowSize M B r) ∨ k = B.card + 1}

private theorem rowSize_mono {M : R → C → Bool} {B : Finset C} {r s : R}
    (h : ∀ c ∈ B, M r c = true → M s c = true) : rowSize M B r ≤ rowSize M B s := by
  apply card_le_card
  intro c hc
  simp only [mem_filter] at hc ⊢
  exact ⟨hc.1, h c hc.1 hc.2⟩

/-- In a chain, a row that is no larger than another row is contained in it. -/
private theorem subset_of_rowSize_le {M : R → C → Bool} {A : Finset R} {B : Finset C} (h : NestedOn M A B)
    {r s : R} (hr : r ∈ A) (hs : s ∈ A) (hle : rowSize M B r ≤ rowSize M B s) :
    ∀ c ∈ B, M r c = true → M s c = true := by
  rcases h r hr s hs with g | g
  · exact g
  · have hsub : (B.filter fun c => M s c = true) ⊆ B.filter fun c => M r c = true := by
      intro c hc
      simp only [mem_filter] at hc ⊢
      exact ⟨hc.1, g c hc.1 hc.2⟩
    have heq := eq_of_subset_of_card_le hsub hle
    intro c hc hm
    have : c ∈ B.filter fun c => M r c = true := mem_filter.2 ⟨hc, hm⟩
    rw [← heq] at this
    exact (mem_filter.1 this).2

/-- **Lemma 1, block form.** The rows of a block are nested iff positions exist. -/
theorem nestedOn_iff_positions (M : R → C → Bool) (A : Finset R) (B : Finset C) :
    NestedOn M A B ↔ ∃ p q, PositionsOn M A B p q := by
  classical
  constructor
  · intro h
    refine ⟨fun r => 2 * (rowSize M B r : ℤ), fun c => 2 * (colLevel M A B c : ℤ) - 1,
      fun r => ⟨(rowSize M B r : ℤ), by ring⟩, fun c => ⟨(colLevel M A B c : ℤ) - 1, by ring⟩, ?_⟩
    intro r hr c hc
    have hne : {k | (∃ r ∈ A, M r c = true ∧ k = rowSize M B r) ∨ k = B.card + 1}.Nonempty :=
      ⟨B.card + 1, Or.inr rfl⟩
    have hmem := Nat.sInf_mem hne
    change colLevel M A B c ∈ _ at hmem
    constructor
    · intro hm
      have hle : colLevel M A B c ≤ rowSize M B r := Nat.sInf_le (Or.inl ⟨r, hr, hm, rfl⟩)
      have hpos : 0 < rowSize M B r := card_pos.2 ⟨c, mem_filter.2 ⟨hc, hm⟩⟩
      simp only
      omega
    · intro hlt
      simp only at hlt
      have hlt' : colLevel M A B c ≤ rowSize M B r := by omega
      rcases hmem with ⟨s, hs, hsc, hk⟩ | hk
      · rw [hk] at hlt'
        exact subset_of_rowSize_le h hs hr hlt' c hc hsc
      · have : rowSize M B r ≤ B.card := card_filter_le _ _
        omega
  · rintro ⟨p, q, hpq⟩
    exact hpq.nestedOn

theorem nested_iff_nestedOn_univ [Fintype R] [Fintype C] (M : R → C → Bool) :
    Nested M ↔ NestedOn M univ univ := by
  constructor
  · intro h r _ s _
    exact (h r s).imp (fun g c _ => g c) (fun g c _ => g c)
  · intro h r s
    exact (h r (mem_univ r) s (mem_univ s)).imp (fun g c => g c (mem_univ c)) (fun g c => g c (mem_univ c))

/-- **Lemma 1.** A finite matrix is nested iff there are positions, even on rows and odd on columns, with
`M[r, c] = 1 ⇔ p(r) > q(c)`. -/
theorem nested_iff_positions [Fintype R] [Fintype C] (M : R → C → Bool) :
    Nested M ↔ ∃ (p : R → ℤ) (q : C → ℤ),
      (∀ r, Even (p r)) ∧ (∀ c, Odd (q c)) ∧ ∀ r c, (M r c = true ↔ q c < p r) := by
  rw [nested_iff_nestedOn_univ, nestedOn_iff_positions]
  simp only [PositionsOn, mem_univ, true_implies]

/-- Transposed positions: the columns of a nested block are nested too. -/
theorem PositionsOn.transpose {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ}
    (h : PositionsOn M A B p q) :
    PositionsOn (fun c r => M r c) B A (fun c => 1 - q c) (fun r => 1 - p r) := by
  refine ⟨fun c => ?_, fun r => ?_, fun c hc r hr => ?_⟩
  · obtain ⟨k, hk⟩ := h.2.1 c
    exact ⟨-k, by show 1 - q c = -k + -k; omega⟩
  · obtain ⟨k, hk⟩ := h.1 r
    exact ⟨-k, by show 1 - p r = 2 * -k + 1; omega⟩
  · have := h.2.2 r hr c hc
    simp only [this]
    omega

/-- Complemented positions: the complement of a nested block is nested. -/
theorem PositionsOn.complement {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ}
    (h : PositionsOn M A B p q) :
    PositionsOn (fun r c => !M r c) A B (fun r => - p r) (fun c => - q c) := by
  refine ⟨fun r => (h.1 r).neg, fun c => (h.2.1 c).neg, fun r hr c hc => ?_⟩
  have h1 := h.false_iff hr hc
  simp only [Bool.not_eq_true', h1]
  omega

theorem NestedOn.transpose {M : R → C → Bool} {A : Finset R} {B : Finset C} (h : NestedOn M A B) :
    NestedOn (fun c r => M r c) B A := by
  obtain ⟨p, q, hpq⟩ := (nestedOn_iff_positions M A B).1 h
  exact hpq.transpose.nestedOn

theorem NestedOn.complement {M : R → C → Bool} {A : Finset R} {B : Finset C} (h : NestedOn M A B) :
    NestedOn (fun r c => !M r c) A B := by
  obtain ⟨p, q, hpq⟩ := (nestedOn_iff_positions M A B).1 h
  exact hpq.complement.nestedOn

end GraphClasses
