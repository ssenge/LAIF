import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max

/-!
# LP-type problems: definitions and Facts 1 to 4

The universe of constraints is a `Fintype H`, so `H` of the notes is `Finset.univ`. The value type
only needs a partial order: strict comparisons in the definitions behave as in a linear order
because `f` is monotone. There is no assumption on `f ∅`.
-/

open Finset

namespace LPType

/-- An LP-type problem on the constraints `H` with values in `R`. -/
structure Problem (H R : Type*) [DecidableEq H] [PartialOrder R] where
  /-- The value of a set of constraints. -/
  f : Finset H → R
  /-- Monotonicity. -/
  mono : ∀ {F G : Finset H}, F ⊆ G → f F ≤ f G
  /-- Locality. -/
  locality : ∀ {F G : Finset H} {h : H}, F ⊆ G → f F = f G → f G < f (insert h G) →
    f F < f (insert h F)

variable {H R : Type*} [DecidableEq H] [PartialOrder R] (P : Problem H R)

namespace Problem

/-- `h` violates `S` if adding it raises the value. -/
def Violates (h : H) (S : Finset H) : Prop := P.f S < P.f (insert h S)

/-- `h ∈ S` is extreme in `S` if removing it lowers the value. -/
def Extreme (h : H) (S : Finset H) : Prop := h ∈ S ∧ P.f (S.erase h) < P.f S

/-- `B` is a basis of `S`: a subset of `S` with the value of `S`, minimal with that property. -/
def IsBasis (B S : Finset H) : Prop :=
  B ⊆ S ∧ P.f B = P.f S ∧ ∀ B' : Finset H, B' ⊂ B → P.f B' ≠ P.f B

variable {P}

/-- Elements of `S` never violate `S`. -/
theorem Violates.not_mem {h : H} {S : Finset H} (hv : P.Violates h S) : h ∉ S := by
  intro hS
  rw [Violates, insert_eq_of_mem hS] at hv
  exact lt_irrefl _ hv

/-- A non-violator does not change the value. -/
theorem eq_of_not_violates {h : H} {S : Finset H} (hv : ¬ P.Violates h S) :
    P.f (insert h S) = P.f S :=
  (eq_of_le_of_not_lt (P.mono (subset_insert h S)) hv).symm

/-- Every set has a basis. -/
theorem exists_isBasis (S : Finset H) : ∃ B, P.IsBasis B S := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : ∀ B' : Finset H, B' ⊂ S → P.f B' ≠ P.f S
    · exact ⟨S, Subset.rfl, rfl, hS⟩
    · push Not at hS
      obtain ⟨B', hB', hval⟩ := hS
      obtain ⟨B, hBsub, hBval, hBmin⟩ := ih B' hB'
      exact ⟨B, hBsub.trans hB'.subset, hBval.trans hval, hBmin⟩

/-- A basis of `S` is a basis of any set containing it with the same value. -/
theorem IsBasis.of_value_eq {B S T : Finset H} (hB : P.IsBasis B S) (hST : S ⊆ T)
    (hval : P.f S = P.f T) : P.IsBasis B T :=
  ⟨hB.1.trans hST, hB.2.1.trans hval, hB.2.2⟩

section Dimension

variable [Fintype H]

variable (P) in
open scoped Classical in
/-- The combinatorial dimension: the largest size of a basis of any set. -/
noncomputable def combDim : ℕ :=
  ((univ : Finset (Finset H)).filter fun B => ∃ S, P.IsBasis B S).sup card

/-- Every basis has size at most the combinatorial dimension. -/
theorem IsBasis.card_le {B S : Finset H} (hB : P.IsBasis B S) : #B ≤ P.combDim := by
  classical
  exact Finset.le_sup (f := card) (mem_filter.2 ⟨mem_univ _, S, hB⟩)

/-- The combinatorial dimension is attained. -/
theorem exists_isBasis_card_eq_combDim : ∃ B S : Finset H, P.IsBasis B S ∧ #B = P.combDim := by
  classical
  have hne : ((univ : Finset (Finset H)).filter fun B => ∃ S, P.IsBasis B S).Nonempty := by
    obtain ⟨B, hB⟩ := exists_isBasis (P := P) ∅
    exact ⟨B, mem_filter.2 ⟨mem_univ _, ∅, hB⟩⟩
  obtain ⟨B, hBmem, hBeq⟩ := Finset.exists_mem_eq_sup _ hne card
  obtain ⟨S, hS⟩ := (mem_filter.1 hBmem).2
  exact ⟨B, S, hS, hBeq.symm⟩

/-- An upper bound on all bases bounds the combinatorial dimension. -/
theorem combDim_le {d : ℕ} (h : ∀ B S : Finset H, P.IsBasis B S → #B ≤ d) : P.combDim ≤ d := by
  obtain ⟨B, S, hB, hc⟩ := exists_isBasis_card_eq_combDim (P := P)
  exact hc ▸ h B S hB

end Dimension

/-! ## Fact 1 -/

/-- Every basis of `S` contains every extreme element of `S`. -/
theorem IsBasis.extreme_mem {B S : Finset H} (hB : P.IsBasis B S) {h : H}
    (hh : P.Extreme h S) : h ∈ B := by
  by_contra hnot
  have hsub : B ⊆ S.erase h := fun x hx =>
    mem_erase.2 ⟨fun e => hnot (e ▸ hx), hB.1 hx⟩
  have h1 : P.f S ≤ P.f (S.erase h) := hB.2.1 ▸ P.mono hsub
  exact absurd (lt_of_le_of_lt h1 hh.2) (lt_irrefl _)

open scoped Classical in
/-- The extreme elements of `S`. -/
noncomputable def extremes (P : Problem H R) [Fintype H] (S : Finset H) : Finset H :=
  univ.filter fun h => P.Extreme h S

/-- **Fact 1.** `S` has at most `δ` extreme elements. -/
theorem fact1 [Fintype H] (S : Finset H) : #(P.extremes S) ≤ P.combDim := by
  classical
  obtain ⟨B, hB⟩ := exists_isBasis (P := P) S
  refine (card_le_card fun h hh => ?_).trans hB.card_le
  exact hB.extreme_mem (mem_filter.1 hh).2

/-! ## Fact 2 -/

/-- **Fact 2.** For `h ∉ S`: `h` violates `S` iff `h` is extreme in `S ∪ {h}`. -/
theorem fact2 {h : H} {S : Finset H} (hS : h ∉ S) : P.Violates h S ↔ P.Extreme h (insert h S) := by
  simp [Violates, Extreme, erase_insert hS]

/-! ## Fact 3 -/

/-- By locality, an element not violating `S` does not violate a superset with the same value. -/
theorem not_violates_of_superset {S G : Finset H} {h : H} (hSG : S ⊆ G)
    (hval : P.f S = P.f G) (hv : ¬ P.Violates h S) : ¬ P.Violates h G :=
  fun hG => hv (P.locality hSG hval hG)

/-- **Fact 3.** If no element of `A` violates `S`, then `f (S ∪ A) = f S`. -/
theorem fact3 {S A : Finset H} (hA : ∀ h ∈ A, ¬ P.Violates h S) : P.f (S ∪ A) = P.f S := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A _ ih =>
    have ih' := ih fun h hh => hA h (mem_insert_of_mem hh)
    have ha := hA a (mem_insert_self a A)
    have hnv : ¬ P.Violates a (S ∪ A) :=
      not_violates_of_superset subset_union_left ih'.symm ha
    rw [union_insert, eq_of_not_violates hnv, ih']

/-! ## Fact 4 -/

section Fact4

variable [Fintype H]

/-- **Fact 4, first part.** If `f S < f H` and `B` is a basis of `H`, some element of `B` violates
`S`. -/
theorem fact4 {S B : Finset H} (hS : P.f S < P.f univ) (hB : P.IsBasis B univ) :
    ∃ b ∈ B, P.Violates b S := by
  by_contra hno
  push Not at hno
  have h3 : P.f (S ∪ B) = P.f S := fact3 hno
  have h4 : P.f univ ≤ P.f S := by
    rw [← hB.2.1, ← h3]
    exact P.mono subset_union_right
  exact absurd (lt_of_lt_of_le hS h4) (lt_irrefl _)

/-- **Fact 4, second part.** If nothing violates `S`, then `f S = f H`. -/
theorem fact4_of_no_violator {S : Finset H} (h : ∀ h, ¬ P.Violates h S) : P.f S = P.f univ := by
  have h3 := fact3 (S := S) (A := univ) fun x _ => h x
  rw [union_eq_right.2 (subset_univ S)] at h3
  exact h3.symm

/-- A violator exists exactly when the value is below `f H`. -/
theorem exists_violates_iff {S : Finset H} : (∃ h, P.Violates h S) ↔ P.f S < P.f univ := by
  constructor
  · rintro ⟨h, hv⟩
    exact lt_of_lt_of_le hv (P.mono (subset_univ _))
  · intro hS
    obtain ⟨B, hB⟩ := exists_isBasis (P := P) (univ : Finset H)
    obtain ⟨b, -, hb⟩ := fact4 hS hB
    exact ⟨b, hb⟩

/-- Stopping is correct: if nothing violates `S`, a basis of `S` is a basis of `H`, with value
`f H`. -/
theorem stopping_correct {S B : Finset H} (h : ∀ h, ¬ P.Violates h S) (hB : P.IsBasis B S) :
    P.f B = P.f univ ∧ P.IsBasis B univ :=
  ⟨hB.2.1.trans (fact4_of_no_violator h),
    hB.of_value_eq (subset_univ _) (fact4_of_no_violator h)⟩

end Fact4

end Problem

end LPType
