import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith

/-!
# Lemma 4: the cap

A bin `S` is enumerated by `Fin |S|`, and the window is its first `min (T, |S|)` elements. If `T ≥ 1`
and at most `T/2` elements of the bin lie outside a nonempty class, written `2 |S \ C| ≤ T` so that
`T` stays a natural number, the window contains an element of the class.

If `|S| ≤ T` the window is the whole bin. Otherwise it has `T` elements, at most `T/2` of them outside
the class. There is no probability here, and the enumeration is arbitrary. The condition `T ≥ 1` is
needed, since for `T = 0` the window is empty.
-/

open Finset

namespace SubsetBalancing

variable {α : Type*}

/-- An enumeration of a bin: the `I`-th element of the bin in some fixed order. -/
abbrev Enum (S : Finset α) := Fin #S ≃ S

/-- The indices below `T`. -/
def firstIndices (T N : ℕ) : Finset (Fin N) := univ.filter fun i => i.val < T

/-- There are `min (T, N)` indices below `T`. -/
theorem card_firstIndices (T N : ℕ) : #(firstIndices T N) = min T N := by
  have h : (firstIndices T N).image Fin.val = range (min T N) := by
    ext k
    simp only [firstIndices, mem_image, mem_filter, mem_univ, true_and, mem_range, lt_min_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨k, h2⟩, h1, rfl⟩
  rw [← card_range (min T N), ← h, card_image_of_injective _ Fin.val_injective]

/-- The cap on indices: a nonempty class of indices with at most `T/2` indices outside it, for
`T ≥ 1`, has an index below `T`. -/
theorem exists_mem_lt {T N : ℕ} (hT : 1 ≤ T) {C : Finset (Fin N)} (hC : C.Nonempty)
    (hout : 2 * #Cᶜ ≤ T) : ∃ i ∈ C, i.val < T := by
  by_contra hcon
  have hall : ∀ i ∈ C, T ≤ i.val := fun i hi => not_lt.mp fun h => hcon ⟨i, hi, h⟩
  obtain ⟨c, hc⟩ := hC
  have hTN : T ≤ N := (hall c hc).trans c.isLt.le
  have hsub : firstIndices T N ⊆ Cᶜ := by
    intro i hi
    rw [mem_compl]
    intro hiC
    have h1 := hall i hiC
    have h2 : i.val < T := by simpa [firstIndices] using hi
    omega
  have h3 := card_le_card hsub
  rw [card_firstIndices, min_eq_left hTN] at h3
  omega

/-- The window of a bin: its first `min (T, |S|)` elements in the enumeration `e`. -/
def firstWindow {S : Finset α} (e : Enum S) (T : ℕ) : Finset α :=
  (firstIndices T #S).map ⟨fun i => (e i : α), fun _ _ h => e.injective (Subtype.ext h)⟩

theorem card_firstWindow {S : Finset α} (e : Enum S) (T : ℕ) : #(firstWindow e T) = min T #S := by
  rw [firstWindow, card_map, card_firstIndices]

theorem firstWindow_subset {S : Finset α} (e : Enum S) (T : ℕ) : firstWindow e T ⊆ S := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := mem_map.mp hx
  exact (e i).2

/-- **Lemma 4.** Let `e` enumerate a bin `S`, and let `T ≥ 1`. If the class of elements of `S` with
property `p` is nonempty, and at most `T/2` elements of `S` lie outside it, then the first
`min (T, |S|)` elements of the bin contain an element of the class. -/
theorem cap_lemma {S : Finset α} (e : Enum S) {T : ℕ} (hT : 1 ≤ T) (p : α → Prop) [DecidablePred p]
    (hne : ∃ x ∈ S, p x) (hout : 2 * #{x ∈ S | ¬ p x} ≤ T) :
    ∃ x ∈ firstWindow e T, p x := by
  obtain ⟨x, hx, hpx⟩ := hne
  set C : Finset (Fin #S) := univ.filter fun i => p (e i : α) with hC
  have hCne : C.Nonempty :=
    ⟨e.symm ⟨x, hx⟩, by simp [hC, hpx]⟩
  have hcompl : #Cᶜ ≤ #{x ∈ S | ¬ p x} := by
    refine card_le_card_of_injOn (fun i => (e i : α)) ?_ ?_
    · intro i hi
      have hi' : ¬ p (e i : α) := by simpa [hC] using hi
      exact mem_filter.mpr ⟨(e i).2, hi'⟩
    · intro i _ j _ h
      exact e.injective (Subtype.ext h)
  obtain ⟨i, hiC, hiT⟩ := exists_mem_lt hT hCne (by omega)
  refine ⟨(e i : α), mem_map.mpr ⟨i, ?_, rfl⟩, ?_⟩
  · simpa [firstIndices] using hiT
  · simpa [hC] using hiC

end SubsetBalancing
