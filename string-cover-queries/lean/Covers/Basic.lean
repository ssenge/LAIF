import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Occurrences, borders, covers

Section "Setting" and the first Fact of `README.md`. Strings are `List α`. Positions are natural numbers and indexing is
`S[i]?`, so an out-of-range position gives `none`.

The notes say that a cover is a border. That needs `S ≠ []`: every string covers the empty string vacuously
(`covers_nil`), and only `[]` is a border of it. See `Covers.isBorder` and `not_isBorder_of_covers_nil`.
-/

namespace Strings

variable {α : Type*}

/-- `C` occurs in `S` starting at position `t`. -/
def OccursAt (C S : List α) (t : ℕ) : Prop :=
  t + C.length ≤ S.length ∧ ∀ i, i < C.length → S[t + i]? = C[i]?

/-- `C` is both a prefix and a suffix of `S`. -/
def IsBorder (C S : List α) : Prop := C <+: S ∧ C <:+ S

/-- `C` covers `S`: every position of `S` lies in an occurrence of `C`. -/
def Covers (C S : List α) : Prop :=
  ∀ p, p < S.length → ∃ t, OccursAt C S t ∧ t ≤ p ∧ p < t + C.length

/-- The occurrence predicate is the usual one, `C` is a prefix of the suffix of `S` from `t`. The bound on `t` only
matters for `C = []`. -/
theorem occursAt_iff_isPrefix_drop {C S : List α} {t : ℕ} (ht : t ≤ S.length) :
    OccursAt C S t ↔ C <+: S.drop t := by
  rw [List.prefix_iff_getElem?]
  constructor
  · rintro ⟨_, h⟩ i hi
    rw [List.getElem?_drop, h i hi]
    exact List.getElem?_eq_getElem hi
  · intro h
    have hle : C.length ≤ (S.drop t).length := by
      by_contra hlt
      have hlt' : (S.drop t).length < C.length := by omega
      have := h _ hlt'
      rw [List.getElem?_eq_none (by omega)] at this
      simp at this
    refine ⟨by simp at hle; omega, fun i hi => ?_⟩
    have := h i hi
    rw [List.getElem?_drop] at this
    rw [this]
    exact (List.getElem?_eq_getElem hi).symm

theorem OccursAt.getElem? {C S : List α} {t : ℕ} (h : OccursAt C S t) {i : ℕ} (hi : i < C.length) :
    S[t + i]? = C[i]? := h.2 i hi

theorem occursAt_zero_iff {C S : List α} : OccursAt C S 0 ↔ C <+: S := by
  rw [occursAt_iff_isPrefix_drop (Nat.zero_le _)]; simp

theorem occursAt_sub_iff {C S : List α} (h : C.length ≤ S.length) :
    OccursAt C S (S.length - C.length) ↔ C <:+ S := by
  rw [occursAt_iff_isPrefix_drop (Nat.sub_le _ _)]
  constructor
  · intro hp
    rw [List.suffix_iff_eq_drop]
    exact hp.eq_of_length (by simp; omega)
  · intro hs
    rw [List.suffix_iff_eq_drop] at hs
    rw [← hs]

theorem IsBorder.length_le {C S : List α} (h : IsBorder C S) : C.length ≤ S.length :=
  h.1.length_le

theorem IsBorder.occursAt_zero {C S : List α} (h : IsBorder C S) : OccursAt C S 0 :=
  occursAt_zero_iff.2 h.1

theorem IsBorder.occursAt_end {C S : List α} (h : IsBorder C S) :
    OccursAt C S (S.length - C.length) :=
  (occursAt_sub_iff h.length_le).2 h.2

theorem isBorder_of_occursAt {C S : List α} (h0 : OccursAt C S 0)
    (h1 : OccursAt C S (S.length - C.length)) : IsBorder C S := by
  refine ⟨occursAt_zero_iff.1 h0, (occursAt_sub_iff ?_).1 h1⟩
  simpa using h0.1

/-- Two borders of the same length are equal, so a border can be identified with its length. -/
theorem IsBorder.eq_of_length_eq {u v S : List α} (hu : IsBorder u S) (hv : IsBorder v S)
    (h : u.length = v.length) : u = v :=
  (List.prefix_of_prefix_length_le hu.1 hv.1 h.le).eq_of_length h

/-- Every string covers `[]`, vacuously. -/
theorem covers_nil (C : List α) : Covers C [] := fun p hp => by simp at hp

/-- So "a cover is a border" fails for `S = []` as soon as `C ≠ []`. -/
theorem not_isBorder_of_covers_nil {C : List α} (hC : C ≠ []) : ¬ IsBorder C [] := by
  rintro ⟨h, _⟩
  exact hC (List.prefix_nil.1 h)

/-- **A cover of a nonempty string is a border.** -/
theorem Covers.isBorder {C S : List α} (hS : S ≠ []) (h : Covers C S) : IsBorder C S := by
  have hn : 0 < S.length := List.length_pos_iff.2 hS
  obtain ⟨t, ht, ht0, hlt⟩ := h 0 hn
  obtain rfl : t = 0 := by omega
  obtain ⟨t', ht', ht0', hlt'⟩ := h (S.length - 1) (by omega)
  have h' := ht'.1
  have hend : t' = S.length - C.length := by omega
  exact isBorder_of_occursAt ht (hend ▸ ht')

/-- A cover of a nonempty string is nonempty. -/
theorem Covers.ne_nil {C S : List α} (hS : S ≠ []) (h : Covers C S) : C ≠ [] := by
  rintro rfl
  have hn : 0 < S.length := List.length_pos_iff.2 hS
  obtain ⟨t, _, h1, h2⟩ := h 0 hn
  simp at h2
  omega

theorem occursAt_self (S : List α) : OccursAt S S 0 :=
  ⟨by simp, fun i _ => by simp⟩

/-- **`S` covers itself.** -/
theorem covers_self (S : List α) : Covers S S :=
  fun p hp => ⟨0, occursAt_self S, Nat.zero_le _, by omega⟩

/-- `S` is a border of itself. -/
theorem isBorder_self (S : List α) : IsBorder S S :=
  ⟨List.prefix_rfl, List.suffix_rfl⟩

/-- An occurrence of `A` in `B` and an occurrence of `B` in `S` compose. -/
theorem OccursAt.trans {A B S : List α} {t₁ t₂ : ℕ} (h₁ : OccursAt A B t₁) (h₂ : OccursAt B S t₂) :
    OccursAt A S (t₂ + t₁) := by
  refine ⟨by have := h₁.1; have := h₂.1; omega, fun i hi => ?_⟩
  have hb := h₁.1
  rw [add_assoc, h₂.2 (t₁ + i) (by omega), h₁.2 i hi]

/-- **Transitivity of covers.** -/
theorem Covers.trans {A B S : List α} (hAB : Covers A B) (hBS : Covers B S) : Covers A S := by
  intro p hp
  obtain ⟨t₂, occ₂, h₂, h₂'⟩ := hBS p hp
  obtain ⟨t₁, occ₁, h₁, h₁'⟩ := hAB (p - t₂) (by omega)
  exact ⟨t₂ + t₁, occ₁.trans occ₂, by omega, by omega⟩

/-- **Lemma 1.** If `u, v` are borders of `S` with `|u| ≤ |v| < 2|u|`, then `u` covers `v`. -/
theorem lemma1 {u v S : List α} (hu : IsBorder u S) (hv : IsBorder v S)
    (h₁ : u.length ≤ v.length) (h₂ : v.length < 2 * u.length) : Covers u v := by
  have hb : IsBorder u v :=
    ⟨List.prefix_of_prefix_length_le hu.1 hv.1 h₁, List.suffix_of_suffix_length_le hu.2 hv.2 h₁⟩
  intro p hp
  by_cases hpu : p < u.length
  · exact ⟨0, hb.occursAt_zero, Nat.zero_le _, by omega⟩
  · exact ⟨v.length - u.length, hb.occursAt_end, by omega, by omega⟩

end Strings
