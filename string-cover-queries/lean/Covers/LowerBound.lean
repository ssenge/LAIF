import Covers.Range

/-!
# The lower-bound family

`aⁿ` has shortest cover `a`. With one `b ≠ a` at any position `i`, the only cover is the whole string, and the borders
are `a^j` for `j ≤ min(i, n - 1 - i)` and `S` itself. So for `n ≥ 2` the shortest cover has length 1 iff `S = aⁿ`. This is
the form of the revised notes. It implies the earlier form, length `> n/3` for a middle position.
-/

namespace Strings

variable {α : Type*}

/-- `aⁿ` with position `i` set to `b`. -/
def oneB (n i : ℕ) (a b : α) : List α := (List.replicate n a).set i b

@[simp] theorem length_oneB (n i : ℕ) (a b : α) : (oneB n i a b).length = n := by simp [oneB]

theorem oneB_getElem?_self {n i : ℕ} {a b : α} (hi : i < n) : (oneB n i a b)[i]? = some b := by
  simp [oneB, hi]

theorem oneB_getElem?_of_ne {n i j : ℕ} {a b : α} (hj : j < n) (h : j ≠ i) : (oneB n i a b)[j]? = some a := by
  simp [oneB, hj, Ne.symm h]

theorem oneB_getElem?_eq_b {n i j : ℕ} {a b : α} (hab : a ≠ b) (hj : j < n)
    (h : (oneB n i a b)[j]? = some b) : j = i := by
  by_contra hne
  rw [oneB_getElem?_of_ne hj hne] at h
  exact hab (Option.some.inj h)

/-- `[a]` covers `aⁿ`. -/
theorem covers_replicate (n : ℕ) (a : α) : Covers [a] (List.replicate n a) := by
  intro p hp
  rw [List.length_replicate] at hp
  refine ⟨p, ⟨by simp; omega, fun i hi => ?_⟩, le_rfl, by simp⟩
  simp at hi
  subst hi
  simp [hp]

/-- **Lower bound, first string.** For `n ≥ 1`, `aⁿ` has shortest cover `a`, of length 1. -/
theorem replicate_shortestCover {n : ℕ} (hn : 1 ≤ n) (a : α) : IsShortestCover [a] (List.replicate n a) := by
  refine ⟨covers_replicate n a, fun D hD => ?_⟩
  have hS : List.replicate n a ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have := hD.ne_nil hS
  have hpos := List.length_pos_iff.2 this
  have h1 : [a].length = 1 := rfl
  omega

/-- **Lower bound, second string.** With one `b ≠ a`, the only cover of `aⁿ` is the whole string. -/
theorem oneB_cover_eq {n i : ℕ} {a b : α} {C : List α} (hab : a ≠ b) (hi : i < n)
    (hC : Covers C (oneB n i a b)) : C = oneB n i a b := by
  have hS : oneB n i a b ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have hb := hC.isBorder hS
  obtain ⟨t, ht, h1, h2⟩ := hC i (by simpa using hi)
  have hle := hb.length_le
  rw [length_oneB] at hle
  have hlen : (oneB n i a b).length = n := length_oneB _ _ _ _
  have hat := ht.2 (i - t) (by omega)
  have e1 : t + (i - t) = i := by omega
  rw [e1, oneB_getElem?_self hi] at hat
  -- the prefix occurrence forces `t = 0`
  have h0 := hb.occursAt_zero.2 (i - t) (by omega)
  rw [Nat.zero_add, ← hat] at h0
  have ht0 := oneB_getElem?_eq_b hab (by omega) h0
  -- the suffix occurrence forces `|C| = n`
  have hend := hb.occursAt_end.2 (i - t) (by omega)
  rw [← hat, hlen] at hend
  have hne := oneB_getElem?_eq_b hab (by omega) hend
  have hlenC : C.length = n := by omega
  exact hb.1.eq_of_length (by rw [hlenC, hlen])

/-- **Lower bound, second string.** Its shortest cover has length exactly `n`, for any position of the `b`. -/
theorem oneB_shortestCover {n i : ℕ} {a b : α} (hab : a ≠ b) (hi : i < n) :
    IsShortestCover (oneB n i a b) (oneB n i a b) :=
  ⟨covers_self _, fun _ hD => by rw [oneB_cover_eq hab hi hD]⟩

/-- **The earlier form of the fact.** The shortest cover of `aⁿ` with one `b` has length `> n/3`, at a middle position
or at any other. -/
theorem oneB_shortest_length_gt_third {n i : ℕ} {a b : α} {C : List α} (hab : a ≠ b) (hi : i < n)
    (hC : IsShortestCover C (oneB n i a b)) : n < 3 * C.length := by
  have := oneB_cover_eq hab hi hC.1
  have hlen : C.length = n := by rw [this, length_oneB]
  omega

/-- **Revised notes.** The shortest cover has length 1 on `aⁿ` and not on `aⁿ` with one `b`, for `n ≥ 2`. -/
theorem oneB_shortest_length_ne_one {n i : ℕ} {a b : α} {D : List α} (hab : a ≠ b) (hi : i < n) (hn : 2 ≤ n)
    (hD : IsShortestCover D (oneB n i a b)) : D.length ≠ 1 := by
  rw [oneB_cover_eq hab hi hD.1, length_oneB]
  omega

/-- **The two strings are told apart** by the length of the shortest cover, for `n ≥ 2`. -/
theorem shortest_lengths_differ {n i : ℕ} {a b : α} {C D : List α} (hab : a ≠ b) (hi : i < n) (hn : 2 ≤ n)
    (hC : IsShortestCover C (List.replicate n a)) (hD : IsShortestCover D (oneB n i a b)) :
    C.length = 1 ∧ D.length = n := by
  have h1 := hC.2 _ (replicate_shortestCover (n := n) (by omega) a).1
  have h2 := (replicate_shortestCover (n := n) (by omega) a).2 _ hC.1
  simp at h1 h2
  refine ⟨by omega, ?_⟩
  rw [oneB_cover_eq hab hi hD.1, length_oneB]

/-- **Exact borders of the family.** The length-`j` prefix of `aⁿ` with one `b` at `i` is a border iff
`j ≤ min(i, n - i - 1)` or `j = n`. -/
theorem oneB_isBorder_take_iff {n i j : ℕ} {a b : α} (hab : a ≠ b) (hi : i < n) (hj : j ≤ n) :
    IsBorder ((oneB n i a b).take j) (oneB n i a b) ↔ (j ≤ i ∧ j ≤ n - i - 1) ∨ j = n := by
  set S := oneB n i a b with hS
  have hlen : S.length = n := length_oneB _ _ _ _
  have hlt : ((S.take j).length) = j := by rw [List.length_take, hlen]; omega
  have hocc0 : OccursAt (S.take j) S 0 := occursAt_zero_iff.2 (List.take_prefix _ _)
  constructor
  · intro hb
    by_cases hjn : j = n
    · exact Or.inr hjn
    · left
      have hend := hb.occursAt_end
      rw [hlt, hlen] at hend
      constructor
      · by_contra hgt
        have h1 := hend.2 i (by omega)
        rw [List.getElem?_take_of_lt (by omega), hS, oneB_getElem?_self hi] at h1
        have := oneB_getElem?_eq_b hab (by omega) h1
        omega
      · by_contra hgt
        have h1 := hend.2 (i - (n - j)) (by omega)
        have e : n - j + (i - (n - j)) = i := by omega
        rw [e, List.getElem?_take_of_lt (by omega), hS, oneB_getElem?_self hi] at h1
        have := oneB_getElem?_eq_b hab (by omega) h1.symm
        omega
  · rintro (⟨h1, h2⟩ | hjn)
    · refine isBorder_of_occursAt hocc0 ?_
      rw [hlt, hlen]
      refine ⟨by rw [hlt]; omega, fun k hk => ?_⟩
      rw [hlt] at hk
      rw [List.getElem?_take_of_lt hk, hS, oneB_getElem?_of_ne (by omega) (by omega),
        oneB_getElem?_of_ne (by omega) (by omega)]
    · have : S.take j = S := List.take_of_length_le (by omega)
      rw [this]
      exact isBorder_self S

end Strings
