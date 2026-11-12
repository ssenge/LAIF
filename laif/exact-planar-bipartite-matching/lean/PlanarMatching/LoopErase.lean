import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic

/-!
# Chronological loop erasure

`notes/MATCHING.md`, Section 3. `loopErase` keeps a vertex and jumps to its last visit. Its output has
no repeated vertex, keeps both ends, and every consecutive pair is a consecutive pair of the walk, so a
directed walk becomes a simple directed path. `eraseAt H` jumps only at members of `H`; when only members
of `H` repeat (Lemma C of the note) it computes the same path, so reports from `H` are enough.
-/

namespace PlanarMatching

variable {α : Type*} [DecidableEq α]

/-- The part of `l` after the last occurrence of `x`, or all of `l` if `x` does not occur. -/
def after (x : α) : List α → List α
  | [] => []
  | a :: l => if x ∈ l then after x l else if a = x then l else a :: l

theorem after_suffix (x : α) : ∀ l : List α, after x l <:+ l
  | [] => by simp [after]
  | a :: l => by
    rw [after]
    split_ifs
    · exact (after_suffix x l).trans (List.suffix_cons a l)
    · exact List.suffix_cons a l
    · exact List.suffix_refl _

theorem not_mem_after (x : α) : ∀ l : List α, x ∉ after x l
  | [] => by simp [after]
  | a :: l => by
    rw [after]
    split_ifs with h1 h2
    · exact not_mem_after x l
    · exact h1
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact h2 h.symm
      · exact h1 h

theorem after_length_le (x : α) (l : List α) : (after x l).length ≤ l.length :=
  (after_suffix x l).length_le

theorem after_of_not_mem {x : α} : ∀ {l : List α}, x ∉ l → after x l = l
  | [], _ => by simp [after]
  | a :: l, h => by
    have h1 : x ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    have h2 : a ≠ x := fun e => h (e ▸ List.mem_cons_self)
    simp [after, h1, h2]

/-- A visit of `x` is followed by the part after its last visit. -/
theorem cons_after_suffix_of_mem (x : α) : ∀ {l : List α}, x ∈ l → (x :: after x l) <:+ l
  | [], h => by simp at h
  | a :: l, h => by
    by_cases h1 : x ∈ l
    · simp only [after, h1, ↓reduceIte]
      exact (cons_after_suffix_of_mem x h1).trans (List.suffix_cons a l)
    · have h2 : a = x := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h h1
      simp only [after, h1, h2, ↓reduceIte]
      exact List.suffix_refl _

/-- `x :: after x xs` is a suffix of `x :: xs`: the jump lands just after a visit of `x`. -/
theorem cons_after_suffix (x : α) (xs : List α) : (x :: after x xs) <:+ (x :: xs) := by
  by_cases hx : x ∈ xs
  · exact (cons_after_suffix_of_mem x hx).trans (List.suffix_cons x xs)
  · rw [after_of_not_mem hx]

/-- Chronological loop erasure. -/
def loopErase : List α → List α
  | [] => []
  | x :: xs => x :: loopErase (after x xs)
termination_by l => l.length
decreasing_by
  have := after_length_le x xs
  simp only [List.length_cons]
  omega

theorem mem_of_mem_loopErase : ∀ {l : List α} {a : α}, a ∈ loopErase l → a ∈ l
  | [], a, h => by simp [loopErase] at h
  | x :: xs, a, h => by
    rw [loopErase] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have hlen := after_length_le x xs
      have := mem_of_mem_loopErase h
      exact List.mem_cons_of_mem _ ((after_suffix x xs).subset this)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  omega

/-- The output is simple. -/
theorem nodup_loopErase : ∀ l : List α, (loopErase l).Nodup
  | [] => by simp [loopErase]
  | x :: xs => by
    rw [loopErase, List.nodup_cons]
    have hlen := after_length_le x xs
    exact ⟨fun h => not_mem_after x xs (mem_of_mem_loopErase h), nodup_loopErase _⟩
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  omega

/-- The output starts where the walk starts. -/
theorem head?_loopErase : ∀ l : List α, (loopErase l).head? = l.head?
  | [] => by simp [loopErase]
  | x :: xs => by rw [loopErase]; simp

/-- The output ends where the walk ends. -/
theorem getLast?_loopErase : ∀ l : List α, (loopErase l).getLast? = l.getLast?
  | [] => by simp [loopErase]
  | x :: xs => by
    rw [loopErase]
    have hlen := after_length_le x xs
    have ih := getLast?_loopErase (after x xs)
    obtain ⟨t, ht⟩ := cons_after_suffix x xs
    have e : (x :: xs).getLast? = (x :: after x xs).getLast? := by
      rw [← ht]; simp [List.getLast?_append, List.getLast?_cons]
    rw [e]
    cases ha : after x xs with
    | nil => simp [loopErase]
    | cons a b =>
      rw [ha] at ih
      rw [loopErase] at ih ⊢
      rw [List.getLast?_cons_cons, List.getLast?_cons_cons, ih]
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  omega

/-- Every consecutive pair of the output is related whenever the walk is a chain. -/
theorem isChain_loopErase {R : α → α → Prop} : ∀ {l : List α}, l.IsChain R → (loopErase l).IsChain R
  | [], _ => by simp [loopErase]
  | x :: xs, h => by
    rw [loopErase]
    have hlen := after_length_le x xs
    have hc : (x :: after x xs).IsChain R := h.suffix (cons_after_suffix x xs)
    have hrest : (after x xs).IsChain R := hc.tail
    have ih := isChain_loopErase hrest
    cases ha : after x xs with
    | nil => simp [loopErase]
    | cons a b =>
      rw [ha] at hc ih
      rw [loopErase] at ih ⊢
      rw [List.isChain_cons_cons]
      exact ⟨(List.isChain_cons_cons.mp hc).1, ih⟩
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  omega

/-- The erasure that jumps only at members of `H`. -/
def eraseAt (H : Finset α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ H then x :: eraseAt H (after x xs) else x :: eraseAt H xs
termination_by l => l.length
decreasing_by
  · have := after_length_le x xs
    simp only [List.length_cons]
    omega
  · simp only [List.length_cons]
    omega

/-- Lemma C of the note in use: when only members of `H` repeat, reports from `H` determine the erasure. -/
theorem eraseAt_eq_loopErase (H : Finset α) :
    ∀ l : List α, (∀ a, 1 < l.count a → a ∈ H) → eraseAt H l = loopErase l
  | [], _ => by simp [eraseAt, loopErase]
  | x :: xs, h => by
    rw [eraseAt, loopErase]
    have hlen := after_length_le x xs
    have down : ∀ {t : List α}, t <:+ xs → ∀ a, 1 < t.count a → a ∈ H := by
      intro t ht a hc
      apply h
      have h1 : t.count a ≤ xs.count a := (ht.sublist.count_le a)
      have h2 : xs.count a ≤ (x :: xs).count a := (List.sublist_cons_self x xs).count_le a
      omega
    by_cases hx : x ∈ H
    · simp only [hx, ↓reduceIte]
      rw [eraseAt_eq_loopErase H (after x xs) (down (after_suffix x xs))]
    · simp only [hx, ↓reduceIte]
      have hnot : x ∉ xs := by
        intro hm
        apply hx
        apply h
        have : 0 < xs.count x := List.count_pos_iff.mpr hm
        simp only [List.count_cons_self]
        omega
      rw [after_of_not_mem hnot, eraseAt_eq_loopErase H xs (down (List.suffix_refl _))]
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals omega

end PlanarMatching
