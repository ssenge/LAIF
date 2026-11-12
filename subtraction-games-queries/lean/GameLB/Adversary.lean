import Mathlib

/-!
# The adversary relation for a parity of ORs

Inputs with at most one one per row are maps `x : Fin k → Option (Fin s)`: row `t` has its one at `i` iff
`x t = some i`. The bit `(t, i)` of `x` is `x t = some i`, and the weight of `x` is its number of nonempty rows.
An input `y` is related to `x` if it arises by putting a one into an empty row of `x` (`add`).

* `weight_add`: this raises the weight by one, so the parity of the number of nonempty rows changes.
* `card_adds`: `x` has `(k - weight x) * s` related inputs.
* `card_removes`: an input `y` arises from `weight y` inputs in this way.
* `bit_add`: the related input `add x t i` differs from `x` exactly in the bit `(t, i)`. Together with `add_inj`,
  for each bit at most one related input of `x` differs from `x` there, and by `add_remove` and `remove_inj` the
  same holds for `y`.
-/

namespace GameLB

open Finset

variable {k s : ℕ}

/-- The number of nonempty rows. -/
def weight (x : Fin k → Option (Fin s)) : ℕ := (univ.filter (fun t => x t ≠ none)).card

/-- Put a one at `i` into row `t`. -/
def add (x : Fin k → Option (Fin s)) (t : Fin k) (i : Fin s) : Fin k → Option (Fin s) :=
  Function.update x t (some i)

/-- Empty row `t`. -/
def remove (y : Fin k → Option (Fin s)) (t : Fin k) : Fin k → Option (Fin s) :=
  Function.update y t none

theorem weight_add {x : Fin k → Option (Fin s)} {t : Fin k} (ht : x t = none) (i : Fin s) :
    weight (add x t i) = weight x + 1 := by
  unfold weight add
  have e : univ.filter (fun t' => Function.update x t (some i) t' ≠ none) =
      insert t (univ.filter (fun t' => x t' ≠ none)) := by
    ext t'
    by_cases h : t' = t
    · subst h; simp
    · simp [Function.update_apply, h]
  rw [e, card_insert_of_notMem (by simp [ht])]

/-- The bits of `add x t i` and `x` differ exactly at `(t, i)`. -/
theorem bit_add {x : Fin k → Option (Fin s)} {t : Fin k} (ht : x t = none) (i : Fin s) (t' : Fin k)
    (i' : Fin s) : (add x t i t' = some i' ↔ x t' = some i') ↔ ¬ (t' = t ∧ i' = i) := by
  by_cases h : t' = t
  · subst h
    simp [add, ht, eq_comm]
  · simp [add, Function.update_apply, h]

theorem add_inj {x : Fin k → Option (Fin s)} {t t' : Fin k} {i i' : Fin s} (ht : x t = none)
    (h : add x t i = add x t' i') : t = t' ∧ i = i' := by
  have h1 := congrFun h t
  by_cases e : t = t'
  · subst e
    simp [add] at h1
    exact ⟨rfl, h1⟩
  · simp [add, Function.update_apply, e, ht] at h1

/-- The inputs related to `x` number `(k - weight x) * s`. -/
theorem card_adds (x : Fin k → Option (Fin s)) :
    (((univ.filter (fun t => x t = none)) ×ˢ (univ : Finset (Fin s))).image
      (fun p => add x p.1 p.2)).card = (k - weight x) * s := by
  rw [card_image_of_injOn]
  · rw [card_product, card_univ, Fintype.card_fin]
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (fun t => x t = none)
    simp only [card_univ, Fintype.card_fin] at h
    unfold weight
    simp only [ne_eq] at h ⊢
    congr 1
    omega
  · rintro ⟨t, i⟩ hp ⟨t', i'⟩ - h
    simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_setOf_eq,
      coe_univ, Set.mem_univ, and_true] at hp
    obtain ⟨e1, e2⟩ := add_inj hp h
    simp only at e1 e2
    rw [e1, e2]

theorem add_remove {y : Fin k → Option (Fin s)} {t : Fin k} {i : Fin s} (ht : y t = some i) :
    remove y t t = none ∧ add (remove y t) t i = y := by
  constructor
  · simp [remove]
  · ext1 t'
    by_cases h : t' = t
    · subst h; simp [add, ht]
    · simp [add, remove, Function.update_apply, h]

theorem remove_inj {y : Fin k → Option (Fin s)} {t t' : Fin k} (ht : y t ≠ none)
    (h : remove y t = remove y t') : t = t' := by
  by_contra e
  have h1 := congrFun h t
  simp [remove, Function.update_apply, e] at h1
  exact ht h1.symm

/-- The inputs from which `y` arises by `add` number `weight y`. -/
theorem card_removes (y : Fin k → Option (Fin s)) :
    ((univ.filter (fun t => y t ≠ none)).image (fun t => remove y t)).card = weight y := by
  rw [card_image_of_injOn]
  · rfl
  · intro t ht t' _ h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht
    exact remove_inj ht h

end GameLB
