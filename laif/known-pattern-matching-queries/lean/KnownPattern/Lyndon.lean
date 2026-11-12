import Mathlib.Data.List.Rotate

/-!
# A prefix of a Lyndon word whose minimal rotation is not `x' x`

Words are lists of natural numbers in lexicographic order, with the letters `a = 0`, `b = 1` and `c = 2`. A word is
Lyndon if it is nonempty and smaller than each of its proper rotations.

* `rotation_example`: `x = ababb` is Lyndon, `w = x x'` with `x' = aba` is a proper prefix of the Lyndon word
  `ababbabac`, and the rotation `aababbab` of `w` is smaller than `x' x = abaababb`. So the minimal rotation of a
  string `x^k x'` with a Lyndon word `x` and a proper prefix `x'` of `x` need not be `x' x^k`.
-/

namespace KnownPattern

/-- A Lyndon word: nonempty and smaller than each of its proper rotations. -/
def IsLyndon (x : List ℕ) : Prop := x ≠ [] ∧ ∀ i < x.length, 0 < i → x < x.rotate i

instance (x : List ℕ) : Decidable (IsLyndon x) := by unfold IsLyndon; infer_instance

theorem rotation_example :
    IsLyndon [0, 1, 0, 1, 1] ∧ IsLyndon ([0, 1, 0, 1, 1] ++ [0, 1, 0] ++ [2]) ∧
      ([0, 1, 0, 1, 1] ++ [0, 1, 0]).rotate 7 < [0, 1, 0] ++ [0, 1, 0, 1, 1] := by
  decide

end KnownPattern
