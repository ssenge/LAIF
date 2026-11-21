import Mathlib.Tactic

/-!
# Kings of a tournament and Orthogonal Vectors

* `IsTournament T`: `T` orients every pair of distinct vertices exactly once.
* `IsKing T x`: every other vertex is reached from `x` by a path of length at most two.
* `not_king_iff`: `x` is not a king exactly when `N⁺(x) ⊆ N⁺(y)` for some `y ≠ x`.
* `vec T`: the Orthogonal Vectors instance on `V ⊕ V ⊕ Bool` (positions and coordinates), with
  `U_x = (N⁺(x), e_x, 1, 0)`, `W_y = (V ∖ N⁺(y), e_y, 0, 1)` and two all-ones vectors.
* `hasOV_vec_iff`: this instance has an orthogonal pair exactly when some vertex is not a king.
-/

namespace Kings

variable {V : Type*}

/-- `T u v` means that `u` beats `v`. -/
structure IsTournament (T : V → V → Prop) : Prop where
  irrefl : ∀ x, ¬ T x x
  asymm : ∀ x y, T x y → ¬ T y x
  total : ∀ x y, x ≠ y → T x y ∨ T y x

/-- Every other vertex is reached from `x` within two steps. -/
def IsKing (T : V → V → Prop) (x : V) : Prop :=
  ∀ y, y ≠ x → T x y ∨ ∃ z, T x z ∧ T z y

/-- **Covering.** A vertex `x` is not a king exactly when some `y ≠ x` beats every vertex that `x` beats. -/
theorem not_king_iff {T : V → V → Prop} (hT : IsTournament T) (x : V) :
    ¬ IsKing T x ↔ ∃ y, y ≠ x ∧ ∀ z, T x z → T y z := by
  constructor
  · intro h
    simp only [IsKing, not_forall, not_or, not_exists, not_and] at h
    obtain ⟨y, hyx, hxy, hno⟩ := h
    refine ⟨y, hyx, fun z hxz => ?_⟩
    have hzy : z ≠ y := by rintro rfl; exact hxy hxz
    rcases hT.total y z (Ne.symm hzy) with h | h
    · exact h
    · exact absurd h (hno z hxz)
  · rintro ⟨y, hyx, hsub⟩ hk
    rcases hk y hyx with h | ⟨z, hxz, hzy⟩
    · exact hT.irrefl y (hsub y h)
    · exact hT.asymm _ _ (hsub z hxz) hzy

/-- Two positions of a list of vectors with disjoint supports. -/
def Orth {ι κ : Type*} (v : ι → κ → Prop) (i j : ι) : Prop := ∀ t, ¬ (v i t ∧ v j t)

/-- The list has an orthogonal pair at distinct positions. -/
def HasOV {ι κ : Type*} (v : ι → κ → Prop) : Prop := ∃ i j, i ≠ j ∧ Orth v i j

/-- The Orthogonal Vectors instance of a tournament, with positions and coordinates `V ⊕ V ⊕ Bool`. -/
def vec (T : V → V → Prop) : V ⊕ V ⊕ Bool → V ⊕ V ⊕ Bool → Prop
  | .inl x, .inl z => T x z
  | .inl x, .inr (.inl z) => z = x
  | .inl _, .inr (.inr k) => k = false
  | .inr (.inl y), .inl z => ¬ T y z
  | .inr (.inl y), .inr (.inl z) => z = y
  | .inr (.inl _), .inr (.inr k) => k = true
  | .inr (.inr _), _ => True

/-- **Upper reduction.** The instance `vec T` has an orthogonal pair exactly when some vertex of the
tournament `T` is not a king. -/
theorem hasOV_vec_iff {T : V → V → Prop} (hT : IsTournament T) :
    HasOV (vec T) ↔ ¬ ∀ x, IsKing T x := by
  constructor
  · rintro ⟨i, j, hij, ho⟩ hall
    have key : ∀ x y, x ≠ y → Orth (vec T) (.inl x) (.inr (.inl y)) → False := by
      intro x y hxy ho
      refine (not_king_iff hT x).2 ⟨y, Ne.symm hxy, fun z hxz => ?_⟩ (hall x)
      by_contra hyz
      exact ho (.inl z) ⟨hxz, hyz⟩
    rcases i with x | y | k <;> rcases j with x' | y' | k'
    · exact ho (.inr (.inr false)) ⟨rfl, rfl⟩
    · by_cases h : x = y'
      · subst h; exact ho (.inr (.inl x)) ⟨rfl, rfl⟩
      · exact key x y' h ho
    · exact ho (.inr (.inr false)) ⟨rfl, trivial⟩
    · by_cases h : x' = y
      · subst h; exact ho (.inr (.inl x')) ⟨rfl, rfl⟩
      · exact key x' y h (fun t ht => ho t ⟨ht.2, ht.1⟩)
    · exact ho (.inr (.inr true)) ⟨rfl, rfl⟩
    · exact ho (.inr (.inr true)) ⟨rfl, trivial⟩
    · exact ho (.inr (.inr false)) ⟨trivial, rfl⟩
    · exact ho (.inr (.inr true)) ⟨trivial, rfl⟩
    · exact ho (.inr (.inr true)) ⟨trivial, trivial⟩
  · intro h
    simp only [not_forall] at h
    obtain ⟨x, hx⟩ := h
    obtain ⟨y, hyx, hsub⟩ := (not_king_iff hT x).1 hx
    refine ⟨.inl x, .inr (.inl y), by simp, fun t ht => ?_⟩
    rcases t with z | z | k
    · exact ht.2 (hsub z ht.1)
    · exact hyx (ht.2.symm.trans ht.1)
    · exact Bool.false_ne_true ((show k = false from ht.1).symm.trans (show k = true from ht.2))

end Kings
