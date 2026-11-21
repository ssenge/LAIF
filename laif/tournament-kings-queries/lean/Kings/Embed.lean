import Kings.Basic

/-!
# Orthogonal Vectors inside a tournament

For `X : Fin m → Fin m → Prop` with `m = 2h + 1` and `h ≥ 1`, the tournament `arc X` has vertex set
`Vtx m`: three classes `r i`, `r' j`, `w t` of size `m`, with the rotational tournament `rot` inside
each class, and four fixed vertices `a, b, c, d`. Every orientation is fixed or equal to one entry of `X`.

* `rot_two`: the rotational tournament on `2h + 1` vertices has diameter two.
* `isTournament_arc`: `arc X` is a tournament.
* `allKings_arc_iff`: every vertex of `arc X` is a king exactly when every two rows of `X`,
  equal or not, share a one.
* `allKings_arc_iff_not_hasOV`: for `m ≥ 2`, exactly when `X` has no orthogonal pair of rows.
-/

namespace Kings

/-- `i` beats `j` in the rotational tournament: `j - i mod m` lies in `1, …, (m - 1) / 2`. -/
def rot (m : ℕ) (i j : Fin m) : Prop :=
  ((i : ℕ) < j ∧ (j : ℕ) ≤ i + (m - 1) / 2) ∨ ((j : ℕ) < i ∧ (j : ℕ) + m ≤ i + (m - 1) / 2)

theorem rot_irrefl (m : ℕ) (i : Fin m) : ¬ rot m i i := by
  simp [rot]

theorem rot_asymm {m h : ℕ} (hm : m = 2 * h + 1) (i j : Fin m) : rot m i j → ¬ rot m j i := by
  have := i.isLt; have := j.isLt
  simp only [rot]; subst hm
  have e : (2 * h + 1 - 1) / 2 = h := by omega
  rw [e]; omega

theorem rot_total {m h : ℕ} (hm : m = 2 * h + 1) (i j : Fin m) (hij : i ≠ j) :
    rot m i j ∨ rot m j i := by
  have := i.isLt; have := j.isLt
  have hv : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
  simp only [rot]; subst hm
  have e : (2 * h + 1 - 1) / 2 = h := by omega
  rw [e]; omega

/-- **Diameter two.** If `i ≠ k` and `i` does not beat `k`, then `i` beats some `z` that beats `k`. -/
theorem rot_two {m h : ℕ} (hm : m = 2 * h + 1) (h1 : 1 ≤ h) {i k : Fin m} (hik : i ≠ k)
    (hn : ¬ rot m i k) : ∃ z, rot m i z ∧ rot m z k := by
  have hi := i.isLt; have hk := k.isLt
  have hv : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
  simp only [rot] at hn ⊢; subst hm
  have e : (2 * h + 1 - 1) / 2 = h := by omega
  rw [e] at hn ⊢
  by_cases hz : (i : ℕ) + h < 2 * h + 1
  · exact ⟨⟨i + h, hz⟩, by simp only; omega, by simp only; omega⟩
  · exact ⟨⟨i + h - (2 * h + 1), by omega⟩, by simp only; omega, by simp only; omega⟩

/-- Vertices of the tournament: rows `r i`, second copies `r' j`, columns `w t`, and `a, b, c, d`. -/
inductive Vtx (m : ℕ) where
  | r (i : Fin m)
  | r' (i : Fin m)
  | w (t : Fin m)
  | a
  | b
  | c
  | d
  deriving DecidableEq

/-- `arc X u v` means that `u` beats `v`. -/
def arc {m : ℕ} (X : Fin m → Fin m → Prop) : Vtx m → Vtx m → Prop
  | .r i, .r k => rot m i k
  | .r' i, .r' k => rot m i k
  | .w s, .w t => rot m s t
  | .r' _, .r _ => True
  | .r i, .w t => X i t
  | .w t, .r i => ¬ X i t
  | .w t, .r' j => X j t
  | .r' j, .w t => ¬ X j t
  | .r _, .a => True
  | .r' _, .a => True
  | .a, .w _ => True
  | .b, .r _ => True
  | .b, .r' _ => True
  | .w _, .b => True
  | .r _, .c => True
  | .r' _, .c => True
  | .w _, .c => True
  | .d, .r _ => True
  | .d, .r' _ => True
  | .d, .w _ => True
  | .a, .b => True
  | .c, .a => True
  | .c, .b => True
  | .a, .d => True
  | .b, .d => True
  | .c, .d => True
  | _, _ => False

theorem isTournament_arc {m h : ℕ} (hm : m = 2 * h + 1) (X : Fin m → Fin m → Prop) :
    IsTournament (arc X) where
  irrefl x := by cases x <;> simp [arc, rot]
  asymm x y := by
    cases x <;> cases y <;> simp only [arc] <;>
      first | exact rot_asymm hm _ _ | tauto
  total x y hxy := by
    cases x <;> cases y <;> simp only [arc] <;>
      first
        | exact rot_total hm _ _ (fun e => hxy (by rw [e]))
        | tauto

/-- **Lower reduction.** Every vertex of `arc X` is a king exactly when every two rows of `X`, equal or
not, share a one. -/
theorem allKings_arc_iff {m h : ℕ} (hm : m = 2 * h + 1) (h1 : 1 ≤ h) (X : Fin m → Fin m → Prop) :
    (∀ x, IsKing (arc X) x) ↔ ∀ i j, ∃ t, X i t ∧ X j t := by
  constructor
  · intro hk i j
    rcases hk (.r i) (.r' j) (by simp) with hh | ⟨z, hz1, hz2⟩
    · simp [arc] at hh
    · cases z <;> simp [arc] at hz1 hz2
      exact ⟨_, hz1, hz2⟩
  · intro hX x y hyx
    have h0 : 0 < m := by omega
    by_cases hxy : arc X x y
    · exact Or.inl hxy
    right
    cases x <;> cases y <;> simp only [arc, not_true_eq_false, not_false_eq_true, not_not] at hxy
    all_goals first
      | exact absurd rfl hyx
      | (obtain ⟨z, hz1, hz2⟩ := rot_two hm h1 (fun e => hyx (by rw [e])) hxy
         first | exact ⟨.r z, hz1, hz2⟩ | exact ⟨.r' z, hz1, hz2⟩ | exact ⟨.w z, hz1, hz2⟩)
      | (rename_i i j; obtain ⟨t, ht1, ht2⟩ := hX i j; exact ⟨.w t, ht1, ht2⟩)
      | exact ⟨.a, trivial, trivial⟩
      | exact ⟨.b, trivial, trivial⟩
      | exact ⟨.c, trivial, trivial⟩
      | exact ⟨.d, trivial, trivial⟩
      | exact ⟨.r ⟨0, h0⟩, trivial, trivial⟩
      | exact ⟨.w ⟨0, h0⟩, trivial, trivial⟩

/-- For `m ≥ 2`, every vertex of `arc X` is a king exactly when no two distinct rows of `X` are
orthogonal. -/
theorem allKings_arc_iff_not_hasOV {m h : ℕ} (hm : m = 2 * h + 1) (h1 : 1 ≤ h)
    (X : Fin m → Fin m → Prop) : (∀ x, IsKing (arc X) x) ↔ ¬ HasOV X := by
  rw [allKings_arc_iff hm h1]
  constructor
  · rintro hX ⟨i, j, -, ho⟩
    obtain ⟨t, ht⟩ := hX i j
    exact ho t ht
  · intro hno i j
    by_contra hij
    push Not at hij
    by_cases e : i = j
    · subst e
      have h0 : 1 < m := by omega
      obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i :=
        ⟨if (i : ℕ) = 0 then ⟨1, h0⟩ else ⟨0, by omega⟩, by
          split_ifs with hi <;> intro e <;> simp [Fin.ext_iff] at e <;> omega⟩
      exact hno ⟨i, j, hj.symm, fun t ht => hij t ht.1 ht.1⟩
    · exact hno ⟨i, j, e, fun t ht => hij t ht.1 ht.2⟩

end Kings
