import SsspFlow.RunLevel

/-!
# The corners of the cut path in the annuli of a run

The side of `κ0(x_a)` of a step changes `κ0` only at the index `x` of the step, its new `x_b`, and the
side of `κ0(x_b)` changes `κ1` only at the index `y`, its new `y_a`. So every annulus of a run lies in
the ranges of the annuli above it, and inside its ranges its corners `κ0(t)`, `κ1(t)` are those of the
annulus of the run. In particular the corners at the middle index of every annulus that is not a leaf
are corners of the top annulus.

* `CutPath.Live.Below`: the ranges of an annulus lie in those of another, and inside them the corners
  agree.
* `CutPath.Live.below_lo`, `CutPath.Live.below_hi`: the two sides of a step lie below the annulus.
* `CutPath.Run.below_nodes`: every annulus of a run lies below its top annulus.
* `CutPath.Run.mid_corners`: at the middle index of a subrun that is not a leaf, its corners are those
  of the top annulus.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}

/-- The ranges of `A` lie in those of `L`, and inside its ranges the corners of `A` are those of `L`. -/
def Live.Below {Γ Γ' : Finset (D × Bool)} (L : C.Live g Γ) (A : C.Live g Γ') : Prop :=
  L.xa ≤ A.xa ∧ A.xb ≤ L.xb ∧ L.ya ≤ A.ya ∧ A.yb ≤ L.yb ∧
    (∀ t, A.xa < t → t < A.xb → A.κ0 t = L.κ0 t) ∧ (∀ t, A.ya < t → t < A.yb → A.κ1 t = L.κ1 t)

theorem Live.below_refl {Γ : Finset (D × Bool)} (L : C.Live g Γ) : L.Below L :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem Live.Below.trans {Γ Γ' Γ'' : Finset (D × Bool)} {L : C.Live g Γ} {A : C.Live g Γ'}
    {B : C.Live g Γ''} (h1 : L.Below A) (h2 : A.Below B) : L.Below B := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  refine ⟨a1.trans b1, b2.trans a2, a3.trans b3, b4.trans a4, fun t h h' => ?_, fun t h h' => ?_⟩
  · rw [b5 t h h', a5 t (lt_of_le_of_lt b1 h) (lt_of_lt_of_le h' b2)]
  · rw [b6 t h h', a6 t (lt_of_le_of_lt b3 h) (lt_of_lt_of_le h' b4)]

variable {Γ : Finset (D × Bool)} (L : C.Live g Γ) (hR : R.Planar) (hC : R.Connected) (S : L.Step)
  (hg : ∀ x, g (R.rev x) = g x)

/-- **The side of `κ0(x_a)` lies below the annulus.** -/
theorem Live.below_lo
    (noA : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.La, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ) :
    L.Below (L.lo hR hC S noA hdeg hg) := by
  refine ⟨le_rfl, S.hxb, le_rfl, S.hyb, fun t _ ht => ?_, fun _ _ _ => rfl⟩
  have hne : t ≠ S.x := Nat.ne_of_lt ht
  show L.loκ0 hR hC S noA hdeg t = L.κ0 t
  simp only [Live.loκ0, hne, ↓reduceIte]

/-- **The side of `κ0(x_b)` lies below the annulus.** -/
theorem Live.below_hi
    (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ) :
    L.Below (L.hi hR hC S noB hdeg hg) := by
  refine ⟨S.hxa, le_rfl, S.hya, le_rfl, fun _ _ _ => rfl, fun t ht _ => ?_⟩
  have hne : t ≠ S.y := Nat.ne_of_gt ht
  show L.hiκ1 hR hC S noB hdeg t = L.κ1 t
  simp only [Live.hiκ1, hne, ↓reduceIte]

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- **Every annulus of a run lies below its top annulus.** -/
theorem Run.below_nodes : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), ∀ A ∈ r.nodes ℓ, L.Below A.2
  | _, L, _, _, .leaf .., 0, A, hA => by
    rw [List.mem_singleton.1 hA]
    exact L.below_refl
  | _, _, _, _, .leaf .., _ + 1, _, hA => absurd hA List.not_mem_nil
  | _, L, _, _, .node .., 0, A, hA => by
    rw [List.mem_singleton.1 hA]
    exact L.below_refl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, A, hA => by
    rcases List.mem_append.1 hA with h | h
    · exact SideA.below_nodes left ℓ A h
    · exact SideB.below_nodes right ℓ A h
theorem SideA.below_nodes : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ), ∀ A ∈ s.nodes ℓ, L.Below A.2
  | _, _, _, _, _, _, _, .overlap .., _, _, hA => absurd hA List.not_mem_nil
  | _, L, _, _, S, _, _, .child noA hdeg r, ℓ, A, hA =>
    (L.below_lo hR hC S hg noA hdeg).trans (Run.below_nodes r ℓ A hA)
  | _, _, _, _, _, _, _, .empty _, _, _, hA => absurd hA List.not_mem_nil
theorem SideB.below_nodes : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ), ∀ A ∈ s.nodes ℓ, L.Below A.2
  | _, _, _, _, _, _, _, .overlap .., _, _, hA => absurd hA List.not_mem_nil
  | _, L, _, _, S, _, _, .child noB hdeg r, ℓ, A, hA =>
    (L.below_hi hR hC S hg noB hdeg).trans (Run.below_nodes r ℓ A hA)
  | _, _, _, _, _, _, _, .empty _, _, _, hA => absurd hA List.not_mem_nil
end

/-- **The corners at a middle index are those of the top annulus.** For a subrun at depth `ℓ` with a
range `[j, k]`, `j + 2 ≤ k`, the corners of its annulus at the middle index are those of the top
annulus. -/
theorem Run.mid_corners {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (ℓ : ℕ) {s : Sub C hR hC hg} (hs : s ∈ r.subs ℓ) (hjk : s.2.1.1 + 2 ≤ s.2.1.2) :
    s.1.2.κ0 ((s.2.1.1 + s.2.1.2) / 2) = L.κ0 ((s.2.1.1 + s.2.1.2) / 2) ∧
      s.1.2.κ1 ((s.2.1.1 + s.2.1.2) / 2) = L.κ1 ((s.2.1.1 + s.2.1.2) / 2) := by
  have hA : s.1 ∈ r.nodes ℓ := by
    rw [Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  obtain ⟨-, -, -, -, h0, h1⟩ := r.below_nodes ℓ s.1 hA
  obtain ⟨-, hxa, hya, hxb, hyb⟩ := s.2.2.bounds
  exact ⟨h0 _ (by omega) (by omega), h1 _ (by omega) (by omega)⟩

end CutPath

end RotSystem

end SsspFlow
