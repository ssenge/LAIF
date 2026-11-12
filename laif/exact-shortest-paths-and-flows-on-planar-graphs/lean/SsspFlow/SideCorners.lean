import SsspFlow.AnnuliSep

/-!
# The corners of the two sides of an annulus

The side of `κ0(x_a)` of a live annulus has the corners `κ0(x_a)`, the inner corners `L_a` and
`κ1(y_a)`; the side of `κ0(x_b)` has `κ0(x_b)`, `L_b` and `κ1(y_b)`. They lie on the boundary of the
annulus. A walk of an annulus of a level of a run from `κ0(t)` visits no corner of the sides of
another annulus of the same level.

* `CutPath.Live.CornerA`, `CutPath.Live.CornerB`: the corners of the two sides.
* `CutPath.Live.gcomp_of_visits`: a visited corner lies in the component of `κ0(t)`.
* `CutPath.Run.corner_eq`: a corner of a side of an annulus of a level that a walk of an annulus of
  the same level visits is a corner of that annulus.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

open scoped ENNReal

universe u

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}

namespace Live

variable {Γ : Finset (D × Bool)} (L : C.Live g Γ)

/-- A corner of the side of `κ0(x_a)`: `κ0(x_a)`, a corner of `L_a` or `κ1(y_a)`. -/
def CornerA (c : D × Bool) : Prop := c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya

/-- A corner of the side of `κ0(x_b)`: `κ0(x_b)`, a corner of `L_b` or `κ1(y_b)`. -/
def CornerB (c : D × Bool) : Prop := c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb

/-- The corners of the two sides lie on the boundary of the annulus. -/
theorem corner_mem {c : D × Bool} (hc : L.CornerA c ∨ L.CornerB c) :
    c ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
  rcases hc with (rfl | hc | rfl) | (rfl | hc | rfl)
  · exact L.κ0_mem le_rfl L.le_x
  · unfold liveBoundary
    simp only [List.mem_append]
    exact Or.inr hc
  · exact L.κ1_mem le_rfl L.le_y
  · exact L.κ0_mem L.le_x le_rfl
  · unfold liveBoundary
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr hc))
  · exact L.κ1_mem L.le_y le_rfl

/-- A corner that a walk from `κ0(t)` visits lies in the component of `κ0(t)`. -/
theorem gcomp_of_visits {t : ℕ} {p : List (D × Bool)} {b : (R.double.split Γ).Vertex}
    (hp : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 t)) p b) {c : D × Bool}
    (hv : L.Visits t p c) : (R.double.split Γ).toHypermap.gcomp (L.κ0 t) c := by
  rcases hv with h | ⟨y, hy, h⟩
  · exact IsWalk.gcomp_tail (p := []) h.symm
  · obtain ⟨s, s', rfl⟩ := List.append_of_mem hy
    obtain ⟨m, h1, h2⟩ := isWalk_append_iff.1 hp
    have hw : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 t)) (s ++ [y])
        ((R.double.split Γ).tail c) := h1.append ⟨h2.1, h⟩
    exact IsWalk.gcomp_tail hw

end Live

section Run

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

/-- **Corners of other annuli are not visited.** If a walk of an annulus `A` of a level of a run from
`κ0(t)` visits a corner of a side of an annulus `B` of the same level, then `A = B`. -/
theorem Run.corner_eq {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (ℓ : ℕ) {A B : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) (hB : B ∈ r.nodes ℓ)
    {t : ℕ} (h1 : A.2.xa ≤ t) (h2 : t ≤ A.2.xb) {p : List (D × Bool)}
    {b : (R.double.split A.1).Vertex}
    (hp : (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) p b) {c : D × Bool}
    (hv : A.2.Visits t p c) (hc : B.2.CornerA c ∨ B.2.CornerB c) : A = B :=
  r.sep ℓ A hA B hB c (connect_trans (A.2.gcomp_κ0 h1 h2) (A.2.gcomp_of_visits hp hv))
    (B.2.gcomp_bound (B.2.κ0_mem le_rfl B.2.le_x) (B.2.corner_mem hc))

end Run

end CutPath

end RotSystem

end SsspFlow
