import SsspFlow.Annuli

/-!
# The annuli of a level are different components

Two annuli of one level of a run whose components, in the splits at their own corners, share a
corner are the same annulus. The proof follows the run down to the step whose two sides hold them:
annuli below the two sides lie in the components of `κ1(y)` and `κ0(x)` of the cut along the step,
and these are different (`Live.not_gcomp_sides`).

* `CutPath.Run.sep`: two annuli at depth `ℓ` of a run whose components share a corner are equal.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

noncomputable section

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}

section Run

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- **The annuli of a level are different components.** Two annuli at depth `ℓ` of a run whose
components in the splits at their corners share a corner `y` are equal. -/
theorem Run.sep : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), ∀ A ∈ r.nodes ℓ, ∀ B ∈ r.nodes ℓ, ∀ y : D × Bool,
      (R.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) y →
      (R.double.split B.1).toHypermap.gcomp (B.2.κ0 B.2.xa) y → A = B
  | _, _, _, _, .leaf .., 0 => by
    intro A hA B hB _ _ _
    simp only [Run.nodes, List.mem_singleton] at hA hB
    rw [hA, hB]
  | _, _, _, _, .leaf .., _ + 1 => fun A hA => by simp [Run.nodes] at hA
  | _, _, _, _, .node .., 0 => by
    intro A hA B hB _ _ _
    simp only [Run.nodes, List.mem_singleton] at hA hB
    rw [hA, hB]
  | _, L, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1 => by
    intro A hA B hB y hAy hBy
    simp only [Run.nodes, List.mem_append] at hA hB
    have cross : ∀ {X Y : Σ Γ' : Finset (D × Bool), C.Live g Γ'}, X ∈ left.nodes ℓ → Y ∈ right.nodes ℓ →
        (R.double.split X.1).toHypermap.gcomp (X.2.κ0 X.2.xa) y →
        (R.double.split Y.1).toHypermap.gcomp (Y.2.κ0 Y.2.xa) y → False := by
      intro X Y hX hY hXy hYy
      obtain ⟨hsubX, -, h3X⟩ := (SideA.inv left ℓ).1 X hX
      obtain ⟨hsubY, -, h3Y⟩ := (SideB.inv right ℓ).1 Y hY
      have hx := connect_trans h3X (RootedTree.gcomp_split_mono hsubX hXy)
      have hy := connect_trans h3Y (RootedTree.gcomp_split_mono hsubY hYy)
      cases left with
      | overlap => simp [SideA.nodes] at hX
      | empty => simp [SideA.nodes] at hX
      | child noA hdegA rA =>
        cases right with
        | overlap => simp [SideB.nodes] at hY
        | empty => simp [SideB.nodes] at hY
        | child noB hdegB rB =>
          exact L.not_gcomp_sides hR hC S noA hdegA noB hdegB
            (connect_trans hy ((R.double.split _).toHypermap.glinkC _ _ hx))
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact SideA.sep left ℓ A hA B hB y hAy hBy
    · exact (cross hA hB hAy hBy).elim
    · exact (cross hB hA hBy hAy).elim
    · exact SideB.sep right ℓ A hA B hB y hAy hBy
theorem SideA.sep : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      ∀ A ∈ s.nodes ℓ, ∀ B ∈ s.nodes ℓ, ∀ y : D × Bool,
      (R.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) y →
      (R.double.split B.1).toHypermap.gcomp (B.2.κ0 B.2.xa) y → A = B
  | _, _, _, _, _, _, _, .overlap .., _ => fun A hA => by simp [SideA.nodes] at hA
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => by
    simp only [SideA.nodes]
    exact Run.sep r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => fun A hA => by simp [SideA.nodes] at hA
theorem SideB.sep : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      ∀ A ∈ s.nodes ℓ, ∀ B ∈ s.nodes ℓ, ∀ y : D × Bool,
      (R.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) y →
      (R.double.split B.1).toHypermap.gcomp (B.2.κ0 B.2.xa) y → A = B
  | _, _, _, _, _, _, _, .overlap .., _ => fun A hA => by simp [SideB.nodes] at hA
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => by
    simp only [SideB.nodes]
    exact Run.sep r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => fun A hA => by simp [SideB.nodes] at hA
end

end Run

end CutPath

end RotSystem

end

end SsspFlow
