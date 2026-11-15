import SsspFlow.RunGraft
import SsspFlow.AnnuliSep

/-!
# The list of annuli of a level

The subruns of a run at one depth are on different annuli, since annuli below the two sides of a
step lie in different components of the cut along the step. So the annuli of a level that are not
leaves, each with the middle index of its range, form a list in which each annulus has one index.

* `CutPath.Run.bounds`: the range of a run lies in the ranges of its annulus.
* `CutPath.Run.nodes_nodup`: the annuli at one depth are different.
* `CutPath.Run.levelQ`: the annuli at depth `ℓ` that are not leaves, with their middle indices.
* `CutPath.Run.levelQ_uniq`, `CutPath.Run.mem_levelQ`: each annulus has one index, and the members
  are the subruns that are not leaves.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞} {hR : R.Planar} {hC : R.Connected}
  {hg : ∀ x, g (R.rev x) = g x}

/-- The range of a run lies in the ranges of both copies of the path of its annulus. -/
theorem Run.bounds {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k) :
    j ≤ k ∧ L.xa ≤ j ∧ L.ya ≤ j ∧ k ≤ L.xb ∧ k ≤ L.yb := by
  cases r with
  | leaf hjk _ hxa hya hxb hyb => exact ⟨hjk, hxa, hya, hxb, hyb⟩
  | node hjk hxa hya hxb hyb => exact ⟨by omega, hxa, hya, hxb, hyb⟩

mutual
/-- **The annuli at one depth are different.** -/
theorem Run.nodes_nodup : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), (r.nodes ℓ).Nodup
  | _, _, _, _, .leaf .., 0 => List.nodup_singleton _
  | _, _, _, _, .leaf .., _ + 1 => List.nodup_nil
  | _, _, _, _, .node .., 0 => List.nodup_singleton _
  | _, L, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1 => by
    simp only [Run.nodes]
    refine List.nodup_append.2 ⟨SideA.nodes_nodup left ℓ, SideB.nodes_nodup right ℓ, ?_⟩
    intro X hX Y hY hXY
    subst hXY
    obtain ⟨hsubX, -, h3X⟩ := (SideA.inv left ℓ).1 X hX
    obtain ⟨hsubY, -, h3Y⟩ := (SideB.inv right ℓ).1 X hY
    have hx := connect_trans h3X (RootedTree.gcomp_split_mono hsubX (connect_refl (X.2.κ0 X.2.xa)))
    have hy := connect_trans h3Y (RootedTree.gcomp_split_mono hsubY (connect_refl (X.2.κ0 X.2.xa)))
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
theorem SideA.nodes_nodup : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ), (s.nodes ℓ).Nodup
  | _, _, _, _, _, _, _, .overlap .., _ => List.nodup_nil
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => Run.nodes_nodup r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => List.nodup_nil
theorem SideB.nodes_nodup : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ), (s.nodes ℓ).Nodup
  | _, _, _, _, _, _, _, .overlap .., _ => List.nodup_nil
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => Run.nodes_nodup r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => List.nodup_nil
end

variable {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k) (ℓ : ℕ)

/-- The annuli at depth `ℓ` that are not leaves, with the middle indices of their ranges. -/
def Run.levelQ : List ((Σ Γ' : Finset (D × Bool), C.Live g Γ') × ℕ) :=
  (r.subs ℓ).filterMap fun s =>
    if s.2.1.1 + 2 ≤ s.2.1.2 then some (s.1, (s.2.1.1 + s.2.1.2) / 2) else none

theorem Run.mem_levelQ {q : (Σ Γ' : Finset (D × Bool), C.Live g Γ') × ℕ} :
    q ∈ r.levelQ ℓ ↔ ∃ s ∈ r.subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧ q = (s.1, (s.2.1.1 + s.2.1.2) / 2) := by
  unfold Run.levelQ
  rw [List.mem_filterMap]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

/-- A subrun at depth `ℓ` is determined by its annulus. -/
theorem Run.subs_eq_of_fst {s s' : Sub C hR hC hg} (hs : s ∈ r.subs ℓ) (hs' : s' ∈ r.subs ℓ)
    (h : s.1 = s'.1) : s = s' := by
  have hn := r.nodes_nodup ℓ
  rw [Run.nodes_eq_subs] at hn
  exact List.inj_on_of_nodup_map hn hs hs' h

/-- **Each annulus of a level has one index.** -/
theorem Run.levelQ_uniq : ∀ q ∈ r.levelQ ℓ, ∀ q' ∈ r.levelQ ℓ, q.1 = q'.1 → q.2 = q'.2 := by
  intro q hq q' hq' h
  obtain ⟨s, hs, -, rfl⟩ := (r.mem_levelQ ℓ).1 hq
  obtain ⟨s', hs', -, rfl⟩ := (r.mem_levelQ ℓ).1 hq'
  rw [r.subs_eq_of_fst ℓ hs hs' h]

/-- The members of the list of a level are annuli of the level, with indices in their ranges. -/
theorem Run.levelQ_range : ∀ q ∈ r.levelQ ℓ, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧
    q.2 ≤ q.1.2.xb ∧ q.2 ≤ q.1.2.yb := by
  intro q hq
  obtain ⟨s, hs, hjk, rfl⟩ := (r.mem_levelQ ℓ).1 hq
  obtain ⟨-, h1, h2, h3, h4⟩ := s.2.2.bounds
  refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  rw [Run.nodes_eq_subs]
  exact List.mem_map_of_mem hs

end CutPath

end RotSystem

end SsspFlow
