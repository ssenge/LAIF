import SsspFlow.GHatChainIdx

/-!
# The corners that the chain of a target visits

A walk of a live annulus from `κ0(t)` visits a corner exactly when, in the split at the incisions of
the level, the corner lies at `κ0(t)` or at the head of a dart of the walk, as long as no other
incision of the level is reachable from `κ0(t)`. For the chain of a target, this is read at the copies
of the nodes of the chain.

* `RData.visits_iff_dualSplit`: the visits of a walk from `κ0(t)` in the split at the level.
* `RData.chain_visits`: the chain of a target visits a corner exactly when the piece of the copy of one
  of its nodes is the vertex of the corner.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- **Visits in the split at the level.** Let `Γ ⊆ S.Γ` and let no other incision of `S.Γ` be
reachable from `κ0(t)` in the split at `Γ`. For a walk `p` from `κ0(t)` in the split at `Γ`, the walk
visits a corner `c` exactly when, in the split at `S.Γ`, `c` lies at `κ0(t)` or at the head of a dart
of `p`. -/
theorem visits_iff_dualSplit {C : G.dual.CutPath} {g : E → ℝ≥0∞} {Γ : Finset (E × Bool)}
    (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (G.dual.double.split Γ).IsWalk
      ((G.dual.double.split Γ).tail (L.κ0 t)) p ((G.dual.double.split Γ).tail w))
    {p : List (E × Bool)} {b : (G.dual.double.split Γ).Vertex}
    (hp : (G.dual.double.split Γ).IsWalk ((G.dual.double.split Γ).tail (L.κ0 t)) p b) (c : E × Bool) :
    L.Visits t p c ↔ (S.dualSplit.tail c = S.dualSplit.tail (L.κ0 t) ∨
      ∃ y ∈ p, S.dualSplit.head y = S.dualSplit.tail c) := by
  have teq : ∀ u y : E × Bool, (∃ q, (G.dual.double.split Γ).IsWalk
      ((G.dual.double.split Γ).tail (L.κ0 t)) q ((G.dual.double.split Γ).tail u)) →
      (S.dualSplit.tail u = S.dualSplit.tail y ↔
        (G.dual.double.split Γ).tail u = (G.dual.double.split Γ).tail y) :=
    fun u y hu => G.dual.double.isWalk_split_split_iff hS hz [] hu y
  have hreach : ∀ y ∈ p, ∃ q, (G.dual.double.split Γ).IsWalk
      ((G.dual.double.split Γ).tail (L.κ0 t)) q ((G.dual.double.split Γ).tail (G.dual.double.rev y)) := by
    intro y hy
    obtain ⟨s, s', rfl⟩ := List.append_of_mem hy
    obtain ⟨m, h1, h2⟩ := isWalk_append_iff.1 hp
    exact ⟨s ++ [y], h1.append ⟨h2.1, rfl⟩⟩
  unfold CutPath.Live.Visits
  refine or_congr ?_ (exists_congr fun y => and_congr_right fun hy => ?_)
  · exact eq_comm.trans ((teq _ c ⟨[], rfl⟩).symm.trans eq_comm)
  · exact (teq _ _ (hreach y hy)).symm

end RData

end RotSystem

end SsspFlow
