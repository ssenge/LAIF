import SsspFlow.OracleChainSum

/-!
# Positions on the parent chains of an oracle

The rank of an output of the oracle drops at every valid parent step, so a node is reached from a
node at most once along valid parent steps. With length `1` on the arcs to the parents, one more run
from a set of targets whose chains do not meet gives every node of a chain its position: the number
of steps from its target.

* `Net.ExactSpec.parSteps_inj`: along valid parent steps from one node, the positions of a node are
  unique.
* `Net.ExactSpec.dsrcTop_pos`: for targets whose valid chains do not meet, the distance for the
  lengths `1` on the arcs to the parents is the position on the chain.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Along valid parent steps the rank drops. -/
theorem Net.ExactSpec.rank_iter {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) : ∃ rank : V → ℕ, ∀ (t : V) (i : ℕ), Net.ParSteps r t i →
      ∀ k < i, rank ((Net.parOf r)^[i] t) < rank ((Net.parOf r)^[k] t) := by
  obtain ⟨rank, hrank⟩ := h.parent
  have step : ∀ v p, (r v).2 = some p → rank p < rank v := fun v p hp => by
    rcases hrank v with ⟨p', hp', -, -, -, hlt⟩ | ⟨hn, -⟩
    · rw [hp] at hp'
      cases hp'
      exact hlt
    · rw [hp] at hn
      cases hn
  refine ⟨rank, fun t i hs => ?_⟩
  induction i with
  | zero => intro k hk; omega
  | succ i ih =>
    intro k hk
    have hs' : Net.ParSteps r t i := fun k hk => hs k (by omega)
    have h1 : rank ((Net.parOf r)^[i + 1] t) < rank ((Net.parOf r)^[i] t) := by
      exact step _ _ (hs i (by omega))
    rcases Nat.lt_or_ge k i with hki | hki
    · exact h1.trans (ih hs' k hki)
    · obtain rfl : k = i := by omega
      exact h1

/-- **Positions are unique.** Two numbers of valid parent steps from one node that reach the same
node are equal. -/
theorem Net.ExactSpec.parSteps_inj {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) {t : V} {i i' : ℕ} (hs : Net.ParSteps r t i) (hs' : Net.ParSteps r t i')
    (he : (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t) : i = i' := by
  obtain ⟨rank, hr⟩ := h.rank_iter
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have := hr t i' hs' i hlt
    rw [he] at this
    exact absurd this (lt_irrefl _)
  · exact heq
  · have := hr t i hs i' hgt
    rw [he] at this
    exact absurd this (lt_irrefl _)


open Classical in
/-- **Positions on the chains.** For targets whose valid chains do not meet, with length `1` on the
arc from each node to its parent and offset `0` at the targets, the distance from the virtual source
at the node `i` valid steps above a target is `i`. -/
theorem Net.ExactSpec.dsrcTop_pos {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {t : V} {i : ℕ} (ht : isT t = true) (hs : Net.ParSteps r t i) :
    N.dsrcTop (Net.markLenW r fun _ => 1) (Net.markOffB isT) ((Net.parOf r)^[i] t) = i := by
  rw [h.dsrcTop_markW]
  apply le_antisymm
  · refine iInf_le_of_le t (iInf_le_of_le ht (iInf_le_of_le i (iInf_le_of_le ⟨hs, rfl⟩ (le_of_eq ?_))))
    simp
  · refine le_iInf fun t' => le_iInf fun ht' => le_iInf fun i' => le_iInf fun ⟨hs', hx⟩ => ?_
    obtain rfl : t' = t := hT t' t i' i ht' ht hs' hs hx
    obtain rfl : i' = i := h.parSteps_inj hs' hs hx
    simp

end Congest

end SsspFlow
