import SsspFlow.OracleChainPos

/-!
# Counting along the parent chains of an oracle

For targets whose valid chains do not meet, one more run of the oracle with length `f a` on the arc
from each node `a` to its parent gives every node of a chain the sum of `f` over the nodes below it
on the chain of its target. With `f` the indicator of a flag, this sum is `0` exactly when no node
below is flagged, so the first flagged node of each chain knows that it is the first.

* `Net.ExactSpec.dsrcTop_sum`: the distance for the lengths `f` on the arcs to the parents is the sum
  of `f` below the node on its chain.
* `Net.ExactSpec.dsrcTop_flag_eq_zero`: for the indicator of a flag, the distance is `0` exactly when
  no node below is flagged.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- **Sums along the chains.** For targets whose valid chains do not meet, with length `f a` on the
arc from each node `a` to its parent and offset `0` at the targets, the distance at the node `i`
valid steps above a target is the sum of `f` over the nodes `0, …, i - 1` steps above it. -/
theorem Net.ExactSpec.dsrcTop_sum {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (f : V → ℕ∞) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {t : V} {i : ℕ} (ht : isT t = true) (hs : Net.ParSteps r t i) :
    N.dsrcTop (Net.markLenW r f) (Net.markOffB isT) ((Net.parOf r)^[i] t) =
      ((∑ k ∈ Finset.range i, f ((Net.parOf r)^[k] t) : ℕ∞) : ℝ≥0∞) := by
  rw [h.dsrcTop_markW]
  apply le_antisymm
  · exact iInf_le_of_le t (iInf_le_of_le ht (iInf_le_of_le i (iInf_le_of_le ⟨hs, rfl⟩ le_rfl)))
  · refine le_iInf fun t' => le_iInf fun ht' => le_iInf fun i' => le_iInf fun ⟨hs', hx⟩ => ?_
    obtain rfl : t' = t := hT t' t i' i ht' ht hs' hs hx
    obtain rfl : i' = i := h.parSteps_inj hs' hs hx
    exact le_rfl

open Classical in
/-- **The first flagged node.** For the indicator of a flag `P` as lengths on the arcs to the parents,
the distance at the node `i` valid steps above a target is `0` exactly when no node `0, …, i - 1`
steps above the target is flagged. -/
theorem Net.ExactSpec.dsrcTop_flag_eq_zero {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞}
    {r : V → ℕ∞ × Option V} (h : N.ExactSpec ℓ φ r) (P : V → Prop) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {t : V} {i : ℕ} (ht : isT t = true) (hs : Net.ParSteps r t i) :
    N.dsrcTop (Net.markLenW r fun a => if P a then 1 else 0) (Net.markOffB isT) ((Net.parOf r)^[i] t) = 0 ↔
      ∀ k < i, ¬ P ((Net.parOf r)^[k] t) := by
  rw [h.dsrcTop_sum _ isT hT ht hs]
  rw [← ENat.toENNReal_zero, ENat.toENNReal_inj, Finset.sum_eq_zero_iff]
  refine forall_congr' fun k => ?_
  rw [Finset.mem_range]
  refine imp_congr_right fun _ => ?_
  split_ifs with hP
  · simp [hP]
  · simp [hP]

end Congest

end SsspFlow
