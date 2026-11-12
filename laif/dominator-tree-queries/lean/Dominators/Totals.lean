import Dominators.Cost
import Dominators.LengauerTarjan

/-!
# Theorem 2's minimum findings, on the algorithm itself

The semidominator pass of `LengauerTarjan.lean` calls minimum finding once for each reachable non-root vertex.
So the number of calls is at most `n`, and the charges sum to at most `√(n m)`. The bridge test of `README.md` runs
over the same vertices with the same charge.
-/

namespace Dominators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {E : V → V → Prop} {r : V} {T : DfsTree V}

omit [Fintype V] in
/-- The vertices at which minimum finding is called have no repetition. -/
theorem IsDfsTree.calls_nodup (hT : IsDfsTree E r T) : (T.order.filter (· ≠ r)).Nodup := by
  have h : T.order.Nodup := hT.sorted.imp (fun {a b} hab e => by subst e; exact lt_irrefl _ hab)
  exact h.filter _

/-- At most `n` minimum findings. -/
theorem minFind_calls_le (hT : IsDfsTree E r T) : (T.order.filter (· ≠ r)).length ≤ Fintype.card V :=
  hT.calls_nodup.length_le_card

/-- **The charge of the semidominator pass.** With charge `√(deg⁻ w)` per call, the total is at most `√(n m)`. -/
theorem minFind_charge_le (hT : IsDfsTree E r T) :
    ((T.order.filter (· ≠ r)).map fun w => Real.sqrt (inDeg E w)).sum ≤
      Real.sqrt (Fintype.card V * edgeCount E) := by
  rw [← List.sum_toFinset _ hT.calls_nodup]
  refine le_trans ?_ (sum_sqrt_inDeg_le E)
  exact Finset.sum_le_univ_sum_of_nonneg fun _ => Real.sqrt_nonneg _

end Dominators
