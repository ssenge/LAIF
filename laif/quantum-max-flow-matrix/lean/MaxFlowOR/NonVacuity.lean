import MaxFlowOR.Levels
import MaxFlowOR.Sum
import MaxFlowOR.DirCut

/-!
# Non-vacuity

The hypotheses of the main lemmas hold on small instances, and the cut bound is tight there.
-/

namespace MaxFlowOR

/-- Levels of sizes `1, 2, 1, 2, 1` (total `7`, `d = 4`) satisfy the hypothesis of
`exists_small_pair`, and the factor `2` cannot be dropped: no two consecutive levels both have
`d · size ≤ n`. -/
example : ∑ i ∈ Finset.range (4 + 1), [1, 2, 1, 2, 1].getD i 0 ≤ 7 ∧
    (∃ i < 4, 4 * [1, 2, 1, 2, 1].getD i 0 ≤ 2 * 7 ∧ 4 * [1, 2, 1, 2, 1].getD (i + 1) 0 ≤ 2 * 7) ∧
    ¬ ∃ i < 4, 4 * [1, 2, 1, 2, 1].getD i 0 ≤ 7 ∧ 4 * [1, 2, 1, 2, 1].getD (i + 1) 0 ≤ 7 := by
  decide

/-- Two vertices on levels `0` and `1` with residual capacity `2`: the cut bound holds with
equality. -/
example : ∑ p ∈ (Finset.univ.filter (fun u : Fin 2 => (u : ℕ) ≤ 0)) ×ˢ
      (Finset.univ.filter (fun v : Fin 2 => ¬ (v : ℕ) ≤ 0)),
      (fun u v : Fin 2 => if u = 0 ∧ v = 1 then 2 else 0) p.1 p.2
    = 2 * ((Finset.univ.filter (fun u : Fin 2 => (u : ℕ) = 0)).card *
      (Finset.univ.filter (fun v : Fin 2 => (v : ℕ) = 0 + 1)).card) := by decide

/-- Without the rise condition the cut bound fails: with levels `0, 3, 2` on three vertices, a
capacity-`2` arc from level `0` to level `2` crosses the cut after level `0`, while level `1` is
empty. -/
example : ¬ (∑ p ∈ (Finset.univ.filter (fun u : Fin 3 => ![0, 3, 2] u ≤ 0)) ×ˢ
      (Finset.univ.filter (fun v : Fin 3 => ¬ ![0, 3, 2] v ≤ 0)),
      (fun u v : Fin 3 => if u = 0 ∧ v = 2 then 2 else 0) p.1 p.2
    ≤ 2 * ((Finset.univ.filter (fun u : Fin 3 => ![0, 3, 2] u = 0)).card *
      (Finset.univ.filter (fun v : Fin 3 => ![0, 3, 2] v = 0 + 1)).card)) := by decide

/-- One phase with flow `1` on a path of length `1`: the hypotheses of `sum_FD_le` hold for
`f = n = K = 1`, `m = 0`. -/
example : ((∑ j ∈ ({0} : Finset ℕ), (fun _ => 1) j * (fun _ => 1) j : ℕ) : ℝ) ≤
    ((1 : ℕ) : ℝ) * 1 + 8 * 1 ^ 2 / ((1 : ℕ) : ℝ) :=
  sum_FD_le {0} (fun _ => 1) (fun _ => 1) 1 1 1 0 le_rfl (by simp)
    (fun d => by rcases d with _ | d <;> simp)
    (fun d => by
      rcases d with _ | d
      · norm_num
      · simp; positivity)

/-- The bound of `sum_FD_le` is not trivial: two phases of flow `1` with paths of length `1` and `2`
give `∑ F · D = 3`. -/
example : ∑ j ∈ ({0, 1} : Finset ℕ), (fun _ => 1) j * (fun j => j + 1) j = 3 := by decide

/-- Two complete digraphs on four vertices joined by one arc in each direction: every out-degree is
at least `3`, the first block has one leaving arc, and it has `4 = 3 + 1` vertices, so
`side_large` is tight. -/
def twoBlocks (u v : Fin 8) : Prop :=
  u ≠ v ∧ ((u.val < 4 ↔ v.val < 4) ∨ (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0))

instance : DecidableRel twoBlocks := fun u v => by unfold twoBlocks; infer_instance

example : (∀ v, ¬ twoBlocks v v) ∧ (∀ u, 3 ≤ (Finset.univ.filter (twoBlocks u)).card) ∧
    (leaving twoBlocks (Finset.univ.filter (fun v : Fin 8 => v.val < 4))).card = 1 ∧
    (Finset.univ.filter (fun v : Fin 8 => v.val < 4)).card = 3 + 1 := by decide

end MaxFlowOR
