import SsspFlow.OracleChainDown

/-!
# The nodes between the two ends, read locally

After the counting run up the chains for a flag `F0` and the run down them for a flag `F1`, a node
knows whether it lies on the chain of a target strictly below the first node flagged by `F0` and not
below the last node up to it flagged by `F1`: its count is `0`, it is not flagged by `F0`, and its
distance in the run down the chains is `0`. No further run is needed.

* `Net.ExactSpec.step_iff`: for targets whose valid chains do not meet, a node meets these three
  local conditions exactly when it lies `l` valid steps above a target, below the first node `ia`
  flagged by `F0` and with no node `l + 1, …, ia` flagged by `F1`.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A nonzero value in `ℕ∞` is at least `1` in `[0, ∞]`. -/
theorem ENat.one_le_toENNReal {s : ℕ∞} (h : s ≠ 0) : (1 : ℝ≥0∞) ≤ (s : ℝ≥0∞) := by
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact Order.one_le_iff_ne_zero.2 h

open Classical in
/-- **The nodes between the two ends.** Let the valid chains of distinct targets not meet. A node has
count `0` in the counting run for `F0`, is not flagged by `F0`, and has distance `0` in the run down
the chains for `F1` from the nodes flagged by `F0` with count `0`, exactly when it is the node `l`
valid steps above a target `v` with `l < ia`, where `ia` is the first node above `v` flagged by
`F0`, and no node `l + 1, …, ia` steps above `v` is flagged by `F1`. -/
theorem Net.ExactSpec.step_iff {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (F0 F1 : V → Prop) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t') (w : V) :
    (N.dsrcTop (Net.markLenW r fun a => if F0 a then 1 else 0) (Net.markOffB isT) w = 0 ∧ ¬ F0 w ∧
      N.dsrcTop (Net.downLenW r fun a => if F1 a then 1 else 0)
        (Net.markOffB fun a => decide (F0 a ∧ N.dsrcTop (Net.markLenW r fun a => if F0 a then 1 else 0)
          (Net.markOffB isT) a = 0)) w = 0) ↔
      ∃ v l ia, isT v = true ∧ Net.ParSteps r v ia ∧ l < ia ∧ F0 ((Net.parOf r)^[ia] v) ∧
        (∀ m < ia, ¬ F0 ((Net.parOf r)^[m] v)) ∧ (∀ m, l < m → m ≤ ia → ¬ F1 ((Net.parOf r)^[m] v)) ∧
        w = (Net.parOf r)^[l] v := by
  constructor
  · rintro ⟨h0, hF, h1⟩
    rw [h.dsrcTop_markW] at h0
    obtain ⟨v, hv, l, ⟨hsl, rfl⟩, -⟩ : ∃ v, isT v = true ∧ ∃ l,
        (Net.ParSteps r v l ∧ (Net.parOf r)^[l] v = w) ∧
        (∑ k ∈ Finset.range l, (fun a => if F0 a then (1 : ℕ∞) else 0) ((Net.parOf r)^[k] v)) = 0 := by
      refine by_contra fun hne => absurd h0 (ne_of_gt (lt_of_lt_of_le zero_lt_one
        (le_iInf fun v => le_iInf fun hv => le_iInf fun l => le_iInf fun hp =>
          ENat.one_le_toENNReal fun hs => hne ⟨v, hv, l, hp, hs⟩)))
    have e : ∀ m, (Net.parOf r)^[m] ((Net.parOf r)^[l] v) = (Net.parOf r)^[l + m] v := fun m => by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    rw [h.dsrcTop_downW] at h1
    obtain ⟨j, ⟨hsj, hX⟩, hsum1⟩ : ∃ j, (Net.ParSteps r ((Net.parOf r)^[l] v) j ∧
        decide (F0 ((Net.parOf r)^[j] ((Net.parOf r)^[l] v)) ∧ N.dsrcTop (Net.markLenW r fun a =>
          if F0 a then 1 else 0) (Net.markOffB isT) ((Net.parOf r)^[j] ((Net.parOf r)^[l] v)) = 0) = true) ∧
        (∑ m ∈ Finset.range j, (fun a => if F1 a then (1 : ℕ∞) else 0)
          ((Net.parOf r)^[m + 1] ((Net.parOf r)^[l] v))) = 0 := by
      refine by_contra fun hne => absurd h1 (ne_of_gt (lt_of_lt_of_le zero_lt_one
        (le_iInf fun j => le_iInf fun hp => ENat.one_le_toENNReal fun hs => hne ⟨j, hp, hs⟩)))
    rw [decide_eq_true_iff, e] at hX
    obtain ⟨hX0, hXc⟩ := hX
    have hsa : Net.ParSteps r v (l + j) := Net.parSteps_add.2 ⟨hsl, hsj⟩
    have hbelow := (h.dsrcTop_flag_eq_zero F0 isT hT hv hsa).1 hXc
    have hj : j ≠ 0 := fun hj0 => by
      subst hj0
      exact hF hX0
    refine ⟨v, l, l + j, hv, hsa, by omega, hX0, hbelow, fun m h1m h2m hFm => ?_, rfl⟩
    have := (Finset.sum_eq_zero_iff.1 hsum1) (m - l - 1) (Finset.mem_range.2 (by omega))
    rw [e, show l + (m - l - 1 + 1) = m by omega] at this
    simp [hFm] at this
  · rintro ⟨v, l, ia, hv, hia, hl, h0, h0', h1', rfl⟩
    refine ⟨(h.dsrcTop_flag_eq_zero F0 isT hT hv fun k hk => hia k (by omega)).2
      fun k hk => h0' k (by omega), h0' l hl, ?_⟩
    exact (h.down_none_iff F0 F1 isT hT hv hia h0 h0' hl.le).2 h1'

end Congest

end SsspFlow
