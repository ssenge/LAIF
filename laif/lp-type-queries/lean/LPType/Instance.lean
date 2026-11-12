import LPType.Theorem1

/-!
# An instance: the maximum on a finite linear order

`f S = S.max`, with values in `WithBot H`, so that `f ∅ = ⊥`. This is an LP-type problem of
combinatorial dimension `1`, and Theorem 1's failure bound applies to it.

Smallest enclosing ball is not stated here.
-/

open Finset

namespace LPType

variable (H : Type*) [LinearOrder H]

/-- The problem `f = max` on a linear order. -/
def maxProblem : Problem H (WithBot H) where
  f S := S.max
  mono := Finset.max_mono
  locality := by
    intro F G h _ hval hlt
    rw [Finset.max_insert] at hlt ⊢
    rw [hval]
    exact hlt

variable {H}

/-- `h` violates `S` exactly when it exceeds all of `S`. -/
theorem maxProblem_violates_iff {h : H} {S : Finset H} :
    (maxProblem H).Violates h S ↔ S.max < (h : WithBot H) := by
  simp only [Problem.Violates, maxProblem, Finset.max_insert, lt_max_iff, lt_self_iff_false,
    or_false]

/-- A basis for `f = max` has at most one element. -/
theorem maxProblem_card_le_one {B S : Finset H} (hB : (maxProblem H).IsBasis B S) : #B ≤ 1 := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · simp
  · by_contra hcard
    have hmem := B.max'_mem hne
    have hss : ({B.max' hne} : Finset H) ⊂ B := by
      refine ⟨singleton_subset_iff.2 hmem, fun h => hcard ?_⟩
      have : #B ≤ #({B.max' hne} : Finset H) := card_le_card h
      simpa using this
    refine hB.2.2 _ hss ?_
    change ({B.max' hne} : Finset H).max = B.max
    rw [Finset.max_singleton, Finset.coe_max' hne]

/-- A singleton is a basis of itself, since `f ∅ = ⊥` is below every value. -/
theorem maxProblem_singleton_isBasis (a : H) : (maxProblem H).IsBasis {a} {a} := by
  refine ⟨Subset.rfl, rfl, fun B' hB' => ?_⟩
  have : B' = ∅ := by
    rcases Finset.ssubset_singleton_iff.1 hB' with rfl
    rfl
  subst this
  change (∅ : Finset H).max ≠ ({a} : Finset H).max
  simp [Finset.max_singleton]

/-- **`f = max` has combinatorial dimension `1`.** -/
theorem maxProblem_combDim [Fintype H] [Nonempty H] : (maxProblem H).combDim = 1 := by
  refine le_antisymm (Problem.combDim_le fun B S hB => maxProblem_card_le_one hB) ?_
  obtain ⟨a⟩ := ‹Nonempty H›
  have := (maxProblem_singleton_isBasis a).card_le
  simpa using this

/-- Theorem 1's failure bound for `f = max`, where `T = ⌈12 ln n⌉` and `s = 2`. -/
theorem maxProblem_failure_prob [Fintype H] [Nonempty H] {s' : ℝ} (hs' : 0 < s') (Z : ℝ) :
    ((maxProblem H).clarkson
        ((maxProblem H).two_mul_sq_pos maxProblem_combDim.ge) hs').prob
        ⌈12 * ((maxProblem H).combDim : ℝ) * Real.log (Fintype.card H)⌉₊
        (RoundState.init Z) (maxProblem H).NotStopped
      ≤ (Fintype.card H : ℝ) ^ (-1.3 : ℝ) :=
  (maxProblem H).failure_prob_le hs' maxProblem_combDim.ge Z

end LPType
