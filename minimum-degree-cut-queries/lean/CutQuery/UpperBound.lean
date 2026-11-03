import CutQuery.Model

/-!
# The classical upper bound

Querying every singleton computes the minimum degree with `n` deterministic queries.
-/

open Finset

namespace CutQuery

variable {n : ℕ}

/-- The query set `{v}`. -/
def singleton (v : Fin n) : Fin n → Bool := fun w => decide (w = v)

theorem cut_singleton (A : Weights n) (v : Fin n) : cut A (singleton v) = degree A v := by
  unfold cut degree
  refine sum_congr rfl fun e _ => ?_
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  by_cases h1 : e.1.1 = v
  · have h2 : e.1.2 ≠ v := fun h => hne (h1.trans h.symm)
    simp [crosses, singleton, h1, h2]
  · by_cases h2 : e.1.2 = v
    · simp [crosses, singleton, h1, h2]
    · simp [crosses, singleton, h1, h2]

/-- The algorithm: query the singleton of the next vertex, and output the smallest answer. -/
def singletonAlg (n : ℕ) [NeZero n] : DetAlg n where
  query l := singleton (Fin.ofNat n l.length)
  output l := if h : l.toFinset.Nonempty then l.toFinset.min' h else 0

theorem answers_singleton [NeZero n] (A : Weights n) (t : ℕ) :
    (singletonAlg n).answers A t = (List.range t).map fun i => degree A (Fin.ofNat n i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlen : ((singletonAlg n).answers A t).length = t := by rw [ih]; simp
    rw [DetAlg.answers, List.range_succ, List.map_append, ← ih]
    simp only [List.map_cons, List.map_nil]
    congr 2
    change cut A (singleton (Fin.ofNat n ((singletonAlg n).answers A t).length)) = _
    rw [hlen, cut_singleton]

/-- `n` singleton queries compute the minimum degree exactly. -/
theorem singleton_upper_bound (n : ℕ) [NeZero n] :
    ∃ alg : DetAlg n, ∀ A : Weights n, alg.run n A = minDegree A := by
  refine ⟨singletonAlg n, fun A => ?_⟩
  have hset : ((singletonAlg n).answers A n).toFinset = univ.image (degree A) := by
    ext y
    simp only [answers_singleton, List.mem_toFinset, List.mem_map, List.mem_range, mem_image, mem_univ,
      true_and]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      refine ⟨v.1, v.2, ?_⟩
      congr 1
      exact Fin.ext (by simp [Fin.ofNat, Nat.mod_eq_of_lt v.2])
  have hne : ((singletonAlg n).answers A n).toFinset.Nonempty := by
    rw [hset]
    exact ⟨degree A 0, mem_image_of_mem _ (mem_univ _)⟩
  change (if h : ((singletonAlg n).answers A n).toFinset.Nonempty then
      ((singletonAlg n).answers A n).toFinset.min' h else 0) = _
  simp only [hne, ↓reduceDIte]
  apply le_antisymm
  · refine le_inf' _ _ fun v _ => min'_le _ _ ?_
    rw [hset]
    exact mem_image_of_mem _ (mem_univ _)
  · have hmem := hset.subset (min'_mem _ hne)
    rw [mem_image] at hmem
    obtain ⟨v, _, hv⟩ := hmem
    rw [← hv]
    exact inf'_le _ (mem_univ v)

end CutQuery
