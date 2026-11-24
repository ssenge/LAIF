import Mathlib

/-!
# Search by sampling a fugacity-weighted distribution never beats listing

Let `s` be a finite family of feasible configurations (for example the independent sets of a graph), `f x` the
size of `x`, `m` the optimum size and `opt ⊆ s` the optimal configurations. Sampling `x` with probability
`t ^ f x / Z`, where `Z = ∑ x ∈ s, t ^ f x`, hits `opt` with probability `π = opt.card * t ^ m / Z`, so the
expected number of samples is `1 / π`. For `0 < t ≤ 1` this is at least `s.card / opt.card`: up to the number of
optima, the search draws at least as many samples as there are feasible configurations.
-/

open Finset

namespace ChainSearch

/-- For a fugacity `0 < t ≤ 1`, the number of feasible configurations is at most the number of optima times
the expected number of samples `Z / (opt.card * t ^ m)` needed to hit an optimum. -/
theorem card_le_card_opt_mul_samples {α : Type*} (s opt : Finset α) (f : α → ℕ) (m : ℕ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hf : ∀ x ∈ s, f x ≤ m) (hne : opt.Nonempty) :
    (s.card : ℝ) ≤ opt.card * ((∑ x ∈ s, t ^ f x) / (opt.card * t ^ m)) := by
  have hc : (0 : ℝ) < opt.card := by exact_mod_cast hne.card_pos
  have hm : (0 : ℝ) < t ^ m := pow_pos ht0 m
  have key : (s.card : ℝ) ≤ (∑ x ∈ s, t ^ f x) / t ^ m := by
    rw [le_div_iff₀ hm, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx => ?_
    simpa using pow_le_pow_of_le_one ht0.le ht1 (hf x hx)
  calc (s.card : ℝ) ≤ (∑ x ∈ s, t ^ f x) / t ^ m := key
    _ = opt.card * ((∑ x ∈ s, t ^ f x) / (opt.card * t ^ m)) := by field_simp

/-- The same bound for the independent sets of a finite simple graph, with the hardcore weights `t ^ |x|`. -/
theorem indepSets_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    let s : Finset (Finset V) := Finset.univ.filter (fun x : Finset V => G.IsIndepSet (↑x : Set V))
    let m := s.sup Finset.card
    let opt := s.filter (fun x => x.card = m)
    (s.card : ℝ) ≤ opt.card * ((∑ x ∈ s, t ^ x.card) / (opt.card * t ^ m)) := by
  intro s m opt
  have hs : s.Nonempty := ⟨∅, by simp [s, SimpleGraph.IsIndepSet]⟩
  obtain ⟨y, hy, hym⟩ := Finset.exists_mem_eq_sup s hs Finset.card
  have hne : opt.Nonempty := ⟨y, by simp [opt, hy, m, hym]⟩
  exact card_le_card_opt_mul_samples s opt Finset.card m t ht0 ht1 (fun x hx => Finset.le_sup hx) hne

end ChainSearch
