import Mathlib

/-!
# Sides of small cuts in simple digraphs

In a digraph without loops in which every vertex has out-degree at least `δ`, a nonempty vertex set
`S` with fewer than `δ` arcs leaving it has at least `δ + 1` vertices. Applied to the reversed
digraph, the same holds for the complement of `S` with in-degrees.
-/

namespace MaxFlowOR

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The arcs leaving `S`. -/
def leaving (adj : V → V → Prop) [DecidableRel adj] (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (Finset.univ \ S)).filter (fun p => adj p.1 p.2)

theorem card_leaving (adj : V → V → Prop) [DecidableRel adj] (S : Finset V) :
    (leaving adj S).card = ∑ u ∈ S, ((Finset.univ \ S).filter (adj u)).card := by
  classical
  unfold leaving
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.card_filter]

/-- Lemma 5: a nonempty set with fewer than `δ` leaving arcs has at least `δ + 1` vertices. -/
theorem side_large (adj : V → V → Prop) [DecidableRel adj] (hirr : ∀ v, ¬ adj v v) (δ : ℕ)
    (hout : ∀ u, δ ≤ (Finset.univ.filter (adj u)).card) (S : Finset V) (hS : S.Nonempty)
    (hsmall : (leaving adj S).card < δ) : δ + 1 ≤ S.card := by
  classical
  by_contra hcon
  push Not at hcon
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hS
  have hu : ∀ u ∈ S, δ + 1 ≤ S.card + ((Finset.univ \ S).filter (adj u)).card := by
    intro u hu
    have hsub : Finset.univ.filter (adj u) ⊆ S.erase u ∪ (Finset.univ \ S).filter (adj u) := by
      intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      by_cases hvS : v ∈ S
      · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hvS⟩)
        rintro rfl; exact hirr _ hv'
      · exact Finset.mem_union_right _ (by simp [hvS, hv'])
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S.erase u) ((Finset.univ \ S).filter (adj u))
    have h3 := Finset.card_erase_of_mem hu
    have h4 := hout u
    omega
  have hsum : S.card * (δ + 1) ≤ S.card * S.card + (leaving adj S).card := by
    rw [card_leaving]
    have := Finset.sum_le_sum hu
    simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at this
    linarith
  have hfac : S.card * S.card + δ ≤ S.card * (δ + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, S.card = t + 1 := ⟨S.card - 1, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, δ = S.card + e := ⟨δ - S.card, by omega⟩
    rw [he, ht]; nlinarith
  omega

end MaxFlowOR
