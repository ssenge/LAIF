import Mathlib

/-!
# Vertex connectivity: the neighbourhood lemmas

A graph is given by a neighbourhood function `N : V → Finset V`. For a vertex set `L`,
`nbhd N L = (⋃_{v ∈ L} N v) \ L`. These are Lemmas 4 and 5 of the folder
`laif/vertex-connectivity-matrix-queries`.
-/

namespace VertexConn

variable {V : Type*} [DecidableEq V]

/-- The open neighbourhood of a vertex set: neighbours of its members outside the set. -/
def nbhd (N : V → Finset V) (L : Finset V) : Finset V := L.biUnion N \ L

/-- The symmetric difference of two finite sets, written out. -/
def sdiffs (A B : Finset V) : Finset V := (A \ B) ∪ (B \ A)

lemma nbhd_singleton (N : V → Finset V) (hirr : ∀ v, v ∉ N v) (u : V) :
    nbhd N {u} = N u := by
  ext x; simp only [nbhd, Finset.singleton_biUnion, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, fun e => hirr u (e ▸ h)⟩

lemma card_sdiffs_add (A B : Finset V) :
    (sdiffs A B).card + 2 * A.card + 2 * B.card = 2 * (A ∪ B).card + A.card + B.card := by
  have h1 : (sdiffs A B).card = (A \ B).card + (B \ A).card :=
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  have h2 := Finset.card_sdiff_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_inter B A
  have h4 := Finset.card_union_add_card_inter A B
  rw [Finset.inter_comm] at h3
  omega

/-- **Lemma 4.** If `L ⊆ U` is nonempty and its neighbourhood is smallest among the nonempty subsets
of `U`, then any two members of `L` have neighbourhoods differing in at most `2|L|` vertices. -/
theorem twin_bound (N : V → Finset V) (hirr : ∀ v, v ∉ N v) (U L : Finset V) (hLU : L ⊆ U)
    (hmin : ∀ L' ⊆ U, L'.Nonempty → (nbhd N L).card ≤ (nbhd N L').card)
    {u v : V} (hu : u ∈ L) (hv : v ∈ L) :
    (sdiffs (N u) (N v)).card ≤ 2 * L.card := by
  have hNu : (nbhd N L).card ≤ (N u).card := by
    have := hmin {u} (by simpa using hLU hu) (Finset.singleton_nonempty u)
    rwa [nbhd_singleton N hirr] at this
  have hNv : (nbhd N L).card ≤ (N v).card := by
    have := hmin {v} (by simpa using hLU hv) (Finset.singleton_nonempty v)
    rwa [nbhd_singleton N hirr] at this
  have hsub : N u ∪ N v ⊆ L ∪ nbhd N L := by
    intro x hx
    by_cases hxL : x ∈ L
    · exact Finset.mem_union_left _ hxL
    · apply Finset.mem_union_right
      simp only [nbhd, Finset.mem_sdiff, Finset.mem_biUnion]
      rcases Finset.mem_union.1 hx with h | h
      · exact ⟨⟨u, hu, h⟩, hxL⟩
      · exact ⟨⟨v, hv, h⟩, hxL⟩
  have hc := Finset.card_le_card hsub
  have hcu := Finset.card_union_le L (nbhd N L)
  have key := card_sdiffs_add (N u) (N v)
  omega

/-- **Lemma 5.** For a set `C` and a vertex `c` (in the application a centre `c ∈ C`) and `D = ⋃_{v ∈ C} (N c △ N v)`, every nonempty
`L ⊆ C` has the same neighbours as `c` outside `D ∪ C`. -/
theorem cluster_outside (N : V → Finset V) (C : Finset V) (c : V)
    (L : Finset V) (hLC : L ⊆ C) (hL : L.Nonempty) :
    nbhd N L \ (C.biUnion (fun v => sdiffs (N c) (N v)) ∪ C) =
      N c \ (C.biUnion (fun v => sdiffs (N c) (N v)) ∪ C) := by
  have same : ∀ v ∈ C, ∀ x, x ∉ C.biUnion (fun w => sdiffs (N c) (N w)) → (x ∈ N v ↔ x ∈ N c) := by
    intro v hvC x hx
    simp only [Finset.mem_biUnion, sdiffs, Finset.mem_union, Finset.mem_sdiff, not_exists,
      not_and] at hx
    have := hx v hvC
    tauto
  ext x
  simp only [nbhd, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, not_or]
  constructor
  · rintro ⟨⟨⟨v, hvL, hxv⟩, -⟩, hD, hC⟩
    refine ⟨(same v (hLC hvL) x ?_).1 hxv, hD, hC⟩
    simpa [Finset.mem_biUnion] using hD
  · rintro ⟨hxc, hD, hC⟩
    obtain ⟨v, hvL⟩ := hL
    refine ⟨⟨⟨v, hvL, (same v (hLC hvL) x ?_).2 hxc⟩, fun h => hC (hLC h)⟩, hD, hC⟩
    simpa [Finset.mem_biUnion] using hD

/-- **Lemma 5, counting form.** `|N(L)| = a_C + |N(L) ∩ (D ∪ C)|`, where `a_C = |N c \ (D ∪ C)|`
does not depend on `L`. -/
theorem cluster_card (N : V → Finset V) (C : Finset V) (c : V)
    (L : Finset V) (hLC : L ⊆ C) (hL : L.Nonempty) :
    (nbhd N L).card = (N c \ (C.biUnion (fun v => sdiffs (N c) (N v)) ∪ C)).card +
      (nbhd N L ∩ (C.biUnion (fun v => sdiffs (N c) (N v)) ∪ C)).card := by
  rw [← cluster_outside N C c L hLC hL, Finset.card_sdiff_add_card_inter]

end VertexConn
