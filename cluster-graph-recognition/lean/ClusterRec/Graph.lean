import Mathlib

/-!
# Cluster graphs, induced paths on three vertices, and a vertex with many witnesses

A cluster graph is a disjoint union of cliques: distinct vertices are adjacent exactly when they carry the same label.
`cluster_tfae` shows that this holds iff the graph has no induced path `a - b - c`, iff every edge joins two vertices
with the same closed neighbourhood. An edge whose ends have different closed neighbourhoods gives an induced path
(`p3_of_witness`). If an edge `xz` has ends with different closed neighbourhoods, then one of its ends has such a neighbour
for at least half of its neighbours (`good_end`), so every graph that is not a cluster graph has such a vertex
(`exists_good_vertex`).
-/

open Finset

namespace ClusterRec

section Defs

variable {V : Type*} (G : SimpleGraph V)

/-- Distinct vertices are adjacent iff they carry the same label. -/
def IsCluster : Prop := ∃ f : V → Set V, ∀ u v, u ≠ v → (G.Adj u v ↔ f u = f v)

/-- An induced path `a - b - c` with centre `b`. -/
def IsP3 (a b c : V) : Prop := G.Adj a b ∧ G.Adj b c ∧ a ≠ c ∧ ¬ G.Adj a c

variable {G} in
theorem not_cluster_of_p3 {a b c : V} (h : IsP3 G a b c) : ¬ IsCluster G := by
  rintro ⟨f, hf⟩
  obtain ⟨hab, hbc, hac, hnac⟩ := h
  have e1 := (hf a b hab.ne).1 hab
  have e2 := (hf b c hbc.ne).1 hbc
  exact hnac ((hf a c hac).2 (e1.trans e2))

end Defs

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighbourhood. -/
def cnb (x : V) : Finset V := insert x (G.neighborFinset x)

variable {G}

theorem mem_cnb {x w : V} : w ∈ cnb G x ↔ w = x ∨ G.Adj x w := by
  simp [cnb]

theorem card_cnb (x : V) : (cnb G x).card = G.degree x + 1 := by
  rw [cnb, card_insert_of_notMem (by simp), SimpleGraph.card_neighborFinset_eq_degree]

theorem cnb_eq_of_noP3 (h : ∀ a b c, ¬ IsP3 G a b c) {x z : V} (hxz : G.Adj x z) : cnb G x = cnb G z := by
  ext w
  simp only [mem_cnb]
  constructor
  · rintro (rfl | hxw)
    · exact Or.inr hxz.symm
    · by_cases hwz : w = z
      · exact Or.inl hwz
      · by_contra hz
        push Not at hz
        exact h w x z ⟨hxw.symm, hxz, hwz, fun hwz' => hz.2 hwz'.symm⟩
  · rintro (rfl | hzw)
    · exact Or.inr hxz
    · by_cases hwx : w = x
      · exact Or.inl hwx
      · by_contra hx
        push Not at hx
        exact h x z w ⟨hxz, hzw, fun e => hwx e.symm, hx.2⟩

theorem cluster_of_cnb (h : ∀ x z, G.Adj x z → cnb G x = cnb G z) : IsCluster G := by
  refine ⟨fun x => (cnb G x : Set V), fun u v huv => ⟨fun hadj => by simp only [h u v hadj], fun he => ?_⟩⟩
  have hv : v ∈ cnb G u := by rw [Finset.coe_inj.1 he, mem_cnb]; exact Or.inl rfl
  rcases mem_cnb.1 hv with e | hadj
  · exact absurd e.symm huv
  · exact hadj

/-- **Fact 1.** Three equivalent descriptions of cluster graphs. -/
theorem cluster_tfae :
    [IsCluster G, ∀ a b c, ¬ IsP3 G a b c, ∀ x z, G.Adj x z → cnb G x = cnb G z].TFAE := by
  tfae_have 1 → 2 := fun h a b c hp => not_cluster_of_p3 hp h
  tfae_have 2 → 3 := fun h x z hxz => cnb_eq_of_noP3 h hxz
  tfae_have 3 → 1 := cluster_of_cnb
  tfae_finish

/-- **Fact 2.** An edge `xz` and a vertex `w` outside it, adjacent to exactly one of `x, z`, give an induced path. -/
theorem p3_of_witness {x z w : V} (hxz : G.Adj x z) (hwx : w ≠ x) (hwz : w ≠ z)
    (hdiff : G.Adj x w ↔ ¬ G.Adj z w) : ∃ a b c, IsP3 G a b c := by
  by_cases hxw : G.Adj x w
  · exact ⟨z, x, w, hxz.symm, hxw, fun e => hwz e.symm, hdiff.1 hxw⟩
  · have hzw : G.Adj z w := by
      by_contra hzw
      exact hxw (hdiff.2 hzw)
    exact ⟨x, z, w, hxz, hzw, fun e => hwx e.symm, hxw⟩

/-- An edge whose ends have different closed neighbourhoods has a witness `w` outside it. -/
theorem witness_of_cnb_ne {x z : V} (hxz : G.Adj x z) (hne : cnb G x ≠ cnb G z) :
    ∃ w, w ≠ x ∧ w ≠ z ∧ (G.Adj x w ↔ ¬ G.Adj z w) := by
  by_contra hno
  apply hne
  ext w
  simp only [mem_cnb]
  by_cases hwx : w = x
  · subst hwx; simp [hxz.symm]
  by_cases hwz : w = z
  · subst hwz; simp [hxz]
  have h : ¬ (G.Adj x w ↔ ¬ G.Adj z w) := fun h' => hno ⟨w, hwx, hwz, h'⟩
  constructor
  · rintro (e | hxw)
    · exact absurd e hwx
    · right
      by_contra hzw
      exact h ⟨fun _ => hzw, fun _ => hxw⟩
  · rintro (e | hzw)
    · exact absurd e hwz
    · right
      by_contra hxw
      exact h ⟨fun hx => absurd hx hxw, fun hz => absurd hzw hz⟩

/-- The neighbours of `b` with the closed neighbourhood of `b`. -/
def same (b : V) : Finset V := (G.neighborFinset b).filter fun z => cnb G z = cnb G b

/-- The neighbours of `b` with a different closed neighbourhood. -/
def diff (b : V) : Finset V := (G.neighborFinset b).filter fun z => cnb G z ≠ cnb G b

theorem card_same_add_diff (b : V) : (same (G := G) b).card + (diff (G := G) b).card = G.degree b := by
  have := card_filter_add_card_filter_not (s := G.neighborFinset b) (fun z => cnb G z = cnb G b)
  simpa [same, diff, ne_eq, SimpleGraph.card_neighborFinset_eq_degree] using this

/-- Every neighbour of `x` that is a twin of `z` lies in `diff x`, and so does `z`, when `N[x] ≠ N[z]`. -/
theorem card_same_lt_diff {x z : V} (hxz : G.Adj x z) (hne : cnb G x ≠ cnb G z) :
    (same (G := G) z).card + 1 ≤ (diff (G := G) x).card := by
  have hsub : insert z (same (G := G) z) ⊆ diff (G := G) x := by
    intro y hy
    simp only [diff, mem_filter, SimpleGraph.mem_neighborFinset]
    rcases mem_insert.1 hy with rfl | hy
    · exact ⟨hxz, fun e => hne e.symm⟩
    · simp only [same, mem_filter, SimpleGraph.mem_neighborFinset] at hy
      obtain ⟨-, hyz⟩ := hy
      have hx : x ∈ cnb G y := by rw [hyz, mem_cnb]; exact Or.inr hxz.symm
      have hxy : x ≠ y := fun e => hne (by rw [e]; exact hyz)
      rcases mem_cnb.1 hx with e | hadj
      · exact absurd e hxy
      · exact ⟨hadj.symm, fun e => hne (e.symm.trans hyz)⟩
  have hz : z ∉ same (G := G) z := by simp [same]
  have := card_le_card hsub
  rwa [card_insert_of_notMem hz] at this

/-- **Lemma 3 (a good end).** If `xz` is an edge with `N[x] ≠ N[z]`, then `x` or `z` has the other end among its
neighbours with a different closed neighbourhood, and such neighbours make up at least half of its neighbours. -/
theorem good_end {x z : V} (hxz : G.Adj x z) (hne : cnb G x ≠ cnb G z) :
    (z ∈ diff (G := G) x ∧ G.degree x ≤ 2 * (diff (G := G) x).card) ∨
    (x ∈ diff (G := G) z ∧ G.degree z ≤ 2 * (diff (G := G) z).card) := by
  have h1 := card_same_lt_diff hxz hne
  have h2 := card_same_lt_diff hxz.symm (Ne.symm hne)
  have e1 := card_same_add_diff (G := G) x
  have e2 := card_same_add_diff (G := G) z
  have hzx : z ∈ diff (G := G) x := by
    simp only [diff, mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨hxz, fun e => hne e.symm⟩
  have hxz' : x ∈ diff (G := G) z := by
    simp only [diff, mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨hxz.symm, hne⟩
  by_cases h : G.degree x ≤ 2 * (diff (G := G) x).card
  · exact Or.inl ⟨hzx, h⟩
  · exact Or.inr ⟨hxz', by omega⟩

/-- **Detection.** A graph that is not a cluster graph has a vertex `x` with a neighbour of a different closed
neighbourhood, such that these neighbours make up at least half of the neighbours of `x`. -/
theorem exists_good_vertex (h : ¬ IsCluster G) :
    ∃ x, (diff (G := G) x).Nonempty ∧ G.degree x ≤ 2 * (diff (G := G) x).card := by
  have h3 : ¬ ∀ x z, G.Adj x z → cnb G x = cnb G z := fun h' => h (cluster_of_cnb h')
  push Not at h3
  obtain ⟨x, z, hxz, hne⟩ := h3
  rcases good_end hxz hne with ⟨hm, hd⟩ | ⟨hm, hd⟩
  · exact ⟨x, ⟨z, hm⟩, hd⟩
  · exact ⟨z, ⟨x, hm⟩, hd⟩

end ClusterRec
