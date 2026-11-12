import Dominators.Lemma2

/-!
# Lemma 3: strong bridges and strong articulation points from two flow graphs

`G` is strongly connected and finite, with a chosen vertex `s`. The reduction of Theorem 3 from a general graph
to its components is `isStrongBridge_iff_mutual` and `isSAP_iff_separates`.
-/

namespace Dominators

universe u

variable {V : Type u} [Finite V] {E : V → V → Prop}

/-- For a nonempty finite graph with one component, the count of a subgraph on the same vertices rises iff the
subgraph is not strongly connected. -/
theorem not_strongConn_delEdge_iff (hS : StrongConn E) (u v : V) :
    sccCount E < sccCount (delEdge E u v) ↔ ¬ StrongConn (delEdge E u v) := by
  rw [sccCount_delEdge_lt_iff]
  constructor
  · rintro ⟨x, y, _, hn⟩ hC
    exact hn ⟨hC x y, hC y x⟩
  · intro hn
    simp only [StrongConn, not_forall] at hn
    obtain ⟨x, y, hxy⟩ := hn
    exact ⟨x, y, ⟨hS x y, hS y x⟩, fun h => hxy h.1⟩

/-- **Lemma 3, edges.** In a strongly connected graph, with any `s`, an edge is a strong bridge iff it is a
bridge of the flow graph of `G` from `s`, or of the reverse graph from `s`. -/
theorem lemma3_edge (hS : StrongConn E) (s : V) {u v : V} :
    IsStrongBridge E u v ↔ IsBridge E s u v ∨ IsBridge (rev E) s v u := by
  rw [IsStrongBridge, not_strongConn_delEdge_iff hS]
  constructor
  · rintro ⟨huv, hn⟩
    by_cases hf : Reach (delEdge E u v) s v
    · by_cases hb : Reach (delEdge E u v) u s
      · -- every vertex reaches and is reached from `s` avoiding the edge
        exfalso
        apply hn
        have hto : ∀ x, Reach (delEdge E u v) s x := by
          intro x
          rcases reach_delEdge_or (u := u) (v := v) (hS s x) with h | h
          · exact h
          · exact hf.trans h
        have hfrom : ∀ x, Reach (delEdge E u v) x s := by
          intro x
          rcases reach_delEdge_or' (u := u) (v := v) (hS x s) with h | ⟨h1, _⟩
          · exact h
          · -- `x` reaches `u` in `E`: cut that walk at the edge too, and go on from `u` to `s`
            have : ∀ {a b : V}, Reach E a b → Reach (delEdge E u v) a b ∨ Reach (delEdge E u v) a u := by
              intro a b ⟨p⟩
              induction p with
              | nil c => exact Or.inl (Reach.refl _ c)
              | @cons a c b hac p ih =>
                by_cases he : a = u ∧ c = v
                · exact Or.inr (he.1 ▸ Reach.refl _ _)
                · rcases ih with h | h
                  · exact Or.inl (Reach.head ⟨hac, he⟩ h)
                  · exact Or.inr (Reach.head ⟨hac, he⟩ h)
            rcases this (hS x s) with h | h
            · exact h
            · exact h.trans hb
        exact fun x y => (hfrom x).trans (hto y)
      · right
        refine ⟨huv, reach_rev.mpr (hS u s), ?_⟩
        rw [onAllPaths_iff_not_reach_delEdge, ← rev_delEdge, reach_rev]
        exact hb
    · left
      exact ⟨huv, hS s v, onAllPaths_iff_not_reach_delEdge.mpr hf⟩
  · rintro (⟨huv, _, ho⟩ | ⟨huv, _, ho⟩)
    · exact ⟨huv, fun hC => onAllPaths_iff_not_reach_delEdge.mp ho (hC s v)⟩
    · refine ⟨huv, fun hC => ?_⟩
      rw [onAllPaths_iff_not_reach_delEdge, ← rev_delEdge, reach_rev] at ho
      exact ho (hC u s)

/-- In a strongly connected graph, `d` is a strong articulation point iff two other vertices no longer reach
each other in `G - d`. -/
theorem isSAP_iff_of_strongConn (hS : StrongConn E) (d : V) :
    IsSAP E d ↔ ¬ StrongConn (delVertex E d) := by
  rw [IsSAP, sccCount_delVertex_lt_iff]
  constructor
  · rintro ⟨x, y, _, hn⟩ hC
    exact hn ⟨hC x y, hC y x⟩
  · intro hn
    simp only [StrongConn, not_forall] at hn
    obtain ⟨x, y, hxy⟩ := hn
    exact ⟨x, y, ⟨hS _ _, hS _ _⟩, fun h => hxy h.1⟩

/-- **Lemma 3, vertices.** In a strongly connected graph, a vertex `v ≠ s` is a strong articulation point iff
it dominates some other vertex in the flow graph of `G` from `s`, or of the reverse graph from `s`. -/
theorem lemma3_vertex (hS : StrongConn E) {s v : V} (hv : v ≠ s) :
    IsSAP E v ↔ ∃ w, w ≠ v ∧ (Dominates E s v w ∨ Dominates (rev E) s v w) := by
  rw [isSAP_iff_of_strongConn hS]
  constructor
  · intro hn
    by_contra hno
    push Not at hno
    apply hn
    have hto : ∀ x : {a : V // a ≠ v}, Reach (delVertex E v) ⟨s, Ne.symm hv⟩ x := by
      intro x
      have := (hno x.1 x.2).1
      obtain ⟨p, hp⟩ := not_dominates_iff.mp this
      exact reach_delVertex_iff.mpr ⟨p, hp⟩
    have hfrom : ∀ x : {a : V // a ≠ v}, Reach (delVertex E v) x ⟨s, Ne.symm hv⟩ := by
      intro x
      have := (hno x.1 x.2).2
      obtain ⟨p, hp⟩ := not_dominates_iff.mp this
      refine reach_delVertex_iff.mpr ⟨p.reverse, ?_⟩
      rw [Walk.mem_support_reverse]
      exact hp
    exact fun x y => (hfrom x).trans (hto y)
  · rintro ⟨w, hw, h | h⟩ hC
    · have hc := hC ⟨s, Ne.symm hv⟩ ⟨w, hw⟩
      obtain ⟨p, hp⟩ := reach_delVertex_iff.mp hc
      exact hp (h p)
    · have hc := hC ⟨w, hw⟩ ⟨s, Ne.symm hv⟩
      obtain ⟨p, hp⟩ := reach_delVertex_iff.mp hc
      apply hp
      have := h p.reverse
      rwa [Walk.mem_support_reverse] at this

/-- The test of `s` itself: it is a strong articulation point iff `G - s` is not strongly connected. Two
searches from any vertex of `G - s`, one in each direction, decide this. -/
theorem isSAP_self_iff (hS : StrongConn E) {s : V} (t : {a : V // a ≠ s}) :
    IsSAP E s ↔
      ¬ ((∀ x, Reach (delVertex E s) t x) ∧ (∀ x, Reach (rev (delVertex E s)) t x)) := by
  rw [isSAP_iff_of_strongConn hS]
  constructor
  · intro hn ⟨h1, h2⟩
    exact hn fun x y => (reach_rev.mp (h2 x)).trans (h1 y)
  · intro hn hC
    exact hn ⟨fun x => hC t x, fun x => reach_rev.mpr (hC x t)⟩

/-! ## Reduction to components (Theorem 3) -/

/-- An edge between two components changes nothing: only an edge inside a component can be a strong bridge. -/
theorem IsStrongBridge.mutual {u v : V} (h : IsStrongBridge E u v) : Mutual E u v := by
  obtain ⟨huv, hlt⟩ := h
  obtain ⟨x, y, hm, hn⟩ := (sccCount_delEdge_lt_iff u v).mp hlt
  by_contra hno
  apply hn
  have key : ∀ {a b : V}, Reach E a b → Reach E b a → Reach (delEdge E u v) a b := by
    intro a b hab hba
    rcases reach_delEdge_or' (u := u) (v := v) hab with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      apply hno
      refine ⟨Reach.edge huv, ?_⟩
      have h3 : Reach E v b := h2.mono (delEdge_le E u v)
      exact h3.trans (hba.trans h1)
  exact ⟨key hm.1 hm.2, key hm.2 hm.1⟩

/-- Theorem 3's reduction for edges: `(u, v)` is a strong bridge iff it is an edge inside a component that its
removal separates. -/
theorem isStrongBridge_iff_mutual {u v : V} :
    IsStrongBridge E u v ↔
      E u v ∧ Mutual E u v ∧ ∃ x y, Mutual E x u ∧ Mutual E y u ∧ ¬ Mutual (delEdge E u v) x y := by
  constructor
  · intro h
    have hm := h.mutual
    refine ⟨h.1, hm, ?_⟩
    obtain ⟨x, y, hxy, hn⟩ := (sccCount_delEdge_lt_iff u v).mp h.2
    -- a separated pair must use the edge in one direction, so it lies in the class of `u`
    have key : ∀ {a b : V}, Reach E a b → Reach E b a → ¬ Reach (delEdge E u v) a b → Mutual E a u := by
      intro a b hab hba hn'
      rcases reach_delEdge_or' (u := u) (v := v) hab with h1 | ⟨h1, h2⟩
      · exact absurd h1 hn'
      · exact ⟨h1, (Reach.edge h.1).trans ((h2.mono (delEdge_le E u v)).trans hba)⟩
    by_cases h1 : Reach (delEdge E u v) x y
    · have h2 : ¬ Reach (delEdge E u v) y x := fun h2 => hn ⟨h1, h2⟩
      have hy := key hxy.2 hxy.1 h2
      have hx : Mutual E x u := ⟨hxy.1.trans hy.1, hy.2.trans hxy.2⟩
      exact ⟨x, y, hx, hy, hn⟩
    · have hx := key hxy.1 hxy.2 h1
      have hy : Mutual E y u := ⟨hxy.2.trans hx.1, hx.2.trans hxy.1⟩
      exact ⟨x, y, hx, hy, hn⟩
  · rintro ⟨huv, _, x, y, hx, hy, hn⟩
    exact ⟨huv, (sccCount_delEdge_lt_iff u v).mpr
      ⟨x, y, ⟨hx.1.trans hy.2, hy.1.trans hx.2⟩, hn⟩⟩

/-- Theorem 3's reduction for vertices: `d` is a strong articulation point iff `G - d` separates two vertices
of the component of `d`. A vertex alone in its component has no such pair, and is no such point. -/
theorem isSAP_iff_separates {d : V} :
    IsSAP E d ↔ ∃ x y : {a : V // a ≠ d},
      Mutual E x.1 d ∧ Mutual E y.1 d ∧ ¬ Mutual (delVertex E d) x y := by
  rw [IsSAP, sccCount_delVertex_lt_iff]
  have key : ∀ {a b : {t : V // t ≠ d}}, Reach E a.1 b.1 → Reach E b.1 a.1 →
      ¬ Reach (delVertex E d) a b → Mutual E a.1 d := by
    intro a b hab hba hn
    obtain ⟨p⟩ := hab
    rcases reach_avoid_or d p with h | ⟨h1, h2⟩
    · exact absurd (reach_delVertex_iff.mpr ⟨p, h⟩) hn
    · exact ⟨h1, h2.trans hba⟩
  constructor
  · rintro ⟨x, y, hm, hn⟩
    by_cases h1 : Reach (delVertex E d) x y
    · have h2 : ¬ Reach (delVertex E d) y x := fun h2 => hn ⟨h1, h2⟩
      have hy := key hm.2 hm.1 h2
      exact ⟨x, y, ⟨hm.1.trans hy.1, hy.2.trans hm.2⟩, hy, hn⟩
    · have hx := key hm.1 hm.2 h1
      exact ⟨x, y, hx, ⟨hm.2.trans hx.1, hx.2.trans hm.1⟩, hn⟩
  · rintro ⟨x, y, hx, hy, hn⟩
    exact ⟨x, y, ⟨hx.1.trans hy.2, hy.1.trans hx.2⟩, hn⟩

end Dominators
