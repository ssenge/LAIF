import Dominators.Lemma3

/-!
# Theorem 3: restricting Lemma 3 to a component

`isStrongBridge_comp` and `isSAP_comp`: removal only affects the component, so both notions can be read in the
graph induced on it. `theorem3_edge` and `theorem3_vertex` then apply Lemma 3 inside the component.
-/

namespace Dominators

universe u

variable {V : Type u} {E : V → V → Prop} {c : V}

/-- The vertices of the component of `c`. -/
abbrev CompV (E : V → V → Prop) (c : V) := {t : V // Mutual E c t}

/-- The graph induced on the component of `c`. -/
abbrev compGraph (E : V → V → Prop) (c : V) : CompV E c → CompV E c → Prop := fun x y => E x.1 y.1

/-- A walk between two vertices of a component stays in it. -/
theorem comp_walk {a b : V} (p : Walk E a b) (ha : Mutual E c a) (hb : Mutual E c b) :
    ∃ p' : Walk (compGraph E c) ⟨a, ha⟩ ⟨b, hb⟩,
      (∀ z ∈ p'.support, z.1 ∈ p.support) ∧ ∀ e ∈ p'.edges, (e.1.1, e.2.1) ∈ p.edges := by
  induction p with
  | nil v =>
    refine ⟨.nil _, ?_, by simp⟩
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    simp [hz]
  | @cons a t b hat p ih =>
    have ht : Mutual E c t := ⟨ha.1.tail hat, Reach.trans ⟨p⟩ hb.2⟩
    obtain ⟨q, h1, h2⟩ := ih ht hb
    refine ⟨.cons (y := ⟨t, ht⟩) hat q, ?_, ?_⟩
    · intro z hz
      simp only [Walk.support_cons, List.mem_cons] at hz ⊢
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr (h1 z hz)
    · intro e he
      simp only [Walk.edges_cons, List.mem_cons] at he ⊢
      rcases he with rfl | he
      · exact Or.inl rfl
      · exact Or.inr (h2 e he)

/-- The induced graph on a component is strongly connected. -/
theorem comp_strongConn : StrongConn (compGraph E c) := by
  intro x y
  obtain ⟨p⟩ := x.2.2.trans y.2.1
  obtain ⟨q, _⟩ := comp_walk p x.2 y.2
  exact ⟨q⟩

theorem Mutual.of_same {x y : V} (hx : Mutual E c x) (hy : Mutual E c y) : Mutual E x y :=
  ⟨hx.2.trans hy.1, hy.2.trans hx.1⟩

variable [Finite V]

/-- A strong bridge of `G` inside a component is a strong bridge of the induced graph on it. -/
theorem isStrongBridge_comp (u v : CompV E c) :
    IsStrongBridge E u.1 v.1 ↔ IsStrongBridge (compGraph E c) u v := by
  constructor
  · intro h
    obtain ⟨huv, _, x, y, hx, hy, hn⟩ := isStrongBridge_iff_mutual.mp h
    have hcx : Mutual E c x := ⟨u.2.1.trans hx.2, hx.1.trans u.2.2⟩
    have hcy : Mutual E c y := ⟨u.2.1.trans hy.2, hy.1.trans u.2.2⟩
    refine ⟨huv, (not_strongConn_delEdge_iff comp_strongConn u v).mpr fun hC => hn ?_⟩
    have hmap : ∀ a b : CompV E c, delEdge (compGraph E c) u v a b → delEdge E u.1 v.1 a.1 b.1 :=
      fun a b he => ⟨he.1, fun ⟨h1, h2⟩ => he.2 ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
    exact ⟨Reach.map Subtype.val hmap (hC ⟨x, hcx⟩ ⟨y, hcy⟩), Reach.map Subtype.val hmap (hC ⟨y, hcy⟩ ⟨x, hcx⟩)⟩
  · rintro ⟨huv, hlt⟩
    rw [not_strongConn_delEdge_iff comp_strongConn] at hlt
    simp only [StrongConn, not_forall] at hlt
    obtain ⟨x, y, hxy⟩ := hlt
    refine ⟨huv, (sccCount_delEdge_lt_iff _ _).mpr ⟨x.1, y.1, Mutual.of_same x.2 y.2, fun hm => hxy ?_⟩⟩
    obtain ⟨p, hp⟩ := reach_delEdge_iff.mp hm.1
    obtain ⟨q, _, h2⟩ := comp_walk p x.2 y.2
    exact reach_delEdge_iff.mpr ⟨q, fun hq => hp (h2 _ hq)⟩

/-- A strong articulation point of `G` is one of the induced graph on its component. -/
theorem isSAP_comp (d : CompV E c) : IsSAP E d.1 ↔ IsSAP (compGraph E c) d := by
  rw [isSAP_iff_of_strongConn comp_strongConn]
  constructor
  · intro h hC
    obtain ⟨x, y, hx, hy, hn⟩ := isSAP_iff_separates.mp h
    have hcx : Mutual E c x.1 := ⟨d.2.1.trans hx.2, hx.1.trans d.2.2⟩
    have hcy : Mutual E c y.1 := ⟨d.2.1.trans hy.2, hy.1.trans d.2.2⟩
    have hxd : (⟨x.1, hcx⟩ : CompV E c) ≠ d := fun e => x.2 (congrArg Subtype.val e)
    have hyd : (⟨y.1, hcy⟩ : CompV E c) ≠ d := fun e => y.2 (congrArg Subtype.val e)
    let f : {z : CompV E c // z ≠ d} → {a : V // a ≠ d.1} :=
      fun z => ⟨z.1.1, fun h => z.2 (Subtype.ext h)⟩
    have hmap : ∀ a b, delVertex (compGraph E c) d a b → delVertex E d.1 (f a) (f b) := fun _ _ he => he
    exact hn ⟨Reach.map f hmap (hC ⟨⟨x.1, hcx⟩, hxd⟩ ⟨⟨y.1, hcy⟩, hyd⟩),
      Reach.map f hmap (hC ⟨⟨y.1, hcy⟩, hyd⟩ ⟨⟨x.1, hcx⟩, hxd⟩)⟩
  · intro h
    simp only [StrongConn, not_forall] at h
    obtain ⟨x, y, hxy⟩ := h
    have hxd : x.1.1 ≠ d.1 := fun e => x.2 (Subtype.ext e)
    have hyd : y.1.1 ≠ d.1 := fun e => y.2 (Subtype.ext e)
    refine isSAP_iff_separates.mpr ⟨⟨x.1.1, hxd⟩, ⟨y.1.1, hyd⟩, Mutual.of_same x.1.2 d.2,
      Mutual.of_same y.1.2 d.2, fun hm => hxy ?_⟩
    obtain ⟨p, hp⟩ := reach_delVertex_iff.mp hm.1
    obtain ⟨q, h1, _⟩ := comp_walk p x.1.2 y.1.2
    exact reach_delVertex_iff.mpr ⟨q, fun hq => hp (h1 d hq)⟩

/-- **Theorem 3, edges.** Inside any component, with any `s` in it, an edge is a strong bridge of `G` iff it is a
bridge of the flow graph of the induced graph from `s`, or of its reverse from `s`. An edge between components is
no strong bridge, by `IsStrongBridge.mutual`. -/
theorem theorem3_edge (s u v : CompV E c) :
    IsStrongBridge E u.1 v.1 ↔ IsBridge (compGraph E c) s u v ∨ IsBridge (rev (compGraph E c)) s v u := by
  rw [isStrongBridge_comp]
  exact lemma3_edge comp_strongConn s

/-- **Theorem 3, vertices.** Inside any component, with any `s` in it, a vertex `d ≠ s` is a strong articulation
point of `G` iff it dominates some other vertex in the flow graph of the induced graph from `s`, or of its
reverse from `s`. The vertex `s` itself is tested by `isSAP_self_iff` on the induced graph. -/
theorem theorem3_vertex {s d : CompV E c} (hd : d ≠ s) :
    IsSAP E d.1 ↔ ∃ w, w ≠ d ∧ (Dominates (compGraph E c) s d w ∨ Dominates (rev (compGraph E c)) s d w) := by
  rw [isSAP_comp]
  exact lemma3_vertex comp_strongConn hd

end Dominators
