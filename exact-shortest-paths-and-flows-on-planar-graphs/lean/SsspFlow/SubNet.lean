import SsspFlow.ListRot
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# The subdivision of a rotation system as a network

Every edge of a rotation system `R` becomes a path of three edges: the nodes are the vertices of `R`
and its darts, a vertex is joined to the darts at it, and each dart to its reverse (`subNet`). This
is a simple graph for every `R`, loops and parallel edges included. The darts at a vertex keep their
rotation.

* `subNet_planar`: the subdivision of a connected planar rotation system is planar. A function on
  its darts onto the faces of `R` shows that it has enough faces.
* `reach_of_isWalk`: a walk of `R` with `k` darts gives a walk of the subdivision with `3 k` edges.
* `subNet_diam`: if any two vertices of `R` are joined by a walk with at most `k` darts, the
  subdivision has diameter at most `3 k + 2`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor Cslib.Congest SsspFlow.Congest

namespace RotSystem

variable {D : Type} [Fintype D] [DecidableEq D] (R : RotSystem D)

noncomputable instance : Fintype R.Vertex := Fintype.ofFinite _

noncomputable instance : DecidableEq R.Vertex := Classical.decEq _

/-- The darts at a vertex in rotation order. -/
noncomputable def vList (v : R.Vertex) : List D :=
  if R.rot v.out = v.out then [v.out] else R.rot.toList v.out

theorem tail_eq_iff_sameCycle (v : R.Vertex) (d : D) : R.tail d = v ↔ R.rot.SameCycle v.out d := by
  conv_lhs => rw [← Quotient.out_eq v]
  show Quotient.mk _ d = Quotient.mk _ v.out ↔ _
  rw [Quotient.eq]
  exact ⟨fun h => Equiv.Perm.SameCycle.symm h, fun h => Equiv.Perm.SameCycle.symm h⟩

theorem mem_vList (v : R.Vertex) (d : D) : d ∈ R.vList v ↔ R.tail d = v := by
  rw [R.tail_eq_iff_sameCycle]
  unfold vList
  split_ifs with h
  · rw [List.mem_singleton]
    constructor
    · rintro rfl; exact Equiv.Perm.SameCycle.refl _ _
    · rintro ⟨i, rfl⟩
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h i
  · rw [Equiv.Perm.mem_toList_iff, Equiv.Perm.mem_support]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩

theorem nodup_vList (v : R.Vertex) : (R.vList v).Nodup := by
  unfold vList
  split_ifs
  · exact List.nodup_singleton _
  · exact Equiv.Perm.nodup_toList _ _

theorem formPerm_vList {v : R.Vertex} {d : D} (hd : d ∈ R.vList v) :
    (R.vList v).formPerm d = R.rot d := by
  have hs := (R.tail_eq_iff_sameCycle v d).1 ((R.mem_vList v d).1 hd)
  unfold vList at hd ⊢
  split_ifs with h
  · rw [if_pos h, List.mem_singleton] at hd
    subst hd
    rw [List.formPerm_singleton, h]
    rfl
  · rw [Equiv.Perm.formPerm_toList, Equiv.Perm.cycleOf_apply, if_pos hs]

/-- The adjacency of the subdivision. -/
def SubAdj : R.Vertex ⊕ D → R.Vertex ⊕ D → Prop
  | .inl v, .inr x => R.tail x = v
  | .inr x, .inl v => R.tail x = v
  | .inr x, .inr y => y = R.rev x
  | .inl _, .inl _ => False

open Classical in
/-- The subdivision of `R`. -/
noncomputable def subNet : Net (R.Vertex ⊕ D) where
  G :=
    { Adj := R.SubAdj
      symm := ⟨fun a b h => by
        cases a <;> cases b <;> simp only [SubAdj] at h ⊢
        · exact h
        · exact h
        · rw [h, R.rev_rev]⟩
      loopless := ⟨fun a h => by
        cases a <;> simp only [SubAdj] at h
        exact R.rev_ne _ h.symm⟩ }
  rotList
    | .inl v => (R.vList v).map .inr
    | .inr x => [.inl (R.tail x), .inr (R.rev x)]
  nodup a := by
    cases a with
    | inl v => exact (R.nodup_vList v).map Sum.inr_injective
    | inr x => simp
  mem_rotList a b := by
    cases a <;> cases b <;> simp [SubAdj, R.mem_vList, eq_comm]

@[simp] theorem subNet_adj (a b : R.Vertex ⊕ D) : R.subNet.G.Adj a b ↔ R.SubAdj a b := Iff.rfl

theorem subNet_rotList_inl (v : R.Vertex) : R.subNet.rotList (.inl v) = (R.vList v).map .inr := rfl

theorem subNet_rotList_inr (x : D) :
    R.subNet.rotList (.inr x) = [.inl (R.tail x), .inr (R.rev x)] := rfl

/-- The label of a pair of nodes: a face of `R`. -/
noncomputable def subLabP : R.Vertex ⊕ D → R.Vertex ⊕ D → R.Face
  | .inr x, .inl _ => R.faceOf (R.rev x)
  | .inr x, .inr _ => R.faceOf x
  | .inl _, .inr x => R.faceOf x
  | .inl v, .inl _ => R.faceOf v.out

/-- The label of a dart of the subdivision: a face of `R`. -/
noncomputable def subLab (z : R.subNet.G.Dart) : R.Face := R.subLabP z.fst z.snd

theorem subLab_step (z : R.subNet.G.Dart) :
    R.subLab (R.subNet.toRot.rev (R.subNet.toRot.rot z)) = R.subLab z := by
  obtain ⟨⟨a, b⟩, hz⟩ := z
  cases a with
  | inl v =>
    cases b with
    | inl w => exact absurd hz id
    | inr x =>
      have hx : x ∈ R.vList v := (R.mem_vList v x).2 hz
      have hf : ((R.vList v).map Sum.inr).formPerm (Sum.inr x) = (Sum.inr (R.rot x) : R.Vertex ⊕ D) := by
        rw [RotSystem.formPerm_map_apply Sum.inr_injective (R.nodup_vList v) hx, R.formPerm_vList hx]
      show R.subLabP ((R.subNet.rotList (.inl v)).formPerm (.inr x)) (.inl v) = R.faceOf x
      rw [subNet_rotList_inl, hf]
      exact R.faceOf_rev_rot x
  | inr x =>
    cases b with
    | inl w =>
      have hw : R.tail x = w := hz
      subst hw
      show R.subLabP ((R.subNet.rotList (.inr x)).formPerm (.inl (R.tail x))) (.inr x) =
        R.faceOf (R.rev x)
      rw [subNet_rotList_inr, List.formPerm_pair, Equiv.swap_apply_left]
      rfl
    | inr y =>
      have hy : y = R.rev x := hz
      subst hy
      show R.subLabP ((R.subNet.rotList (.inr x)).formPerm (.inr (R.rev x))) (.inr x) =
        R.faceOf x
      rw [subNet_rotList_inr, List.formPerm_pair, Equiv.swap_apply_right]
      rfl

theorem subLab_surj : Function.Surjective R.subLab := fun f => by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  exact ⟨⟨(.inl (R.tail x), .inr x), rfl⟩, rfl⟩

theorem subNet_noIso (a : R.Vertex ⊕ D) : ∃ b, R.subNet.G.Adj a b := by
  cases a with
  | inl v =>
    obtain ⟨x, hx⟩ := R.exists_tail_eq v
    exact ⟨.inr x, hx⟩
  | inr x => exact ⟨.inl (R.tail x), rfl⟩

theorem sum_vList : ∑ v, (R.vList v).length = Fintype.card D := by
  classical
  have h : ∀ v, (R.vList v).length = (Finset.univ.filter fun x => R.tail x = v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (R.nodup_vList v)]
    congr 1
    ext x
    simp [R.mem_vList]
  simp_rw [h]
  exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (R.tail x))).symm

/-- A walk of `R` with `k` darts gives a walk of the subdivision with `3 k` edges. -/
theorem reach_of_isWalk {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) :
    Reach R.subNet.G (3 * p.length) (.inl u) (.inl v) := by
  induction p generalizing u with
  | nil =>
    rw [R.isWalk_nil] at hp
    subst hp
    exact Reach.refl _
  | cons x p ih =>
    obtain ⟨hx, hp'⟩ := (R.isWalk_cons _ _ _ _).1 hp
    subst hx
    have h1 : Reach R.subNet.G 1 (.inl (R.tail x)) (.inr x) := Reach.of_adj (show R.tail x = R.tail x from rfl)
    have h2 : Reach R.subNet.G 1 (.inr x) (.inr (R.rev x)) := Reach.of_adj (show R.rev x = R.rev x from rfl)
    have h3 : Reach R.subNet.G 1 (.inr (R.rev x)) (.inl (R.head x)) :=
      Reach.of_adj (show R.tail (R.rev x) = R.head x from rfl)
    have := ((h1.trans h2).trans h3).trans (ih hp')
    obtain ⟨q, hq⟩ := this
    exact ⟨q, by simp only [List.length_cons]; omega⟩

theorem reach_inl (a : R.Vertex ⊕ D) : ∃ v, Reach R.subNet.G 1 a (.inl v) ∧ Reach R.subNet.G 1 (.inl v) a := by
  cases a with
  | inl v => exact ⟨v, ⟨.nil, by simp⟩, ⟨.nil, by simp⟩⟩
  | inr x =>
    exact ⟨R.tail x, Reach.of_adj (show R.tail x = R.tail x from rfl),
      Reach.of_adj (show R.tail x = R.tail x from rfl)⟩

/-- **Diameter of the subdivision.** -/
theorem subNet_diam {k : ℕ} (h : ∀ u v : R.Vertex, ∃ p, R.IsWalk u p v ∧ p.length ≤ k) :
    R.subNet.DiamLE (3 * k + 2) := by
  intro a b
  obtain ⟨u, ha, -⟩ := R.reach_inl a
  obtain ⟨v, -, hb⟩ := R.reach_inl b
  obtain ⟨p, hp, hk⟩ := h u v
  obtain ⟨q, hq⟩ := (ha.trans (R.reach_of_isWalk hp)).trans hb
  exact ⟨q, by omega⟩

theorem subNet_G_connected (hc : R.Connected) : R.subNet.G.Connected := by
  obtain ⟨⟨d₀⟩, hw⟩ := R.connected_iff.1 hc
  exact
    { preconnected := fun a b => by
        obtain ⟨u, ha, -⟩ := R.reach_inl a
        obtain ⟨v, -, hb⟩ := R.reach_inl b
        obtain ⟨p, hp⟩ := hw u v
        obtain ⟨q, -⟩ := (ha.trans (R.reach_of_isWalk hp)).trans hb
        exact ⟨q⟩
      nonempty := ⟨.inr d₀⟩ }

theorem subNet_connected (hc : R.Connected) : R.subNet.toRot.Connected := by
  obtain ⟨⟨d₀⟩, -⟩ := R.connected_iff.1 hc
  exact R.subNet.toRot_connected (R.subNet_G_connected hc) ⟨(.inl (R.tail d₀), .inr d₀), rfl⟩

/-- **The subdivision of a connected planar rotation system is planar.** -/
theorem subNet_planar (hP : R.Planar) (hc : R.Connected) : R.subNet.toRot.Planar := by
  classical
  refine R.subNet.toRot.planar_of_count (R.subNet_connected hc) ?_
  have hF := R.subNet.toRot.card_le_numFaces R.subLab R.subLab_step R.subLab_surj
  rw [R.natCard_face] at hF
  have hV := R.subNet.numVertices_eq R.subNet_noIso
  rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, R.natCard_vertex] at hV
  have hE := R.subNet.numEdges_eq
  rw [Fintype.sum_sum_type] at hE
  simp only [subNet_rotList_inl, subNet_rotList_inr, List.length_map, List.length_cons,
    List.length_nil, R.sum_vList, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hE
  have hEu := R.euler hP hc
  rw [R.numEdges_eq] at hEu
  omega

end RotSystem

namespace Congest

namespace Net

variable {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] (N : Net V) (e : V ≃ V')

/-- The network with its nodes renamed by `e`. -/
def relabel : Net V' where
  G := N.G.comap e.symm
  rotList u := (N.rotList (e.symm u)).map e
  nodup u := (N.nodup _).map e.injective
  mem_rotList u w := by
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show N.G.Adj (e.symm u) (e.symm (e y))
      rw [e.symm_apply_apply]
      exact (N.mem_rotList _ _).1 hy
    · intro h
      exact ⟨e.symm w, (N.mem_rotList _ _).2 h, e.apply_symm_apply w⟩

theorem relabel_adj (a b : V) : (N.relabel e).G.Adj (e a) (e b) ↔ N.G.Adj a b := by
  show N.G.Adj (e.symm (e a)) (e.symm (e b)) ↔ _
  rw [e.symm_apply_apply, e.symm_apply_apply]

/-- The renaming as an isomorphism of graphs. -/
def relabelIso : N.G ≃g (N.relabel e).G := ⟨e, fun {a b} => N.relabel_adj e a b⟩

theorem relabel_diam {D : ℕ} (hD : N.DiamLE D) : (N.relabel e).DiamLE D := by
  intro u w
  obtain ⟨p, hp⟩ := hD ((N.relabelIso e).symm u) ((N.relabelIso e).symm w)
  rw [← (N.relabelIso e).apply_symm_apply u, ← (N.relabelIso e).apply_symm_apply w]
  exact ⟨p.map (N.relabelIso e).toHom, by rw [SimpleGraph.Walk.length_map]; exact hp⟩

/-- The dart of `N` of a dart of the renamed network. -/
def relabelDart (z : (N.relabel e).G.Dart) : N.G.Dart := ⟨(e.symm z.fst, e.symm z.snd), z.adj⟩

theorem relabelDart_step (z : (N.relabel e).G.Dart) :
    N.relabelDart e ((N.relabel e).toRot.rev ((N.relabel e).toRot.rot z)) =
      N.toRot.rev (N.toRot.rot (N.relabelDart e z)) := by
  obtain ⟨⟨u, w⟩, hz⟩ := z
  have hm : e.symm w ∈ N.rotList (e.symm u) := (N.mem_rotList _ _).2 hz
  have hf : ((N.rotList (e.symm u)).map e).formPerm w = e ((N.rotList (e.symm u)).formPerm (e.symm w)) := by
    conv_lhs => rw [← e.apply_symm_apply w]
    exact RotSystem.formPerm_map_apply e.injective (N.nodup _) hm
  apply SimpleGraph.Dart.ext
  show (e.symm (((N.rotList (e.symm u)).map e).formPerm w), e.symm u) =
    ((N.rotList (e.symm u)).formPerm (e.symm w), e.symm u)
  rw [hf, e.symm_apply_apply]

theorem relabel_noIso (h : ∀ v, ∃ u, N.G.Adj v u) (u : V') : ∃ w, (N.relabel e).G.Adj u w := by
  obtain ⟨w, hw⟩ := h (e.symm u)
  exact ⟨e w, by rw [← e.apply_symm_apply u, N.relabel_adj]; exact hw⟩

/-- **Renaming keeps planarity.** -/
theorem relabel_planar (hP : N.toRot.Planar) (hG : N.G.Connected) (h : ∀ v, ∃ u, N.G.Adj v u) :
    (N.relabel e).toRot.Planar := by
  classical
  obtain ⟨v₀⟩ := hG.nonempty
  obtain ⟨u₀, hu₀⟩ := h v₀
  have hc := N.toRot_connected hG ⟨(v₀, u₀), hu₀⟩
  have hG' : (N.relabel e).G.Connected := (N.relabelIso e).connected_iff.1 hG
  have hc' := (N.relabel e).toRot_connected hG' ⟨(e v₀, e u₀), (N.relabel_adj e _ _).2 hu₀⟩
  refine (N.relabel e).toRot.planar_of_count hc' ?_
  have hF := (N.relabel e).toRot.card_le_numFaces (fun z => N.toRot.faceOf (N.relabelDart e z))
    (fun z => by rw [relabelDart_step, RotSystem.faceOf_rev_rot])
    (fun f => by
      obtain ⟨d, rfl⟩ := Quotient.exists_rep f
      refine ⟨⟨(e d.fst, e d.snd), (N.relabel_adj e _ _).2 d.adj⟩, ?_⟩
      show N.toRot.faceOf _ = N.toRot.faceOf d
      congr 1
      apply SimpleGraph.Dart.ext
      simp [relabelDart])
  rw [N.toRot.natCard_face] at hF
  have hV := N.numVertices_eq h
  have hV' := (N.relabel e).numVertices_eq (N.relabel_noIso e h)
  have hE := N.numEdges_eq
  have hE' := (N.relabel e).numEdges_eq
  have hs : ∑ u, ((N.relabel e).rotList u).length = ∑ v, (N.rotList v).length := by
    show ∑ u, ((N.rotList (e.symm u)).map e).length = _
    simp only [List.length_map]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  have hcard : Fintype.card V' = Fintype.card V := (Fintype.card_congr e).symm
  have hEu := N.toRot.euler hP hc
  omega

end Net

end Congest

end SsspFlow
