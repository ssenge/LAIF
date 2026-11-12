import SsspFlow.NetPad

/-!
# The dual network of a plane network

The expansion of a plane network `N`: a vertex becomes a crown of corners with a centre, a face becomes
a ring of corners, and an edge becomes a face with twelve sides. All edges of crowns and rings are
subdivided, so the expansion is a simple graph for every `N`. Shortest paths on it, with suitable arcs,
are the dual of flows on `N`.

* `Net.xNet`: the expansion.
* `Net.xNet_planar`: the expansion of a connected planar network is planar. A function on the darts
  shows that it has enough faces.
* `Net.xNet_diam`: its diameter is at most `5 D + 4`.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

/-- The five nodes of a dart in the expansion: its corner, two nodes on the edge of the crown, two nodes
on the edge of the ring. -/
inductive Kind where
  | corner | m1 | m2 | r1 | r2
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.corner, .m1, .m2, .r1, .r2}
  complete k := by cases k <;> simp

theorem Kind.card_eq : Fintype.card Kind = 5 := rfl

/-- The nodes of the expansion: a centre per vertex, five nodes per dart. -/
inductive XNode (V D : Type) where
  | center (v : V)
  | node (k : Kind) (x : D)
  deriving DecidableEq

namespace XNode

variable {V D : Type}

/-- The nodes as a sum. -/
def equivSum : XNode V D ≃ V ⊕ Kind × D where
  toFun
    | center v => .inl v
    | node k x => .inr (k, x)
  invFun
    | .inl v => center v
    | .inr p => node p.1 p.2
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with v | ⟨k, x⟩ <;> rfl

instance [Fintype V] [Fintype D] : Fintype (XNode V D) := Fintype.ofEquiv _ equivSum.symm

theorem card_eq [Fintype V] [Fintype D] :
    Fintype.card (XNode V D) = Fintype.card V + 5 * Fintype.card D := by
  rw [Fintype.card_congr equivSum, Fintype.card_sum, Fintype.card_prod, Kind.card_eq]

/-- A sum over the nodes. -/
theorem sum_eq [Fintype V] [Fintype D] (f : XNode V D → ℕ) :
    ∑ a, f a = ∑ v, f (center v) + ∑ x, (f (node .corner x) + f (node .m1 x) + f (node .m2 x) +
      f (node .r1 x) + f (node .r2 x)) := by
  rw [Fintype.sum_equiv equivSum f (fun s => f (equivSum.symm s)) (fun a => by simp),
    Fintype.sum_sum_type, Fintype.sum_prod_type_right]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have : (Finset.univ : Finset Kind) = {.corner, .m1, .m2, .r1, .r2} := by decide
  rw [this]
  simp [equivSum]
  omega

end XNode

open XNode Kind

namespace Net

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

/-- The darts at a node, in rotation order. -/
def dartsAt (v : V) : List N.G.Dart :=
  (N.rotList v).attach.map fun u => ⟨(v, u.1), (N.mem_rotList _ _).1 u.2⟩

theorem mem_dartsAt {v : V} {w : N.G.Dart} : w ∈ N.dartsAt v ↔ w.fst = v := by
  constructor
  · intro h
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 h
    rfl
  · rintro rfl
    exact List.mem_map.2 ⟨⟨w.snd, (N.mem_rotList _ _).2 w.adj⟩, List.mem_attach _ _, rfl⟩

theorem dartsAt_nodup (v : V) : (N.dartsAt v).Nodup := by
  refine (List.nodup_attach.2 (N.nodup v)).map fun a b h => ?_
  have := congrArg (fun d : N.G.Dart => d.snd) h
  exact Subtype.ext this

theorem length_dartsAt (v : V) : (N.dartsAt v).length = (N.rotList v).length := by
  simp [dartsAt]

/-- The cycle of the darts at a node is the rotation. -/
theorem formPerm_dartsAt {v : V} {w : N.G.Dart} (hw : w.fst = v) :
    (N.dartsAt v).formPerm w = N.rotPerm w := by
  subst hw
  have hmem : w.snd ∈ N.rotList w.fst := (N.mem_rotList _ _).2 w.adj
  obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hmem
  have hlen := N.length_dartsAt w.fst
  have hi' : i < (N.dartsAt w.fst).length := by omega
  have h1 : (N.dartsAt w.fst)[i] = w := by
    refine SimpleGraph.Dart.ext _ _ (Prod.ext (by simp [dartsAt]) ?_)
    simpa [dartsAt] using hwi
  have h2 := List.formPerm_apply_getElem _ (N.dartsAt_nodup w.fst) i hi'
  rw [h1] at h2
  rw [h2]
  have h3 := List.formPerm_apply_getElem _ (N.nodup w.fst) i hi
  rw [hwi] at h3
  refine SimpleGraph.Dart.ext _ _ (Prod.ext (by simp [dartsAt]) ?_)
  show _ = (N.rotList w.fst).formPerm w.snd
  rw [h3]
  simp [dartsAt]

/-- The rotation list of a node of the expansion. -/
def xList : XNode V N.G.Dart → List (XNode V N.G.Dart)
  | center v => (N.dartsAt v).map (node corner)
  | node corner x => [center x.fst, node m1 x, node r1 x, node r2 (N.rotPerm x), node m2 (N.rotPerm x)]
  | node m1 x => [node corner x, node m2 x]
  | node m2 x => [node m1 x, node corner (N.rotPerm.symm x)]
  | node r1 x => [node corner x, node r2 x.symm]
  | node r2 x => [node r1 x.symm, node corner (N.rotPerm.symm x)]

theorem xList_symm {a b : XNode V N.G.Dart} (h : b ∈ N.xList a) : a ∈ N.xList b := by
  cases a with
  | center v =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
    have hv : w.fst = v := N.mem_dartsAt.1 hw
    simp [xList, hv]
  | node k x =>
    cases k <;> simp only [xList, List.mem_cons, List.not_mem_nil, or_false] at h
    · rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [xList, N.mem_dartsAt]
    · rcases h with rfl | rfl <;> simp [xList]
    · rcases h with rfl | rfl <;> simp [xList]
    · rcases h with rfl | rfl <;> simp [xList]
    · rcases h with rfl | rfl <;> simp [xList]

theorem xList_irrefl (a : XNode V N.G.Dart) : a ∉ N.xList a := by
  cases a with
  | center v => simp [xList]
  | node k x => cases k <;> simp [xList]

theorem xList_nodup (a : XNode V N.G.Dart) : (N.xList a).Nodup := by
  cases a with
  | center v =>
    exact (N.dartsAt_nodup v).map fun a b h => by
      injection h
  | node k x => cases k <;> simp [xList]

/-- The expansion of a plane network. -/
def xNet : Net (XNode V N.G.Dart) where
  G := { Adj := fun a b => b ∈ N.xList a
         symm := ⟨fun _ _ h => N.xList_symm h⟩
         loopless := ⟨N.xList_irrefl⟩ }
  rotList := N.xList
  nodup := N.xList_nodup
  mem_rotList _ _ := Iff.rfl

/-! ### Reachability and diameter -/

theorem xNet_reach_center (a : XNode V N.G.Dart) :
    ∃ v, Reach N.xNet.G 2 a (center v) ∧ (∀ x k, a = node k x → v = x.fst) := by
  cases a with
  | center v => exact ⟨v, (Reach.refl _).mono (by omega), by simp⟩
  | node k x =>
    refine ⟨x.fst, ?_, by simp +contextual⟩
    have hc : ∀ y : N.G.Dart, Reach N.xNet.G 1 (node corner y) (center y.fst) := fun y =>
      Reach.of_adj (show _ ∈ N.xList _ by simp [xList])
    cases k
    · exact (hc x).mono (by omega)
    · exact (Reach.of_adj (show _ ∈ N.xList _ by simp [xList])).trans (hc x)
    · exact (Reach.of_adj (show _ ∈ N.xList _ by simp [xList])).trans (hc (N.rotPerm.symm x))
    · exact (Reach.of_adj (show _ ∈ N.xList _ by simp [xList])).trans (hc x)
    · exact (Reach.of_adj (show _ ∈ N.xList _ by simp [xList])).trans (hc (N.rotPerm.symm x))

/-- An edge of the network costs five hops between centres. -/
theorem xNet_reach_adj {u v : V} (h : N.G.Adj u v) :
    Reach N.xNet.G 5 (center u) (center v) := by
  let x : N.G.Dart := ⟨(u, v), h⟩
  have h1 : N.xNet.G.Adj (center u) (node corner x) :=
    show _ ∈ N.xList _ from List.mem_map.2 ⟨x, N.mem_dartsAt.2 rfl, rfl⟩
  have h2 : N.xNet.G.Adj (node corner x) (node r1 x) := show _ ∈ N.xList _ by simp [xList]
  have h3 : N.xNet.G.Adj (node r1 x) (node r2 x.symm) := show _ ∈ N.xList _ by simp [xList]
  have h4 : N.xNet.G.Adj (node r2 x.symm) (node corner (N.rotPerm.symm x.symm)) :=
    show _ ∈ N.xList _ by simp [xList]
  have h5 : N.xNet.G.Adj (node corner (N.rotPerm.symm x.symm)) (center v) :=
    show _ ∈ N.xList _ by simp [xList]; rfl
  exact ((((Reach.of_adj h1).trans (Reach.of_adj h2)).trans (Reach.of_adj h3)).trans
    (Reach.of_adj h4)).trans (Reach.of_adj h5)

theorem xNet_reach_centers {u v : V} {k : ℕ} (h : Reach N.G k u v) :
    Reach N.xNet.G (5 * k) (center u) (center v) := by
  obtain ⟨p, hp⟩ := h
  refine Reach.mono ?_ (Nat.mul_le_mul_left 5 hp)
  clear hp
  induction p with
  | nil => exact Reach.refl _
  | cons h _ ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.mul_add, add_comm]
    exact (N.xNet_reach_adj h).trans ih

/-- The diameter of the expansion. -/
theorem xNet_diam {D : ℕ} (h : N.DiamLE D) : N.xNet.DiamLE (5 * D + 4) := by
  intro a b
  obtain ⟨u, hu, -⟩ := N.xNet_reach_center a
  obtain ⟨v, hv, -⟩ := N.xNet_reach_center b
  obtain ⟨p, hp⟩ := h u v
  obtain ⟨q, hq⟩ := hv
  have hv' : Reach N.xNet.G 2 (center v) b := ⟨q.reverse, by simpa using hq⟩
  exact ((hu.trans (N.xNet_reach_centers ⟨p, hp⟩)).trans hv').mono (by omega)

theorem xNet_noIso (h : ∀ v, ∃ u, N.G.Adj v u) (a : XNode V N.G.Dart) : ∃ b, N.xNet.G.Adj a b := by
  cases a with
  | center v =>
    obtain ⟨u, hu⟩ := h v
    let x : N.G.Dart := ⟨(v, u), hu⟩
    exact ⟨node corner x, List.mem_map.2 ⟨x, N.mem_dartsAt.2 rfl, rfl⟩⟩
  | node k x =>
    cases k
    · exact ⟨_, show _ ∈ N.xList _ by simp [xList]; exact Or.inl rfl⟩
    · exact ⟨_, show _ ∈ N.xList _ by simp [xList]; exact Or.inl rfl⟩
    · exact ⟨_, show _ ∈ N.xList _ by simp [xList]; exact Or.inl rfl⟩
    · exact ⟨_, show _ ∈ N.xList _ by simp [xList]; exact Or.inl rfl⟩
    · exact ⟨_, show _ ∈ N.xList _ by simp [xList]; exact Or.inl rfl⟩

/-! ### Planarity -/

/-- The faces of the expansion: a ring per face, a face per edge, a crown triangle per dart. -/
private abbrev XLabel : Type := N.toRot.Face ⊕ N.G.edgeSet ⊕ N.G.Dart

private def ring (x : N.G.Dart) : XLabel N := .inl (N.toRot.faceOf x)
private def quad (x : N.G.Dart) : XLabel N := .inr (.inl ⟨x.edge, x.edge_mem⟩)
private def crown (x : N.G.Dart) : XLabel N := .inr (.inr x)

/-- The face to the left of a dart of the expansion. -/
private def xLab (x₀ : N.G.Dart) : XNode V N.G.Dart → XNode V N.G.Dart → XLabel N
  | center _, node corner w => crown N w
  | node corner x, center _ => crown N (N.rotPerm.symm x)
  | node corner x, node m1 _ => quad N x
  | node corner x, node r1 _ => ring N x
  | node corner _, node r2 y => quad N y
  | node corner _, node m2 y => crown N (N.rotPerm.symm y)
  | node m1 x, node corner _ => crown N (N.rotPerm.symm x)
  | node m1 x, node m2 _ => quad N x
  | node m2 x, node m1 _ => crown N (N.rotPerm.symm x)
  | node m2 x, node corner _ => quad N x
  | node r1 x, node corner _ => quad N x
  | node r1 x, node r2 _ => ring N x
  | node r2 x, node r1 _ => quad N x
  | node r2 _, node corner y => ring N y
  | _, _ => crown N x₀

private theorem formPerm_five {α : Type*} [DecidableEq α] {a b c d e : α}
    (h : [a, b, c, d, e].Nodup) :
    [a, b, c, d, e].formPerm a = b ∧ [a, b, c, d, e].formPerm b = c ∧
      [a, b, c, d, e].formPerm c = d ∧ [a, b, c, d, e].formPerm d = e ∧
      [a, b, c, d, e].formPerm e = a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using List.formPerm_apply_getElem _ h 0 (by simp)
  · simpa using List.formPerm_apply_getElem _ h 1 (by simp)
  · simpa using List.formPerm_apply_getElem _ h 2 (by simp)
  · simpa using List.formPerm_apply_getElem _ h 3 (by simp)
  · simp

private theorem xLab_step (x₀ : N.G.Dart) (a b : XNode V N.G.Dart) (hab : b ∈ N.xList a) :
    xLab N x₀ ((N.xList a).formPerm b) a = xLab N x₀ a b := by
  have hrev : ∀ x : N.G.Dart, quad N x.symm = quad N x := fun x => by
    simp only [quad]
    congr 2
    exact Subtype.ext x.edge_symm
  cases a with
  | center v =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hab
    have hinj : Function.Injective (node corner : N.G.Dart → XNode V N.G.Dart) := fun _ _ h => by
      injection h
    show xLab N x₀ (((N.dartsAt v).map (node corner)).formPerm (node corner w)) (center v) = _
    rw [formPerm_map_apply hinj (N.dartsAt_nodup v) hw, N.formPerm_dartsAt (N.mem_dartsAt.1 hw)]
    simp [xLab]
  | node k x =>
    have hnd := N.xList_nodup (node k x)
    cases k
    · obtain ⟨h1, h2, h3, h4, h5⟩ := formPerm_five hnd
      simp only [xList, List.mem_cons, List.not_mem_nil, or_false] at hab
      simp only [xList] at h1 h2 h3 h4 h5 ⊢
      rcases hab with rfl | rfl | rfl | rfl | rfl
      · rw [h1]
        rfl
      · rw [h2]
        rfl
      · rw [h3]
        simp [xLab]
      · rw [h4]
        rfl
      · rw [h5]
        simp [xLab]
    · simp only [xList, List.mem_cons, List.not_mem_nil, or_false] at hab
      simp only [xList, List.formPerm_pair]
      rcases hab with rfl | rfl
      · rw [Equiv.swap_apply_left]
        rfl
      · rw [Equiv.swap_apply_right]
        rfl
    · simp only [xList, List.mem_cons, List.not_mem_nil, or_false] at hab
      simp only [xList, List.formPerm_pair]
      rcases hab with rfl | rfl
      · rw [Equiv.swap_apply_left]
        rfl
      · rw [Equiv.swap_apply_right]
        rfl
    · simp only [xList, List.mem_cons, List.not_mem_nil, or_false] at hab
      simp only [xList, List.formPerm_pair]
      rcases hab with rfl | rfl
      · rw [Equiv.swap_apply_left]
        exact hrev x
      · rw [Equiv.swap_apply_right]
        rfl
    · simp only [xList, List.mem_cons, List.not_mem_nil, or_false] at hab
      simp only [xList, List.formPerm_pair]
      rcases hab with rfl | rfl
      · rw [Equiv.swap_apply_left]
        rfl
      · rw [Equiv.swap_apply_right]
        have := N.toRot.faceOf_rot_symm x
        exact (congrArg Sum.inl this).symm

/-- The expansion of a connected network is connected. -/
theorem xNet_connected {D : ℕ} (hD : N.DiamLE D) (hc : N.toRot.Connected) : N.xNet.toRot.Connected := by
  obtain ⟨⟨d₀⟩, -⟩ := N.toRot.connected_iff.1 hc
  have hdiam := N.xNet_diam hD
  have hne : Nonempty (XNode V N.G.Dart) := ⟨center d₀.fst⟩
  have hG : N.xNet.G.Connected :=
    { preconnected := fun u v => by
        obtain ⟨p, -⟩ := hdiam u v
        exact ⟨p⟩ }
  have hd' : N.xNet.G.Adj (node corner d₀) (node m1 d₀) := show _ ∈ N.xList _ by simp [xList]
  exact N.xNet.toRot_connected hG ⟨(_, _), hd'⟩

/-- The expansion of a connected planar network is planar. -/
theorem xNet_planar (hP : N.toRot.Planar) (hN : ∀ v, ∃ u, N.G.Adj v u) {D : ℕ} (hD : N.DiamLE D)
    (hc : N.toRot.Connected) : N.xNet.toRot.Planar := by
  classical
  obtain ⟨⟨d₀⟩, -⟩ := N.toRot.connected_iff.1 hc
  have hc' := N.xNet_connected hD hc
  refine RotSystem.planar_of_count _ hc' ?_
  have hfaces : Nat.card (XLabel N) ≤ N.xNet.toRot.numFaces := by
    refine RotSystem.card_le_numFaces _ (fun z => xLab N d₀ z.fst z.snd) (fun z => ?_) (fun l => ?_)
    · exact xLab_step N d₀ z.fst z.snd z.adj
    · rcases l with f | ⟨⟨e, he⟩⟩ | w
      · obtain ⟨d, rfl⟩ := Quotient.exists_rep f
        exact ⟨⟨(node corner d, node r1 d), show _ ∈ N.xList _ by simp [xList]⟩, rfl⟩
      · obtain ⟨d, hd⟩ : ∃ d : N.G.Dart, d.edge = e := by
          induction e using Sym2.ind with
          | _ u v => exact ⟨⟨(u, v), he⟩, rfl⟩
        subst hd
        exact ⟨⟨(node corner d, node m1 d), show _ ∈ N.xList _ by simp [xList]⟩, rfl⟩
      · exact ⟨⟨(center w.fst, node corner w), List.mem_map.2 ⟨w, N.mem_dartsAt.2 rfl, rfl⟩⟩, rfl⟩
  have hcard : Nat.card (XLabel N) =
      N.toRot.numFaces + (Fintype.card N.G.Dart / 2 + Fintype.card N.G.Dart) := by
    have he : Nat.card N.G.edgeSet = Fintype.card N.G.Dart / 2 := by
      rw [N.G.dart_card_eq_twice_card_edges, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      omega
    rw [Nat.card_sum, Nat.card_sum, N.toRot.natCard_face, he, Nat.card_eq_fintype_card]
  have hsum : ∑ a, (N.xList a).length = 14 * Fintype.card N.G.Dart := by
    rw [XNode.sum_eq]
    have h1 : ∑ v, (N.xList (center v)).length = Fintype.card N.G.Dart := by
      rw [N.dart_card]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [xList, N.length_dartsAt]
    have h2 : ∑ x : N.G.Dart, ((N.xList (node corner x)).length + (N.xList (node m1 x)).length +
        (N.xList (node m2 x)).length + (N.xList (node r1 x)).length +
        (N.xList (node r2 x)).length) = 13 * Fintype.card N.G.Dart := by
      simp [xList, Finset.sum_const, Finset.card_univ]
      omega
    rw [h1, h2]
    omega
  have h1 := N.xNet.numVertices_eq (N.xNet_noIso hN)
  have h2 := N.numVertices_eq hN
  have h3 := N.xNet.numEdges_eq
  have h3' : ∑ a, (N.xNet.rotList a).length = ∑ a, (N.xList a).length := rfl
  have h4 := N.toRot.card_eq
  have h5 := N.toRot.euler hP hc
  have h6 := XNode.card_eq (V := V) (D := N.G.Dart)
  have h7 : N.toRot.numEdges = Fintype.card N.G.Dart / 2 := N.toRot.numEdges_eq
  omega

end Net

end SsspFlow.Congest
