import SsspFlow.GHatRot
import SsspFlow.NetPad
import SsspFlow.GHatDist
import SsspFlow.Chord

/-!
# The repaired graph is planar

Property (3) of Lemma R. Every face of the rotation system `hRot` of Table R carries one of four
labels: a wheel `W(d)` at each dart of `G`, a quad `Q(e)` at each edge, a face `F(f)` at each face of
`G`, and a lens `L(d)` at each incised dart (`lab`). The label of a dart is invariant along faces
(`lab_face`), and every label occurs (`lab_surj`), so the full repaired graph has at least
`|E| + |E|/2 + f + |inc|` faces, where `|E|` counts the darts of `G` (`numFaces_hRot`). With its
edges (`numEdges_hRot`), its vertices (`numVertices_hRot`) and Euler's formula for `G`, this gives
`E + 2 ≤ V + F`. The full graph is connected (`hRot_connected`), so it is planar (`hRot_planar`).

`Ĝ_ℓ` keeps every edge except the rims that are no E_C edges (`keep`). Its rotation system `gRot`
is the restriction, so it is planar (`gRot_planar`). Each kept dart is an arc of the multigraph
`Arc` of `Ĝ_ℓ` between the same copies (`arc_of_keep`), and each arc is a kept dart
(`keep_of_arc`). Two kept darts start at one vertex of `gRot` exactly when they start at one copy
(`gRot_tail_iff`).

The face invariance needs one condition on the data of a level (`NoConflict`): no incised dart has
its tail corner cut in mode R and its head corner cut in mode L. Any number of cut corners is
allowed, at any vertices.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

universe u

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E}

/-- The edges of `G`: the orbits of `rev`. -/
abbrev EdgeQ (G : RotSystem E) : Type u := Quotient (Equiv.Perm.SameCycle.setoid G.revPerm)

/-- The edge of a dart. -/
def edgeOf (G : RotSystem E) (x : E) : G.EdgeQ := Quotient.mk _ x

@[simp] theorem edgeOf_rev (x : E) : G.edgeOf (G.rev x) = G.edgeOf x := by
  show Quotient.mk _ _ = Quotient.mk _ _
  rw [Quotient.eq]
  exact ⟨1, by simp [G.rev_rev]⟩

attribute [local simp] faceOf_rev_rot

@[simp] theorem rev_rev' (c : E) : G.rev (G.rev c) = c := G.rev_rev c

theorem edgeOf_eq_iff (x y : E) : G.edgeOf x = G.edgeOf y ↔ G.toHypermap.cedge x y := by
  show Quotient.mk _ x = Quotient.mk _ y ↔ fconnect G.toHypermap.edge x y
  rw [Quotient.eq]
  exact (sameCycle_iff_fconnect G.revPerm).trans (fconnect_congr fun _ => rfl)

/-- `numEdges` counts the edges. -/
theorem natCard_edgeQ : Nat.card G.EdgeQ = G.numEdges := by
  have hs : ConnectSym (frel G.toHypermap.edge) := G.toHypermap.cedge_sym
  have key : ∀ x ∈ (Set.univ : Set E), ∀ y ∈ (Set.univ : Set E),
      G.edgeOf x = G.edgeOf y ↔
        comp (frel G.toHypermap.edge) x = comp (frel G.toHypermap.edge) y := by
    intro x _ y _
    rw [comp_eq_iff hs]
    exact edgeOf_eq_iff x y
  have h := ncard_image_eq_of_ker G.edgeOf (comp (frel G.toHypermap.edge)) key
  have hu : G.edgeOf '' Set.univ = Set.univ :=
    Set.eq_univ_of_forall fun v => Quotient.inductionOn v fun x => ⟨x, trivial, rfl⟩
  rw [hu, Set.ncard_univ] at h
  exact h

/-- A rotation system in which every dart is in the component of one dart is connected. -/
theorem connected_of_gcomp {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D) (x0 : D)
    (h : ∀ x, R.toHypermap.gcomp x x0) : R.Connected := by
  have hs := R.toHypermap.glinkC
  unfold Connected Hypermap.Connected nComp
  rw [Set.ncard_eq_one]
  refine ⟨comp R.toHypermap.glink x0, Set.ext fun s => ?_⟩
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact (comp_eq_iff hs).2 (h x)
  · rintro rfl
    exact ⟨x0, rfl⟩

namespace RData

variable (S : G.RData)

/-- The face labels: wheels, quads, faces of `G`, lenses. -/
abbrev FL : Type u := E ⊕ G.EdgeQ ⊕ G.Face ⊕ {d : E // d ∈ S.inc}

variable {S}

/-- The wheel at a dart. -/
def labW (d : E) : S.FL := Sum.inl d
/-- The quad at the edge of a dart. -/
def labQ (d : E) : S.FL := Sum.inr (Sum.inl (G.edgeOf d))
/-- The face of `G` of the note on the left of a dart. -/
def labF (d : E) : S.FL := Sum.inr (Sum.inr (Sum.inl (G.faceOf (G.rev d))))
/-- The lens at an incised dart. -/
def labL (d : E) (h : d ∈ S.inc) : S.FL := Sum.inr (Sum.inr (Sum.inr ⟨d, h⟩))

@[simp] theorem labQ_rev (d : E) : (labQ (G.rev d) : S.FL) = labQ d := by simp [labQ]

variable (S)

theorem inc_of_one {d : E} (h : S.IsTok (d, .one)) : d ∈ S.inc := by simpa [IsTok] using h
theorem inc_of_two {d : E} (h : S.IsTok (d, .two)) : d ∈ S.inc := by simpa [IsTok] using h

/-- The label of a dart of `H⁺`. -/
def lab : S.HD → S.FL
  | (.sp c, b) => if b then labW c else labW (G.rot c)
  | (.rim d, b) => if b then labQ d else labW d
  | (.tok ⟨(d, .zero), _⟩, b) => if b then labF d else labQ d
  | (.tok ⟨(d, .one), h⟩, b) =>
    if S.Opt d then (if b then labL d (S.inc_of_one h) else labQ d)
    else (if b then labF d else labL d (S.inc_of_one h))
  | (.tok ⟨(d, .two), h⟩, b) =>
    if S.Opt d then (if b then labF d else labL d (S.inc_of_two h))
    else (if b then labL d (S.inc_of_two h) else labQ d)
  | (.lsp ⟨a, ha⟩, b) =>
    if S.Opt a then (if b then labQ a else labL a ha) else (if b then labL a ha else labF a)
  | (.rsp ⟨d, hd⟩, b) =>
    if S.Opt d then (if b then labF d else labL d hd) else (if b then labL d hd else labQ d)
  | (.xsp ⟨c, _⟩, b) =>
    if S.modeL c then
      (if b then labW c else if h : G.rev c ∈ S.inc then labL (G.rev c) h else labF (G.rev c))
    else
      (if b then (if h : G.rot c ∈ S.inc then labL (G.rot c) h else labF (G.rot c))
        else labW (G.rot c))

/-- No incised dart has its tail corner cut in mode R and its head corner cut in mode L. -/
def NoConflict : Prop := ∀ d ∈ S.inc, ¬ (S.Opt d ∧ S.MovA (G.rev d))

@[simp] theorem opt_rot (c : E) : S.Opt (G.rot c) ↔ S.MovB c := by simp [Opt]

/-- Two darts in a row in a list: the label of the reverse of the second is that of the first. -/
def Step (x y : S.HD) : Prop := S.lab (S.hrev y) = S.lab x

set_option maxHeartbeats 2000000 in
theorem chain_dc (hN : S.NoConflict) (c : E) :
    List.IsChain S.Step (S.lst (.dc c) ++ (S.lst (.dc c)).take 1) := by
  have hN' : G.rev c ∈ S.inc → ¬ (S.Opt (G.rev c) ∧ S.MovA c) := fun h => by
    simpa using hN _ h
  have hAB : S.MovA c → ¬ S.MovB c := S.not_movB_of_movA
  have hA1 : S.MovA c → S.modeL c = true := fun h => h.2
  have hB1 : S.MovB c → S.modeL c = false := fun h => h.2
  simp only [lst, dList, segA, segB, entA, entB]
  split_ifs <;> simp [Step, lab, hrev, labF, *] <;> simp_all

theorem chain_lc (c : E) : List.IsChain S.Step (S.lst (.lc c) ++ (S.lst (.lc c)).take 1) := by
  simp only [lst, lList]
  split_ifs <;> simp [Step, lab, hrev, *]

theorem chain_rc (c : E) : List.IsChain S.Step (S.lst (.rc c) ++ (S.lst (.rc c)).take 1) := by
  simp only [lst, rList]
  split_ifs <;> simp [Step, lab, hrev, *]

set_option maxHeartbeats 1000000 in
theorem chain_xc (hN : S.NoConflict) (c : E) :
    List.IsChain S.Step (S.lst (.xc c) ++ (S.lst (.xc c)).take 1) := by
  have hN' : G.rev c ∈ S.inc → ¬ (S.Opt (G.rev c) ∧ S.MovA c) := fun h => by
    simpa using hN _ h
  simp only [lst, xList]
  by_cases ha : G.rev c ∈ S.inc <;> by_cases hb : G.rot c ∈ S.inc <;>
    split_ifs <;> simp [Step, lab, hrev, labF, firstLab, lastLab, MovA, MovB, *] <;> simp_all [MovA]

/-- The label is invariant along the faces of `hRot`. -/
theorem lab_face (hN : S.NoConflict) (z : S.HD) :
    S.lab (S.hRot.rev (S.hRot.rot z)) = S.lab z := by
  refine S.listData.lab_rev_rot_of_mem S.lab (fun v x hx => ?_) z
  show S.lab (S.hrev ((S.lst v).formPerm x)) = S.lab x
  cases v with
  | star v =>
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx
    have hinj : Function.Injective fun c : E => (fw (HE.sp c) : S.HD) := fun a b h => by
      simpa using h
    simp only [lst]
    rw [formPerm_map_apply hinj (G.starList_nodup v) hc', formPerm_starList hc']
    simp [lab, hrev]
  | dc c => exact rel_formPerm_of_isChain (S.lst_nodup _) (S.chain_dc hN c) hx
  | lc c => exact rel_formPerm_of_isChain (S.lst_nodup _) (S.chain_lc c) hx
  | rc c => exact rel_formPerm_of_isChain (S.lst_nodup _) (S.chain_rc c) hx
  | xc c => exact rel_formPerm_of_isChain (S.lst_nodup _) (S.chain_xc hN c) hx

/-! ### Every label occurs -/

theorem lab_surj : Function.Surjective S.lab := by
  rintro (d | e | f | ⟨d, hd⟩)
  · exact ⟨fw (HE.rim d), by simp [lab, labW]⟩
  · obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    exact ⟨bw (HE.rim d), by simp [lab, labQ]; rfl⟩
  · obtain ⟨x, rfl⟩ := Quotient.exists_rep f
    by_cases hd : G.rev x ∈ S.inc
    · by_cases ho : S.Opt (G.rev x)
      · exact ⟨bw (HE.tok ⟨(G.rev x, .two), S.isTok_two hd⟩), by simp [lab, labF, ho]; rfl⟩
      · exact ⟨bw (HE.tok ⟨(G.rev x, .one), S.isTok_one hd⟩), by simp [lab, labF, ho]; rfl⟩
    · exact ⟨bw (HE.tok ⟨(G.rev x, .zero), S.isTok_zero hd⟩), by simp [lab, labF]; rfl⟩
  · by_cases ho : S.Opt d
    · exact ⟨fw (HE.tok ⟨(d, .two), S.isTok_two hd⟩), by simp [lab, labL, ho]⟩
    · exact ⟨fw (HE.tok ⟨(d, .one), S.isTok_one hd⟩), by simp [lab, labL, ho]⟩

/-! ### Counting -/

/-- The tokens: one at each dart outside `inc`, two at each dart in `inc`. -/
def tokEquiv : S.Tok ≃ E ⊕ {d : E // d ∈ S.inc} where
  toFun
    | ⟨(d, .zero), _⟩ => .inl d
    | ⟨(d, .one), _⟩ => .inl d
    | ⟨(d, .two), h⟩ => .inr ⟨d, S.inc_of_two h⟩
  invFun
    | .inl d => ⟨(d, S.firstLab d), S.isTok_first d⟩
    | .inr d => ⟨(d.1, .two), S.isTok_two d.2⟩
  left_inv := by
    rintro ⟨⟨d, l⟩, h⟩
    have h' := h
    simp only [IsTok] at h'
    cases l
    · exact Subtype.ext (by simp_all [firstLab])
    · exact Subtype.ext (by simp_all [firstLab])
    · rfl
  right_inv := by
    rintro (d | ⟨d, hd⟩)
    · by_cases h : d ∈ S.inc <;> simp [firstLab, h]
    · rfl

theorem card_HE : Fintype.card S.HE = 3 * Fintype.card E + 3 * S.inc.card + S.cut.card := by
  classical
  rw [Fintype.card_congr S.heEquiv]
  simp only [Fintype.card_sum, Fintype.card_congr S.tokEquiv, Fintype.card_coe]
  ring

theorem numEdges_hRot : S.hRot.numEdges = 3 * Fintype.card E + 3 * S.inc.card + S.cut.card := by
  rw [RotSystem.numEdges_eq, Fintype.card_prod, Fintype.card_bool, card_HE]
  omega

theorem numVertices_hRot :
    Nat.card G.Vertex + Fintype.card E + 2 * S.inc.card + S.cut.card ≤ S.hRot.numVertices := by
  classical
  rw [hRot, ListData.numVertices_eq]
  let f : G.Vertex ⊕ E ⊕ {a : E // a ∈ S.inc} ⊕ {b : E // b ∈ S.inc} ⊕ {c : E // c ∈ S.cut} →
      Copy G.Vertex E
    | .inl v => .star v
    | .inr (.inl c) => .dc c
    | .inr (.inr (.inl a)) => .lc (G.rev a.1)
    | .inr (.inr (.inr (.inl b))) => .rc (G.tailCorner b.1)
    | .inr (.inr (.inr (.inr c))) => .xc c.1
  have hf : Function.Injective f := by
    rintro (v | c | a | b | c) (v' | c' | a' | b' | c') h <;>
      simp only [f, Copy.star.injEq, Copy.dc.injEq, Copy.lc.injEq, Copy.rc.injEq, Copy.xc.injEq,
        reduceCtorEq] at h
    all_goals first
      | (subst h; rfl)
      | exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z))) (Subtype.ext (by
          simpa using congrArg G.rev h))
      | exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr (Sum.inl z))))
          (Subtype.ext (G.rot.symm.injective h))
      | exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr (Sum.inr z)))) (Subtype.ext h)
  have hsub : Finset.univ.image f ⊆ Finset.univ.image S.listData.tl := by
    intro u hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨y, rfl⟩ := hu
    rcases y with v | c | ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨c, hc⟩
    · exact ⟨fw (HE.sp (Quotient.out v)), by simp [listData, ends, f, tail_out]⟩
    · exact ⟨bw (HE.sp c), by simp [listData, ends, f]⟩
    · exact ⟨bw (HE.lsp ⟨a, ha⟩), by simp [listData, ends, f, headCorner]⟩
    · exact ⟨bw (HE.rsp ⟨b, hb⟩), by simp [listData, ends, f]⟩
    · exact ⟨bw (HE.xsp ⟨c, hc⟩), by simp [listData, ends, f]⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ] at h1
  simp only [Fintype.card_sum, Fintype.card_coe] at h1
  rw [Nat.card_eq_fintype_card]
  omega

theorem numFaces_hRot (hN : S.NoConflict) :
    Fintype.card E + G.numEdges + G.numFaces + S.inc.card ≤ S.hRot.numFaces := by
  have h := S.hRot.card_le_numFaces S.lab (S.lab_face hN) S.lab_surj
  rw [Nat.card_sum, Nat.card_sum, Nat.card_sum, natCard_edgeQ, natCard_face,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe] at h
  omega

/-! ### Connectivity -/

/-- The first dart at the star centre of a vertex. -/
noncomputable def star0 (v : G.Vertex) : S.HD := fw (HE.sp (Quotient.out v))

theorem gc_tl {x y : S.HD} (h : S.tl x = S.tl y) : S.hRot.toHypermap.gcomp x y :=
  S.hRot.toHypermap.gcomp_of_cnode
    ((RotSystem.tail_eq_iff _ x y).1 ((S.listData.tail_eq_iff x y).2 h))

theorem gc_rev (x : S.HD) : S.hRot.toHypermap.gcomp x (S.hrev x) :=
  connect_of_rel (S.hRot.toHypermap.glinkE x)

theorem gc_symm {x y : S.HD} (h : S.hRot.toHypermap.gcomp x y) : S.hRot.toHypermap.gcomp y x :=
  S.hRot.toHypermap.glinkC x y h

theorem gc_dc (c : E) (x : S.HD) (hx : S.tl x = .dc c) :
    S.hRot.toHypermap.gcomp x (S.star0 (G.tail c)) :=
  connect_trans (S.gc_tl (y := bw (HE.sp c)) (by simpa [ends] using hx))
    (connect_trans (S.gc_rev _) (S.gc_tl (by simp [star0, hrev, ends, tail_out])))

/-- Every dart is in the component of the star centre of its vertex of `G`. -/
theorem gc_star (x : S.HD) : S.hRot.toHypermap.gcomp x (S.star0 (G.owner (S.tl x))) := by
  have hm := S.mem_lst_tl x
  obtain ⟨u, hu⟩ : ∃ u, S.tl x = u := ⟨_, rfl⟩
  rw [hu] at hm ⊢
  cases u with
  | star v => exact S.gc_tl (by simp [hu, star0, ends, tail_out, owner])
  | dc c => exact S.gc_dc c x hu
  | lc c =>
    have ha : G.rev c ∈ S.inc := by
      by_contra h; simp [lst, lList, h] at hm
    have hy : S.tl (bw (HE.lsp ⟨G.rev c, ha⟩)) = .lc c := by simp [ends, headCorner]
    exact connect_trans (S.gc_tl (hu.trans hy.symm))
      (connect_trans (S.gc_rev _) (S.gc_dc c _ (by simp [hrev, ends, headCorner])))
  | rc c =>
    have hb : G.rot c ∈ S.inc := by
      by_contra h; simp [lst, rList, h] at hm
    have hy : S.tl (bw (HE.rsp ⟨G.rot c, hb⟩)) = .rc c := by simp [ends]
    exact connect_trans (S.gc_tl (hu.trans hy.symm))
      (connect_trans (S.gc_rev _) (S.gc_dc c _ (by simp [hrev, ends])))
  | xc c =>
    have hc : c ∈ S.cut := by
      by_contra h; simp [lst, xList, h] at hm
    have hy : S.tl (bw (HE.xsp ⟨c, hc⟩)) = .xc c := by simp [ends]
    exact connect_trans (S.gc_tl (hu.trans hy.symm))
      (connect_trans (S.gc_rev _) (S.gc_dc c _ (by simp [hrev, ends])))

/-- The star centres at the two ends of an edge of `G` are in one component. -/
theorem gc_cross (d : E) :
    S.hRot.toHypermap.gcomp (S.star0 (G.tail d)) (S.star0 (G.head d)) := by
  let t : S.HE := HE.tok ⟨(d, S.firstLab d), S.isTok_first d⟩
  have h1 := S.gc_star (fw t)
  have h2 := S.gc_star (bw t)
  simp only [tl_fw, tl_bw, ends, t, owner_alpha, owner_beta] at h1 h2
  exact connect_trans (S.gc_symm h1) (connect_trans (S.gc_rev _) h2)

theorem hRot_connected (hc : G.Connected) : S.hRot.Connected := by
  obtain ⟨⟨e0⟩, -⟩ := G.connected_iff.1 hc
  refine connected_of_gcomp _ (S.star0 (G.tail e0)) fun x => ?_
  refine connect_trans (S.gc_star x) ?_
  obtain ⟨a, ha⟩ := G.exists_tail_eq (G.owner (S.tl x))
  rw [← ha]
  have hg : G.toHypermap.gcomp a e0 :=
    connect_of_nComp_eq_one G.toHypermap.glinkC hc (Set.mem_univ a) (Set.mem_univ e0)
  induction hg with
  | refl => exact connect_refl _
  | @tail b z _ hbz ih =>
    refine connect_trans ih ?_
    rcases hbz with h | h | h
    · rw [← h]; exact S.gc_cross b
    · rw [← h]; simp only [toHypermap_node, G.tail_rot]; exact connect_refl _
    · rw [← h]
      simp only [toHypermap_face, G.tail_rot_symm]
      exact S.gc_cross b

/-- **The full repaired graph is planar**, for a connected planar `G` and data without conflict. -/
theorem hRot_planar (hP : G.Planar) (hc : G.Connected) (hN : S.NoConflict) : S.hRot.Planar := by
  refine S.hRot.planar_of_count (S.hRot_connected hc) ?_
  have hE := S.numEdges_hRot
  have hV := S.numVertices_hRot
  have hF := S.numFaces_hRot hN
  have hEu := G.euler hP hc
  have hcard := G.card_eq
  rw [← G.natCard_vertex] at hEu
  omega

/-! ### The repaired graph of a level -/

/-- The edges of `Ĝ_ℓ`: all edges of the full graph except the rims that are no E_C edges. The rim
across `d` at its tail is the E_C edge of the pair hosted there. -/
def Keep : S.HE → Prop
  | .rim d => d ∈ S.inc ∨ S.hostT d = true
  | _ => True

instance (e : S.HE) : Decidable (S.Keep e) := by
  cases e <;> unfold Keep <;> infer_instance

/-- The darts of `Ĝ_ℓ`. -/
noncomputable def keep : Finset S.HD := Finset.univ.filter fun x => S.Keep x.1

/-- The rotation system of `Ĝ_ℓ`: the full graph restricted to the kept darts. -/
noncomputable def gRot : RotSystem S.HD := S.hRot.restrict S.keep

/-- **Property (3): `Ĝ_ℓ` is planar.** -/
theorem gRot_planar (hP : G.Planar) (hc : G.Connected) (hN : S.NoConflict) : S.gRot.Planar :=
  planar_restrict (S.hRot_planar hP hc hN) _

/-- Two kept darts start at one vertex of `Ĝ_ℓ` exactly when they start at one copy. -/
theorem gRot_tail_iff {x y : S.HD} (hx : x ∈ S.keep) (hy : y ∈ S.keep) :
    S.gRot.tail x = S.gRot.tail y ↔ S.tl x = S.tl y :=
  (tail_restrict_iff hx hy).trans (S.listData.tail_eq_iff x y)

theorem gRot_rev (x : S.HD) : S.gRot.rev x = S.hrev x := rfl

theorem att_of_atTail {x : E × Lab} (hx : S.IsTok x) (h : S.atTail x = true) :
    S.att x = S.alphaD (G.tailCorner x.1) ∧ S.att (G.partner x) = S.betaD x.1 := by
  obtain ⟨d, l⟩ := x
  cases l
  · have hd : d ∉ S.inc := by simpa [IsTok] using hx
    simp_all [att, atTail, alpha, beta, partner, Lab.swap, S.hostT_rev d hd, headCorner]
  · simp_all [att, atTail, alpha, beta, partner, Lab.swap, headCorner]
  · simp [atTail] at h

/-- Each kept dart is an arc of `Ĝ_ℓ` between the same copies. -/
theorem arc_of_keep (x : S.HD) (hx : x ∈ S.keep) :
    Nonempty (S.Arc (S.tl x) (S.tl (S.hrev x))) := by
  obtain ⟨e, b⟩ := x
  simp only [keep, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  cases e with
  | sp c =>
    cases b
    · exact ⟨.es (a := .star (G.tail c)) (b := .dc c) rfl⟩
    · exact ⟨.es' (a := .star (G.tail c)) (b := .dc c) rfl⟩
  | rim d =>
    simp only [Keep] at hx
    have key : ∃ y : S.Tok, S.att y.1 = S.alphaD (G.tailCorner d) ∧
        S.att (G.partner y.1) = S.betaD d := by
      by_cases hd : d ∈ S.inc
      · exact ⟨⟨(d, .one), S.isTok_one hd⟩, S.att_of_atTail (x := (d, .one)) (S.isTok_one hd) rfl⟩
      · have hh : S.hostT d = true := by simpa [hd] using hx
        exact ⟨⟨(d, .zero), S.isTok_zero hd⟩, S.att_of_atTail (x := (d, .zero)) (S.isTok_zero hd) hh⟩
    obtain ⟨y, h1, h2⟩ := key
    have hpp : S.att (G.partner (S.partnerTok y).1) = S.att y.1 := by
      simp [partnerTok]
    cases b
    · show Nonempty (S.Arc (S.alphaD (G.tailCorner d)) (S.betaD d))
      rw [← h1, ← h2]
      exact ⟨.ec y⟩
    · show Nonempty (S.Arc (S.betaD d) (S.alphaD (G.tailCorner d)))
      rw [← h1, ← h2, ← hpp]
      exact ⟨.ec (S.partnerTok y)⟩
  | tok y =>
    cases b
    · exact ⟨.er y⟩
    · exact ⟨.er' y⟩
  | lsp a =>
    obtain ⟨a, ha⟩ := a
    have h : S.ES (.dc (G.headCorner a)) (.lc (G.headCorner a)) :=
      ⟨rfl, by simpa [inDart, headCorner] using ha⟩
    cases b
    · exact ⟨.es h⟩
    · exact ⟨.es' h⟩
  | rsp b' =>
    obtain ⟨b', hb⟩ := b'
    have h : S.ES (.dc (G.tailCorner b')) (.rc (G.tailCorner b')) :=
      ⟨rfl, by simpa [outDart, tailCorner] using hb⟩
    cases b
    · exact ⟨.es h⟩
    · exact ⟨.es' h⟩
  | xsp c =>
    obtain ⟨c, hc⟩ := c
    have h : S.ES (.dc c) (.xc c) := ⟨rfl, hc⟩
    cases b
    · exact ⟨.es h⟩
    · exact ⟨.es' h⟩

/-- Each arc of `Ĝ_ℓ` is a kept dart between the same copies. -/
theorem keep_of_arc : ∀ (a b : Copy G.Vertex E), S.Arc a b →
    ∃ x ∈ S.keep, S.tl x = a ∧ S.tl (S.hrev x) = b := by
  have hk : ∀ x : S.HD, S.Keep x.1 → x ∈ S.keep := fun x h => by simp [keep, h]
  have hES : ∀ a b : Copy G.Vertex E, S.ES a b →
      ∃ x ∈ S.keep, S.tl x = a ∧ S.tl (S.hrev x) = b := by
    intro a b h
    cases a <;> cases b <;> simp only [ES] at h
    · exact ⟨fw (HE.sp _), hk _ trivial, by simp [ends, h], rfl⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨fw (HE.lsp ⟨_, h⟩), hk _ trivial, by simp [ends, inDart, headCorner],
        by simp [hrev, ends, inDart, headCorner]⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨fw (HE.rsp ⟨_, h⟩), hk _ trivial, by simp [ends, outDart, tailCorner],
        by simp [hrev, ends, outDart, tailCorner]⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨fw (HE.xsp ⟨_, h⟩), hk _ trivial, rfl, rfl⟩
  intro a b e
  cases e with
  | er y => exact ⟨fw (HE.tok y), hk _ trivial, rfl, rfl⟩
  | er' y => exact ⟨bw (HE.tok y), hk _ trivial, rfl, rfl⟩
  | es h => exact hES _ _ h
  | es' h =>
    obtain ⟨x, hx, h1, h2⟩ := hES _ _ h
    exact ⟨S.hrev x, hk _ (by simpa [keep, hrev] using hx), h2, by simpa [hrev] using h1⟩
  | ec y =>
    obtain ⟨⟨d, l⟩, hy⟩ := y
    have hy' := hy
    simp only [IsTok] at hy'
    by_cases ht : S.atTail (d, l) = true
    · obtain ⟨h1, h2⟩ := S.att_of_atTail hy ht
      refine ⟨fw (HE.rim d), hk _ ?_, by simpa [ends] using h1.symm, by simpa [hrev, ends] using h2.symm⟩
      cases l <;> simp_all [Keep, atTail]
    · cases l with
      | one => simp [atTail] at ht
      | two =>
        have hd : d ∈ S.inc := by simpa [IsTok] using hy
        refine ⟨bw (HE.rim (G.rev d)), hk _ (Or.inl ((S.inc_rev d).2 hd)), ?_, ?_⟩ <;>
          simp [ends, hrev, att, atTail, alpha, beta, partner, Lab.swap, headCorner]
      | zero =>
        have hd : d ∉ S.inc := by simpa [IsTok] using hy
        have hh : S.hostT d = false := by simpa [atTail] using ht
        have hr : S.hostT (G.rev d) = true := by simp [S.hostT_rev d hd, hh]
        refine ⟨bw (HE.rim (G.rev d)), hk _ (Or.inr hr), ?_, ?_⟩ <;>
          simp [ends, hrev, att, atTail, alpha, beta, partner, Lab.swap, headCorner, hh, hr]

end RData

end RotSystem

end SsspFlow
