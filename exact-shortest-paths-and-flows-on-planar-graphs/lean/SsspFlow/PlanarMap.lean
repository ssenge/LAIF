import FourColor.Snip
import Mathlib.Data.Fin.VecNotation
import SsspFlow.LemmaD

/-!
# Rotation systems and hypermaps

A graph with a rotation system as in `notes/GHAT_REPAIR.md`, and its bridge to the hypermap library
`FourColor`, which supplies planarity and the cut along a cycle.

`RotSystem D` has the darts `D`, the reversal `rev`, an involution without fixed points, and the
rotation `rot`, which steps from `r_v(i)` to `r_v(i+1)`. Vertices are the `rot`-orbits (`Vertex`,
`tail`, `head`), so every vertex has a dart; loops and parallel edges are allowed. The corner
`(v, i)` between `r_v(i)` and `r_v(i+1)` is named by its first flank `r_v(i)`, and `inDart`,
`outDart`, `tailCorner`, `headCorner` are `in`, `out`, `τ`, `η` of the note. `toHypermap` has
`edge := rev`, `node := rot`, `face := rot⁻¹ ∘ rev`, the last being forced by `edgeK`. It is plain
(`plain`), and `Face` is the type of its face orbits. `dual` is the dual rotation system, with
rotation `rev ∘ rot` (`dual_toHypermap`, `dual_dual`), and `mirror` inverts the rotation.

The two face permutations differ. The face walk of the note follows `δ` by `out (η δ) =
rot (rev δ)`, which is `noteFace`, while `toHypermap.face` is `rot⁻¹ ∘ rev`. By `noteFace_eq_conj`,
`noteFace = rev ∘ face⁻¹ ∘ rev`, so the faces of the note are the sets of reverses of the faces of
the hypermap, and they are equal in number (`sameCycle_noteFace_rev`, `fcard_noteFace`). On corners,
`face (η δ) = τ δ` and `τ (noteFace δ) = η δ` (`facePerm_headCorner`, `tailCorner_noteFace`), so a
step of `face` is a step backwards along the face walk of the note, and the orbits of `face` are the
faces of the note as sets of corners. The face permutation of the mirror is `noteFace`
(`mirror_facePerm`).

`SsspFlow.LemmaD` takes a combinatorial map `(α, φ)` with a free `φ`. For an involutive `α` without
fixed points, `ofMap` gives the rotation system with rotation `α ∘ φ⁻¹`, whose face permutation is
`φ` (`ofMap_facePerm`, `ofMap_face`), and every rotation system arises so
(`ofMap_revPerm_facePerm`). `toSetup` is the face-disjoint graph of that module for `φ := face`,
with corners named by the first flank, and `noteSetup` is the one for `φ := noteFace`, with `d`
standing for the corner `τ d`. Renaming corners by `rot` carries the rings, the spokes and the arcs
of the first to those of the second, the arcs with their directions reversed (`toSetup_rg_iff`,
`toSetup_spoke_iff`, `toSetup_arc`). `FaceDisjoint.rot_lemmaD` applies to both.

`Planar` and `Connected` are those of the hypermap; by `connected_iff`, the second says that there
is a dart and that walks (`IsWalk`) join all vertices. `numVertices`, `numFaces`, `numEdges` count
the orbits of `node`, `face`, `edge` (`natCard_vertex`, `natCard_face`, `numEdges_eq`, which says
`numEdges = card D / 2`). `genus_formula` holds for every rotation system. `euler` is
`V + F = E + 2` for connected planar `R`, `euler_card` and `euler_note` are the same with
`Nat.card` and with the faces of the note, and `planar_iff_euler` is the converse.

A simple cycle is a list of darts in which the head of each is the tail of the next, cyclically, and
the tails are distinct (`IsRing`). It is exactly a simple `rlink` cycle of the dual map `dualMap`,
whose faces are the vertices (`isRing_iff`). `IsRing` also holds for `[]` and `[d, rev d]`, and
`IsCycle` excludes these. The sides are those of the library's `Snip` on the dual map: `inside c` is
`diskE c`, which is `diskN c` without `c`, and `outside c` is the complement of `diskN c`.
`rot_symm_rev_mem_inside` and `rev_cycle_mem_outside` show which side is which.

* Exactly one side. Every dart off the cycle lies on exactly one side (`exactly_one_side`), and so
  does every vertex off the cycle (`vertex_exactly_one_side`). Both hold without planarity, the
  first by construction. Planarity enters through `diskE_edge`: both darts of an edge off the cycle
  lie on the same side (`rev_mem_inside_iff`, `rev_mem_outside`, `edge_exactly_one_side`).
* Separation. For planar `R`, a walk from one side to the other passes through a vertex of the
  cycle: `walk_meets_cycle`, `walk_meets_cycle'` for darts linked head to tail, and
  `isWalk_meets_cycle`, `isWalk_meets_cycle'` for walks between vertices.
* The cut. `insideMap` and `outsideMap` are the planar maps of the two sides
  (`insideMap_planar`, `outsideMap_planar`, `patch_inside_outside`).
* Reversal. A component that does not meet the cycle counts as outside, so this needs `Connected`.
  For connected planar `R` and `IsCycle c`, the outside of `reverseCycle c` is `c` and the inside of
  `c`, and its inside is the outside of `c` without the reverses of `c`
  (`mem_outside_reverseCycle_iff`, `mem_inside_reverseCycle_iff`). So `outside c` is a side in its
  own right, and not only a complement.

`triangle` is a triangle with a pendant edge on each side, planar and connected (`triangle_planar`,
`triangle_connected`), and `triangleCycle` is a cycle of it (`triangle_isCycle`). The sides of the
cycle and of its reversal are computed in `triangle_inside`, `triangle_outside`,
`triangle_inside_reverse`, `triangle_vertices`, so the statements on sides are not vacuous.

Not here: that a side is connected; that a side has a dart, which fails when the cycle runs around
a face; which side is bounded, and any embedding in the plane, since `Planar` is the property of the
hypermap; the incisions, tokens and modes of Definition R and the repaired graph `Ĝ` itself, as
`toSetup` and `noteSetup` have one node per corner and no incision; and the planarity of `Ĝ`.
-/

set_option autoImplicit false
namespace SsspFlow

open FourColor

/-- A rotation system: darts, the reversal of darts, and the rotation at the tail vertex. -/
@[ext]
structure RotSystem (D : Type*) [Fintype D] [DecidableEq D] where
  /-- The reverse dart. -/
  rev : D → D
  /-- `rev` is an involution. -/
  rev_rev : ∀ x, rev (rev x) = x
  /-- `rev` has no fixed point: every edge has two darts. -/
  rev_ne : ∀ x, rev x ≠ x
  /-- The rotation: `rot x` is the dart after `x` in the rotation order at the tail of `x`. -/
  rot : Equiv.Perm D

namespace RotSystem

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-! ### The hypermap -/

/-- The hypermap of a rotation system: `edge := rev`, `node := rot`, `face := rot⁻¹ ∘ rev`. -/
def toHypermap : Hypermap D where
  edge := R.rev
  node := R.rot
  face := fun x => R.rot.symm (R.rev x)
  edgeK := fun x => by rw [R.rev_rev, Equiv.apply_symm_apply]

@[simp] theorem toHypermap_edge (x : D) : R.toHypermap.edge x = R.rev x := rfl
@[simp] theorem toHypermap_node (x : D) : R.toHypermap.node x = R.rot x := rfl
@[simp] theorem toHypermap_face (x : D) : R.toHypermap.face x = R.rot.symm (R.rev x) := rfl

/-- Every edge orbit has size two. -/
theorem plain : R.toHypermap.Plain :=
  R.toHypermap.plainP.2 fun x _ => ⟨R.rev_rev x, R.rev_ne x⟩

/-- `rev` as a permutation. -/
def revPerm : Equiv.Perm D := Function.Involutive.toPerm R.rev R.rev_rev

@[simp] theorem revPerm_apply (x : D) : R.revPerm x = R.rev x := rfl
@[simp] theorem revPerm_symm_apply (x : D) : R.revPerm.symm x = R.rev x := rfl

/-- The face permutation of `toHypermap`, as a permutation. -/
def facePerm : Equiv.Perm D := R.revPerm.trans R.rot.symm

@[simp] theorem facePerm_apply (x : D) : R.facePerm x = R.toHypermap.face x := rfl
@[simp] theorem facePerm_symm_apply (x : D) : R.facePerm.symm x = R.rev (R.rot x) := rfl

/-! ### Vertices and faces as orbits -/

omit [DecidableEq D] in
/-- The orbits of a permutation on a finite type are its forward orbits. -/
theorem sameCycle_iff_fconnect (f : Equiv.Perm D) {x y : D} :
    f.SameCycle x y ↔ fconnect f x y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hn
    exact fconnect_iff_iterate.2 ⟨n, hn⟩
  · intro h
    obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 h
    exact ⟨n, by rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hn⟩

/-- The vertices: the orbits of `rot`. -/
abbrev Vertex : Type u := Quotient (Equiv.Perm.SameCycle.setoid R.rot)

/-- The tail vertex of a dart. -/
def tail (x : D) : R.Vertex := Quotient.mk _ x

/-- The head vertex of a dart: the tail of its reverse. -/
def head (x : D) : R.Vertex := R.tail (R.rev x)

theorem exists_tail_eq (v : R.Vertex) : ∃ x, R.tail x = v := Quotient.exists_rep v

theorem tail_eq_iff (x y : D) : R.tail x = R.tail y ↔ R.toHypermap.cnode x y := by
  show Quotient.mk _ x = Quotient.mk _ y ↔ fconnect (⇑R.rot) x y
  rw [Quotient.eq]
  exact sameCycle_iff_fconnect R.rot

theorem tail_rot (x : D) : R.tail (R.rot x) = R.tail x :=
  (R.tail_eq_iff _ _).2 ((R.toHypermap.cnodeC).1 (fconnect1 _ x))

theorem tail_rot_symm (x : D) : R.tail (R.rot.symm x) = R.tail x := by
  have h := R.tail_rot (R.rot.symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem head_rev (x : D) : R.head (R.rev x) = R.tail x := by
  show R.tail (R.rev (R.rev x)) = R.tail x
  rw [R.rev_rev]

/-- The faces: the orbits of the face permutation of `toHypermap`. -/
abbrev Face : Type u := Quotient (Equiv.Perm.SameCycle.setoid R.facePerm)

/-- The face of a dart. -/
def faceOf (x : D) : R.Face := Quotient.mk _ x

theorem faceOf_eq_iff (x y : D) : R.faceOf x = R.faceOf y ↔ R.toHypermap.cface x y := by
  show Quotient.mk _ x = Quotient.mk _ y ↔ fconnect R.toHypermap.face x y
  rw [Quotient.eq]
  exact (sameCycle_iff_fconnect R.facePerm).trans (fconnect_congr R.facePerm_apply)

/-- The number of vertices, as the library counts them: the `rot`-orbits. -/
noncomputable def numVertices : ℕ := fcard R.toHypermap.node Set.univ

/-- The number of faces, as the library counts them: the orbits of the face permutation. -/
noncomputable def numFaces : ℕ := fcard R.toHypermap.face Set.univ

/-- The number of edges, as the library counts them: the `rev`-orbits. -/
noncomputable def numEdges : ℕ := fcard R.toHypermap.edge Set.univ

/-- The number of connected components. -/
noncomputable def numComponents : ℕ := nComp R.toHypermap.glink Set.univ

/-- The image of a quotient map on the whole type is the whole quotient. -/
private theorem image_univ_quotient {α : Type*} (s : Setoid α) :
    (Quotient.mk s) '' Set.univ = Set.univ :=
  Set.eq_univ_of_forall fun v => Quotient.inductionOn v fun x => ⟨x, trivial, rfl⟩

/-- `numVertices` counts the type of vertices. -/
theorem natCard_vertex : Nat.card R.Vertex = R.numVertices := by
  have hs : ConnectSym (frel R.toHypermap.node) := R.toHypermap.cnode_sym
  have key : ∀ x ∈ (Set.univ : Set D), ∀ y ∈ (Set.univ : Set D),
      R.tail x = R.tail y ↔ comp (frel R.toHypermap.node) x = comp (frel R.toHypermap.node) y := by
    intro x _ y _
    rw [comp_eq_iff hs]
    exact R.tail_eq_iff x y
  have h := ncard_image_eq_of_ker R.tail (comp (frel R.toHypermap.node)) key
  rw [show R.tail '' Set.univ = Set.univ from image_univ_quotient _, Set.ncard_univ] at h
  exact h

/-- `numFaces` counts the type of faces. -/
theorem natCard_face : Nat.card R.Face = R.numFaces := by
  have hs : ConnectSym (frel R.toHypermap.face) := R.toHypermap.cface_sym
  have key : ∀ x ∈ (Set.univ : Set D), ∀ y ∈ (Set.univ : Set D),
      R.faceOf x = R.faceOf y ↔
        comp (frel R.toHypermap.face) x = comp (frel R.toHypermap.face) y := by
    intro x _ y _
    rw [comp_eq_iff hs]
    exact R.faceOf_eq_iff x y
  have h := ncard_image_eq_of_ker R.faceOf (comp (frel R.toHypermap.face)) key
  rw [show R.faceOf '' Set.univ = Set.univ from image_univ_quotient _, Set.ncard_univ] at h
  exact h

/-- An edge has two darts: the number of edges is half the number of darts. -/
theorem numEdges_eq : R.numEdges = Fintype.card D / 2 := by
  have h := fcard_order_set R.toHypermap.edgeI R.plain closed_univ
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  unfold numEdges
  omega

/-- The number of darts is even. -/
theorem card_eq : Fintype.card D = 2 * R.numEdges := by
  have h := fcard_order_set R.toHypermap.edgeI R.plain closed_univ
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  unfold numEdges
  omega

/-! ### Corners and the faces of the note

A corner `(v, i)` of the note lies between `r_v(i)` and `r_v(i+1)`. It is named here by the dart
`r_v(i)`, so that `rot` steps from a corner to the next one around `v`. -/

/-- `in(c) = rev r_v(i)`: the in-dart of the corner named `c = r_v(i)`. -/
def inDart (c : D) : D := R.rev c

/-- `out(c) = r_v(i+1)`: the out-dart of the corner named `c = r_v(i)`. -/
def outDart (c : D) : D := R.rot c

/-- `τ(δ)`: the tail corner of a dart, the corner with `out(c) = δ`. -/
def tailCorner (x : D) : D := R.rot.symm x

/-- `η(δ)`: the head corner of a dart, the corner with `in(c) = δ`. -/
def headCorner (x : D) : D := R.rev x

theorem outDart_tailCorner (x : D) : R.outDart (R.tailCorner x) = x := R.rot.apply_symm_apply x
theorem inDart_headCorner (x : D) : R.inDart (R.headCorner x) = x := R.rev_rev x
theorem tail_tailCorner (x : D) : R.tail (R.tailCorner x) = R.tail x := R.tail_rot_symm x
theorem tail_headCorner (x : D) : R.tail (R.headCorner x) = R.head x := rfl

/-- The face permutation of the note: `δ` is followed by `out (η δ) = rot (rev δ)`. -/
def noteFace : Equiv.Perm D := R.revPerm.trans R.rot

@[simp] theorem noteFace_apply (x : D) : R.noteFace x = R.rot (R.rev x) := rfl

theorem noteFace_eq_out_head (x : D) : R.noteFace x = R.outDart (R.headCorner x) := rfl

/-- The corner `η δ` lies between `δ` and its successor on the face of the note. -/
theorem tailCorner_noteFace (x : D) : R.tailCorner (R.noteFace x) = R.headCorner x :=
  R.rot.symm_apply_apply _

/-- On corners, the face permutation of the hypermap steps from `η δ` back to `τ δ`, one step
backwards along the face walk of the note. -/
theorem facePerm_headCorner (x : D) : R.facePerm (R.headCorner x) = R.tailCorner x := by
  show R.rot.symm (R.rev (R.rev x)) = R.rot.symm x
  rw [R.rev_rev]

/-- On darts, the face permutation of the note is the conjugate by `rev` of the inverse of the
face permutation of the hypermap. -/
theorem noteFace_rev (x : D) : R.noteFace (R.rev x) = R.rev (R.facePerm.symm x) := by
  simp only [noteFace_apply, facePerm_symm_apply, R.rev_rev]

theorem noteFace_eq_conj : R.noteFace = R.revPerm * R.facePerm⁻¹ * R.revPerm⁻¹ := by
  ext x
  show R.noteFace x = R.revPerm (R.facePerm.symm (R.revPerm.symm x))
  rw [revPerm_symm_apply, revPerm_apply, ← R.noteFace_rev, R.rev_rev]

/-- The faces of the note are the sets of reverses of the faces of the hypermap. -/
theorem sameCycle_noteFace_rev (x y : D) :
    R.noteFace.SameCycle (R.rev x) (R.rev y) ↔ R.toHypermap.cface x y := by
  rw [noteFace_eq_conj, Equiv.Perm.sameCycle_conj, Equiv.Perm.sameCycle_inv]
  show R.facePerm.SameCycle (R.rev (R.rev x)) (R.rev (R.rev y)) ↔ _
  rw [R.rev_rev, R.rev_rev]
  exact (sameCycle_iff_fconnect R.facePerm).trans (fconnect_congr R.facePerm_apply)

/-- The note's faces and the hypermap's faces are equal in number. -/
theorem fcard_noteFace : fcard R.noteFace Set.univ = R.numFaces := by
  have hs : ConnectSym (frel R.noteFace) := fconnect_sym R.noteFace.injective
  have hs' : ConnectSym (frel R.toHypermap.face) := R.toHypermap.cface_sym
  unfold numFaces
  rw [fcard, fcard, nComp, nComp]
  have himg : comp (frel R.noteFace) '' Set.univ =
      comp (frel R.noteFace) '' (R.rev '' Set.univ) := by
    rw [Set.image_univ_of_surjective fun y => ⟨R.rev y, R.rev_rev y⟩]
  rw [himg, Set.image_image]
  refine ncard_image_eq_of_ker _ _ fun x _ y _ => ?_
  rw [comp_eq_iff hs, comp_eq_iff hs']
  exact (sameCycle_iff_fconnect R.noteFace).symm.trans (R.sameCycle_noteFace_rev x y)

/-! ### The dual and the mirror -/

/-- The dual rotation system: the same darts and reversal, and the rotation `rev ∘ rot`, whose
orbits are the faces of `R`. -/
def dual : RotSystem D where
  rev := R.rev
  rev_rev := R.rev_rev
  rev_ne := R.rev_ne
  rot := R.rot.trans R.revPerm

@[simp] theorem dual_rev (x : D) : R.dual.rev x = R.rev x := rfl
@[simp] theorem dual_rot (x : D) : R.dual.rot x = R.rev (R.rot x) := rfl

/-- The dual hypermap of the library, whose faces are the vertices of the graph. -/
abbrev dualMap : Hypermap D := R.toHypermap.dual

@[simp] theorem dualMap_edge (x : D) : R.dualMap.edge x = R.rev x :=
  Equiv.apply_symm_apply R.rot (R.rev x)
@[simp] theorem dualMap_node (x : D) : R.dualMap.node x = R.rev (R.rot x) := rfl
@[simp] theorem dualMap_face (x : D) : R.dualMap.face x = R.rot.symm x := by
  show R.rot.symm (R.rev (R.rev x)) = R.rot.symm x
  rw [R.rev_rev]

/-- The hypermap of the dual rotation system is the dual of the hypermap. -/
theorem dual_toHypermap : R.dual.toHypermap = R.dualMap := by
  refine Hypermap.ext ?_ ?_ ?_ <;> funext x
  · exact (R.dualMap_edge x).symm
  · rfl
  · rfl

/-- The dual of the dual is the rotation system itself. -/
theorem dual_dual : R.dual.dual = R :=
  RotSystem.ext rfl (Equiv.ext fun x => R.rev_rev (R.rot x))

/-- The vertices of the dual are the faces. -/
theorem dual_tail_eq_iff (x y : D) : R.dual.tail x = R.dual.tail y ↔ R.faceOf x = R.faceOf y := by
  rw [tail_eq_iff, faceOf_eq_iff, dual_toHypermap]
  exact fconnect_inverse (f := R.toHypermap.face) (g := R.dualMap.node)
    R.toHypermap.faceK R.toHypermap.nodeK

/-- The faces of the dual are the vertices. -/
theorem dual_faceOf_eq_iff (x y : D) : R.dual.faceOf x = R.dual.faceOf y ↔ R.tail x = R.tail y := by
  rw [tail_eq_iff, faceOf_eq_iff, dual_toHypermap]
  exact fconnect_inverse (f := R.toHypermap.node) (g := R.dualMap.face)
    R.toHypermap.nodeK R.toHypermap.edgeK

theorem dual_numVertices : R.dual.numVertices = R.numFaces := by
  unfold numVertices numFaces
  rw [dual_toHypermap]
  exact nComp_congr (fun _ _ => fconnect_inverse (f := R.toHypermap.face) (g := R.dualMap.node)
    R.toHypermap.faceK R.toHypermap.nodeK) _

theorem dual_numFaces : R.dual.numFaces = R.numVertices := by
  unfold numVertices numFaces
  rw [dual_toHypermap]
  exact nComp_congr (fun _ _ => fconnect_inverse (f := R.toHypermap.node) (g := R.dualMap.face)
    R.toHypermap.nodeK R.toHypermap.edgeK) _

/-- The mirror image: the same darts and reversal, and the inverse rotation. -/
def mirror : RotSystem D where
  rev := R.rev
  rev_rev := R.rev_rev
  rev_ne := R.rev_ne
  rot := R.rot.symm

/-- The face permutation of the hypermap of the mirror is the face permutation of the note. -/
theorem mirror_facePerm : R.mirror.facePerm = R.noteFace := rfl

/-- The face permutation of the note of the mirror is the face permutation of the hypermap. -/
theorem mirror_noteFace : R.mirror.noteFace = R.facePerm := rfl

theorem mirror_mirror : R.mirror.mirror = R := RotSystem.ext rfl rfl

private theorem gcomp_of_mirror {x y : D} (h : R.mirror.toHypermap.gcomp x y) :
    R.toHypermap.gcomp x y := by
  refine connect_sub (fun a b hab => ?_) h
  rcases hab with hab | hab | hab
  · exact connect_of_rel (Or.inl hab)
  · have hba : R.toHypermap.node b = a := by
      show R.rot b = a
      rw [← (show R.rot.symm a = b from hab), Equiv.apply_symm_apply]
    exact R.toHypermap.glinkC _ _ (connect_of_rel (Or.inr (Or.inl hba)))
  · exact connect_trans (connect_of_rel (R.toHypermap.glinkE a))
      (connect_of_rel (Or.inr (Or.inl hab)))

/-- The mirror has the same connected components. -/
theorem gcomp_mirror (x y : D) : R.mirror.toHypermap.gcomp x y ↔ R.toHypermap.gcomp x y :=
  ⟨R.gcomp_of_mirror, fun h => R.mirror.gcomp_of_mirror (by rwa [mirror_mirror])⟩

theorem mirror_numVertices : R.mirror.numVertices = R.numVertices :=
  nComp_congr (fun _ _ => fconnect_inverse (f := R.rot) (g := R.rot.symm)
    R.rot.symm_apply_apply R.rot.apply_symm_apply) _

theorem mirror_numFaces : R.mirror.numFaces = R.numFaces := R.fcard_noteFace

/-- The mirror has the same genus. -/
theorem genus_mirror : R.mirror.toHypermap.genus = R.toHypermap.genus := by
  have hC : nComp R.mirror.toHypermap.glink Set.univ = nComp R.toHypermap.glink Set.univ :=
    nComp_congr R.gcomp_mirror _
  have hN : fcard R.mirror.toHypermap.node Set.univ = fcard R.toHypermap.node Set.univ :=
    R.mirror_numVertices
  have hF : fcard R.mirror.toHypermap.face Set.univ = fcard R.toHypermap.face Set.univ :=
    R.mirror_numFaces
  have hE : fcard R.mirror.toHypermap.edge Set.univ = fcard R.toHypermap.edge Set.univ := rfl
  unfold Hypermap.genus Hypermap.eulerLhs Hypermap.eulerRhs
  rw [hC, hN, hF, hE]

/-! ### Planarity and Euler's formula -/

/-- Planarity: the hypermap has genus zero. -/
def Planar : Prop := R.toHypermap.Planar

/-- Connectivity: the hypermap has one component (`connected_iff`: walks join all vertices). -/
def Connected : Prop := R.toHypermap.Connected

theorem planar_dual : R.dual.Planar ↔ R.Planar := by
  unfold Planar
  rw [dual_toHypermap]
  exact Hypermap.planar_dual _

theorem planar_mirror : R.mirror.Planar ↔ R.Planar := by
  show R.mirror.toHypermap.genus = 0 ↔ R.toHypermap.genus = 0
  rw [genus_mirror]

/-- The dual hypermap of a planar rotation system is planar. -/
theorem planar_dualMap (hR : R.Planar) : R.dualMap.Planar := (Hypermap.planar_dual _).2 hR

theorem connected_dual : R.dual.Connected ↔ R.Connected := by
  unfold Connected
  rw [dual_toHypermap]
  exact Hypermap.connected_dual _

theorem connected_mirror : R.mirror.Connected ↔ R.Connected := by
  unfold Connected Hypermap.Connected
  rw [nComp_congr R.gcomp_mirror]

/-- The genus formula of a rotation system, with no truncation. -/
theorem genus_formula :
    R.numVertices + R.numFaces + 2 * R.toHypermap.genus = R.numEdges + 2 * R.numComponents := by
  have h := R.toHypermap.evenGenus
  unfold Hypermap.EvenGenus Hypermap.eulerLhs Hypermap.eulerRhs at h
  have hD := R.card_eq
  unfold numEdges at hD
  unfold numVertices numFaces numEdges numComponents
  omega

/-- Euler's formula with components: `V + F = E + 2 k` for a planar rotation system. -/
theorem euler_components (hR : R.Planar) :
    R.numVertices + R.numFaces = R.numEdges + 2 * R.numComponents := by
  have h := R.genus_formula
  rw [show R.toHypermap.genus = 0 from hR] at h
  omega

/-- **Euler's formula.** For a connected planar rotation system, `V + F = E + 2`. -/
theorem euler (hR : R.Planar) (hc : R.Connected) :
    R.numVertices + R.numFaces = R.numEdges + 2 := by
  have h := R.euler_components hR
  rw [show R.numComponents = 1 from hc] at h
  omega

/-- A connected rotation system is planar exactly if Euler's formula holds. -/
theorem planar_iff_euler (hc : R.Connected) :
    R.Planar ↔ R.numVertices + R.numFaces = R.numEdges + 2 := by
  have h := R.genus_formula
  rw [show R.numComponents = 1 from hc] at h
  show R.toHypermap.genus = 0 ↔ _
  omega

/-- **Euler's formula** on the orbit types: the vertices, the faces, and half the darts. -/
theorem euler_card (hR : R.Planar) (hc : R.Connected) :
    Nat.card R.Vertex + Nat.card R.Face = Fintype.card D / 2 + 2 := by
  rw [R.natCard_vertex, R.natCard_face, ← R.numEdges_eq]
  exact R.euler hR hc

/-- Euler's formula for the faces of the note. -/
theorem euler_note (hR : R.Planar) (hc : R.Connected) :
    R.numVertices + fcard R.noteFace Set.univ = R.numEdges + 2 := by
  rw [fcard_noteFace]
  exact R.euler hR hc

/-! ### Walks and connectivity -/

/-- `p` is a walk of darts from the vertex `u` to the vertex `v`. -/
def IsWalk : R.Vertex → List D → R.Vertex → Prop
  | u, [], v => u = v
  | u, x :: p, v => R.tail x = u ∧ IsWalk (R.head x) p v

theorem isWalk_nil (u v : R.Vertex) : R.IsWalk u [] v ↔ u = v := Iff.rfl

theorem isWalk_cons (u v : R.Vertex) (x : D) (p : List D) :
    R.IsWalk u (x :: p) v ↔ R.tail x = u ∧ R.IsWalk (R.head x) p v := Iff.rfl

theorem IsWalk.append {R : RotSystem D} {u v w : R.Vertex} {p q : List D} (hp : R.IsWalk u p v)
    (hq : R.IsWalk v q w) : R.IsWalk u (p ++ q) w := by
  induction p generalizing u with
  | nil =>
    obtain rfl : u = v := hp
    exact hq
  | cons x p ih => exact ⟨hp.1, ih hp.2⟩

/-- Two darts are in one component exactly if a walk joins their tails. -/
theorem gcomp_iff (x y : D) :
    R.toHypermap.gcomp x y ↔ ∃ p, R.IsWalk (R.tail x) p (R.tail y) := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | @tail b z _ hbz ih =>
      obtain ⟨p, hp⟩ := ih
      have hstep : ∃ q, R.IsWalk (R.tail b) q (R.tail z) := by
        rcases hbz with h | h | h
        · exact ⟨[b], rfl, by rw [← h]; rfl⟩
        · refine ⟨[], ?_⟩
          rw [← h]
          exact (R.tail_rot b).symm
        · refine ⟨[b], rfl, ?_⟩
          rw [← h]
          exact (R.tail_rot_symm (R.rev b)).symm
      obtain ⟨q, hq⟩ := hstep
      exact ⟨p ++ q, hp.append hq⟩
  · rintro ⟨p, hp⟩
    have key : ∀ (p : List D) (u v : R.Vertex), R.IsWalk u p v → ∀ a b : D, R.tail a = u →
        R.tail b = v → R.toHypermap.gcomp a b := by
      intro p
      induction p with
      | nil =>
        intro u v huv a b ha hb
        exact R.toHypermap.gcomp_of_cnode
          ((R.tail_eq_iff a b).1 (ha.trans (Eq.trans huv hb.symm)))
      | cons z p ih =>
        intro u v huv a b ha hb
        have h1 : R.toHypermap.gcomp a z :=
          R.toHypermap.gcomp_of_cnode ((R.tail_eq_iff a z).1 (ha.trans huv.1.symm))
        have h2 : R.toHypermap.gcomp z (R.rev z) := connect_of_rel (R.toHypermap.glinkE z)
        exact connect_trans (connect_trans h1 h2) (ih _ v huv.2 (R.rev z) b rfl hb)
    exact key p _ _ hp x y rfl rfl

/-- `R` is connected exactly if it has darts and walks join all vertices. -/
theorem connected_iff :
    R.Connected ↔ Nonempty D ∧ ∀ u v : R.Vertex, ∃ p, R.IsWalk u p v := by
  have hs := R.toHypermap.glinkC
  constructor
  · intro h
    have hpos : 0 < nComp R.toHypermap.glink Set.univ := by
      rw [show nComp R.toHypermap.glink Set.univ = 1 from h]
      exact Nat.one_pos
    obtain ⟨x, -⟩ := nComp_pos.1 hpos
    refine ⟨⟨x⟩, fun u v => ?_⟩
    obtain ⟨a, rfl⟩ := R.exists_tail_eq u
    obtain ⟨b, rfl⟩ := R.exists_tail_eq v
    exact (R.gcomp_iff a b).1 (connect_of_nComp_eq_one hs h (Set.mem_univ a) (Set.mem_univ b))
  · rintro ⟨⟨x0⟩, h⟩
    unfold Connected Hypermap.Connected nComp
    rw [Set.ncard_eq_one]
    refine ⟨comp R.toHypermap.glink x0, Set.ext fun s => ?_⟩
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact (comp_eq_iff hs).2 ((R.gcomp_iff x x0).2 (h _ _))
    · rintro rfl
      exact ⟨x0, rfl⟩

/-! ### The combinatorial map of `SsspFlow.LemmaD` -/

/-- The rotation system of a combinatorial map `(α, φ)` of `SsspFlow.LemmaD` with an involutive
`α` without fixed points: the rotation `α ∘ φ⁻¹` makes `φ` the face permutation of the hypermap. -/
def ofMap (α φ : Equiv.Perm D) (hα : ∀ d, α (α d) = d) (hne : ∀ d, α d ≠ d) : RotSystem D where
  rev := α
  rev_rev := hα
  rev_ne := hne
  rot := φ.symm.trans α

theorem ofMap_revPerm (α φ : Equiv.Perm D) (hα : ∀ d, α (α d) = d) (hne : ∀ d, α d ≠ d) :
    (ofMap α φ hα hne).revPerm = α :=
  Equiv.ext fun _ => rfl

theorem ofMap_facePerm (α φ : Equiv.Perm D) (hα : ∀ d, α (α d) = d) (hne : ∀ d, α d ≠ d) :
    (ofMap α φ hα hne).facePerm = φ := by
  ext x
  show φ (α.symm (α x)) = φ x
  rw [Equiv.symm_apply_apply]

/-- The face function of the hypermap of `ofMap α φ` is `φ`. -/
theorem ofMap_face (α φ : Equiv.Perm D) (hα : ∀ d, α (α d) = d) (hne : ∀ d, α d ≠ d) (x : D) :
    (ofMap α φ hα hne).toHypermap.face x = φ x := by
  rw [← facePerm_apply, ofMap_facePerm]

/-- In the convention of the note, the same map has the mirror rotation `φ ∘ α`. -/
theorem ofMap_mirror_noteFace (α φ : Equiv.Perm D) (hα : ∀ d, α (α d) = d)
    (hne : ∀ d, α d ≠ d) : (ofMap α φ hα hne).mirror.noteFace = φ :=
  ofMap_facePerm α φ hα hne

/-- A rotation system is recovered from its combinatorial map. -/
theorem ofMap_revPerm_facePerm : ofMap R.revPerm R.facePerm R.rev_rev R.rev_ne = R :=
  RotSystem.ext rfl (Equiv.ext fun x => R.rev_rev (R.rot x))

/-- Renaming corners by `rot` (from the first flank to the out-dart) turns the steps of the face
permutation of the hypermap into backward steps of the face permutation of the note. -/
theorem eq_facePerm_iff (a b : D) : b = R.facePerm a ↔ R.rot a = R.noteFace (R.rot b) := by
  constructor
  · rintro rfl
    show R.rot a = R.rot (R.rev (R.rot (R.rot.symm (R.rev a))))
    rw [Equiv.apply_symm_apply, R.rev_rev]
  · intro h
    have h1 : a = R.rev (R.rot b) := R.rot.injective h
    show b = R.rot.symm (R.rev a)
    rw [h1, R.rev_rev, Equiv.symm_apply_apply]

section LemmaD

variable (pick : D → Prop) [DecidablePred pick]

/-- The face-disjoint graph of `SsspFlow.LemmaD` for `φ := facePerm`. Its corners are named by
their first flank, as in the section on corners. `FaceDisjoint.rot_lemmaD` applies to it. -/
def toSetup : FaceDisjoint.Setup R.Face D R.Vertex D :=
  FaceDisjoint.rotSetup R.revPerm R.facePerm R.tail pick

/-- The face-disjoint graph of `SsspFlow.LemmaD` for `φ := noteFace`. Its corners are named by
their out-dart, `d` standing for `τ d`. `FaceDisjoint.rot_lemmaD` applies to it. -/
def noteSetup :
    FaceDisjoint.Setup (Quotient (Equiv.Perm.SameCycle.setoid R.noteFace)) D R.Vertex D :=
  FaceDisjoint.rotSetup R.revPerm R.noteFace R.tail pick

/-- The faces of `toSetup` are the faces of the hypermap. -/
theorem toSetup_fc_eq_iff (x y : D) :
    (R.toSetup pick).fc x = (R.toSetup pick).fc y ↔ R.toHypermap.cface x y :=
  R.faceOf_eq_iff x y

/-- The faces of `noteSetup` are the reverses of the faces of the hypermap. -/
theorem noteSetup_fc_rev_eq_iff (x y : D) :
    (R.noteSetup pick).fc (R.rev x) = (R.noteSetup pick).fc (R.rev y) ↔
      R.toHypermap.cface x y := by
  show Quotient.mk _ (R.rev x) = Quotient.mk _ (R.rev y) ↔ _
  rw [Quotient.eq]
  exact R.sameCycle_noteFace_rev x y

/-- The spokes join a vertex to the darts leaving it. -/
theorem toSetup_spoke (v : R.Vertex) (x : D) : (R.toSetup pick).spoke v x ↔ R.tail x = v := Iff.rfl

/-- The rings of the two graphs agree, up to the renaming of corners by `rot`. -/
theorem toSetup_rg_iff (pick' : D → Prop) [DecidablePred pick'] (a b : D) :
    (R.toSetup pick).rg a b ↔ (R.noteSetup pick').rg (R.rot a) (R.rot b) :=
  (or_congr (R.eq_facePerm_iff a b) (R.eq_facePerm_iff b a)).trans or_comm

/-- The spokes of the two graphs agree, up to the renaming of corners by `rot`. -/
theorem toSetup_spoke_iff (pick' : D → Prop) [DecidablePred pick'] (v : R.Vertex) (a : D) :
    (R.toSetup pick).spoke v a ↔ (R.noteSetup pick').spoke v (R.rot a) := by
  show R.tail a = v ↔ R.tail (R.rot a) = v
  rw [R.tail_rot]

/-- The two arcs of an edge join the same corners (`FaceDisjoint.rot_pair`). -/
theorem toSetup_pair (hpick : ∀ d, pick (R.rev d) ↔ ¬ pick d) (d : D) (hd : pick d) :
    (R.toSetup pick).src (R.rev d) = (R.toSetup pick).dst d ∧
      (R.toSetup pick).dst (R.rev d) = (R.toSetup pick).src d :=
  FaceDisjoint.rot_pair R.revPerm R.facePerm R.tail pick R.rev_rev hpick d hd

/-- For the same picked darts, the arcs of the two graphs agree too, up to the renaming of corners
by `rot`, with their directions reversed. -/
theorem toSetup_arc (pick' : D → Prop) [DecidablePred pick'] (h : ∀ d, pick d ↔ pick' d) (d : D) :
    R.rot ((R.toSetup pick).src d) = (R.noteSetup pick').dst d ∧
      R.rot ((R.toSetup pick).dst d) = (R.noteSetup pick').src d := by
  by_cases hd : pick d
  · have hd' := (h d).1 hd
    simp [toSetup, noteSetup, FaceDisjoint.rotSetup, hd, hd', R.rev_rev]
  · have hd' : ¬ pick' d := fun h' => hd ((h d).2 h')
    simp [toSetup, noteSetup, FaceDisjoint.rotSetup, hd, hd', R.rev_rev]

end LemmaD

/-! ### Simple cycles of the graph -/

/-- `y` can follow `x` in a walk: the head of `x` is the tail of `y`. -/
def link (x y : D) : Prop := R.head x = R.tail y

/-- `c` is a closed walk of darts whose tail vertices are pairwise distinct. This admits two
degenerate walks, the empty list and `[d, rev d]`, which `IsCycle` excludes. -/
def IsRing (c : List D) : Prop := cycle R.link c ∧ (c.map R.tail).Nodup

/-- `c` is a simple cycle of the graph: a nonempty closed walk of darts with pairwise distinct
tail vertices that does not run through an edge in both directions. -/
structure IsCycle (c : List D) : Prop where
  /-- The closed walk with pairwise distinct tail vertices. -/
  ring : R.IsRing c
  /-- The cycle has a dart. -/
  ne_nil : c ≠ []
  /-- No edge is used in both directions. -/
  rev_not_mem : ∀ d ∈ c, R.rev d ∉ c

/-- The vertex `v` lies on the cycle `c`: it is the tail of a dart of `c`. -/
def OnCycle (c : List D) (v : R.Vertex) : Prop := ∃ d ∈ c, R.tail d = v

variable {R} in
/-- The head of a dart of a closed walk lies on the walk. -/
theorem onCycle_head {c : List D} (hc : cycle R.link c) {d : D} (hd : d ∈ c) :
    R.OnCycle c (R.head d) := by
  obtain ⟨y, hy, hdy⟩ := cycle.exists_succ hc hd
  exact ⟨y, hy, hdy.symm⟩

/-- The faces of the dual hypermap are the vertices of the graph. -/
theorem dualMap_cface_iff (x y : D) : R.dualMap.cface x y ↔ R.tail x = R.tail y := by
  rw [tail_eq_iff]
  exact (fconnect_congr R.dualMap_face).trans
    (fconnect_inverse R.rot.symm_apply_apply R.rot.apply_symm_apply)

/-- The links of the graph are the R-links of the dual hypermap. -/
theorem link_iff_rlink (x y : D) : R.link x y ↔ R.dualMap.rlink x y := by
  show R.tail (R.rev x) = R.tail y ↔ R.dualMap.cface (R.dualMap.edge x) y
  rw [dualMap_edge, dualMap_cface_iff]

/-- The face band of the cycle in the dual hypermap: the darts whose tail is on the cycle. -/
theorem mem_fband_iff (c : List D) (x : D) :
    x ∈ R.dualMap.fband c ↔ R.OnCycle c (R.tail x) := by
  simp only [Hypermap.mem_fband, dualMap_cface_iff, OnCycle]
  exact exists_congr fun y => and_congr_right fun _ => eq_comm

private theorem cycle_congr {α : Type*} {e e' : α → α → Prop} (h : ∀ a b, e a b ↔ e' a b)
    (p : List α) : cycle e p ↔ cycle e' p := by
  cases p with
  | nil => exact Iff.rfl
  | cons x p => rw [cycle_cons, cycle_cons]; exact path_congr h

private theorem nodup_map_congr {α β γ : Type*} {f : α → β} {g : α → γ}
    (h : ∀ x y, f x = f y ↔ g x = g y) (l : List α) : (l.map f).Nodup ↔ (l.map g).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map, List.pairwise_map]
  exact ⟨fun hp => hp.imp fun hne heq => hne ((h _ _).2 heq),
    fun hp => hp.imp fun hne heq => hne ((h _ _).1 heq)⟩

/-- A closed walk with distinct tail vertices is a ring of the dual hypermap, a simple R-cycle. -/
theorem isRing_iff (c : List D) : R.IsRing c ↔ R.dualMap.SCycle R.dualMap.rlink c := by
  unfold IsRing Hypermap.SCycle Hypermap.Simple
  refine and_congr (cycle_congr R.link_iff_rlink c) ?_
  refine nodup_map_congr (fun x y => ?_) c
  exact (R.dualMap_cface_iff x y).symm.trans R.dualMap.froot_face_eq_iff.symm

/-! ### The two sides of a cycle -/

/-- The darts strictly on one side: the strict disk `diskE` of the dual hypermap. -/
def inside (c : List D) : Set D := R.dualMap.diskE c

/-- The darts on the other side: the complement of the disk `diskN` of the dual hypermap. It
holds the reverses of the darts of a simple cycle, and every component without the cycle. -/
def outside (c : List D) : Set D := (R.dualMap.diskN c)ᶜ

variable {c : List D}

theorem not_mem_of_mem_inside {x : D} (hx : x ∈ R.inside c) : x ∉ c := hx.2

theorem not_mem_of_mem_outside {x : D} (hx : x ∈ R.outside c) : x ∉ c :=
  fun h => hx (R.dualMap.mem_diskN_of_mem c h)

/-- The disk is the cycle and the inside. -/
theorem mem_diskN_iff (x : D) : x ∈ R.dualMap.diskN c ↔ x ∈ c ∨ x ∈ R.inside c :=
  R.dualMap.diskN_E c x

/-- **(a)** A dart not on the cycle lies on exactly one side. -/
theorem exactly_one_side {x : D} (hx : x ∉ c) :
    (x ∈ R.inside c ∧ x ∉ R.outside c) ∨ (x ∈ R.outside c ∧ x ∉ R.inside c) := by
  by_cases h : x ∈ R.dualMap.diskN c
  · exact Or.inl ⟨⟨h, hx⟩, fun h' => h' h⟩
  · exact Or.inr ⟨h, fun h' => h h'.1⟩

/-- The inside is closed under `rev`: both darts of an edge are inside, or neither. -/
theorem rev_mem_inside_iff (hR : R.Planar) (hc : R.IsRing c) (x : D) :
    R.rev x ∈ R.inside c ↔ x ∈ R.inside c :=
  ((R.dualMap.diskE_edge (R.planar_dualMap hR) ((R.isRing_iff c).1 hc)) x (R.rev x)
    (R.dualMap_edge x)).symm

theorem rev_mem_inside (hR : R.Planar) (hc : R.IsRing c) {x : D} (hx : x ∈ R.inside c) :
    R.rev x ∈ R.inside c :=
  (R.rev_mem_inside_iff hR hc x).2 hx

/-- The outside is closed under `rev`, away from the darts of the cycle. -/
theorem rev_mem_outside (hR : R.Planar) (hc : R.IsRing c) {x : D} (hx : x ∈ R.outside c)
    (hrx : R.rev x ∉ c) : R.rev x ∈ R.outside c := by
  intro h
  rcases (R.mem_diskN_iff (R.rev x)).1 h with h | h
  · exact hrx h
  · exact hx ((R.rev_mem_inside_iff hR hc x).1 h).1

/-- **(a)** for edges: an edge with no dart on the cycle lies on exactly one side. -/
theorem edge_exactly_one_side (hR : R.Planar) (hc : R.IsRing c) {x : D} (hx : x ∉ c)
    (hrx : R.rev x ∉ c) :
    (x ∈ R.inside c ∧ R.rev x ∈ R.inside c) ∨ (x ∈ R.outside c ∧ R.rev x ∈ R.outside c) := by
  rcases R.exactly_one_side hx with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl ⟨h, R.rev_mem_inside hR hc h⟩
  · exact Or.inr ⟨h, R.rev_mem_outside hR hc h hrx⟩

/-- Which side is the inside: the dart before `rev d` around the head of a dart `d` of the cycle
is inside, unless it is on the cycle. -/
theorem rot_symm_rev_mem_inside {d : D} (hd : d ∈ c) (h : R.rot.symm (R.rev d) ∉ c) :
    R.rot.symm (R.rev d) ∈ R.inside c := by
  refine ⟨⟨d, hd, ?_⟩, h⟩
  show connect _ (R.dualMap.face (R.dualMap.edge d)) _
  rw [dualMap_edge, dualMap_face]

/-- The reverse of a dart of the cycle is outside, unless it is on the cycle too. -/
theorem rev_cycle_mem_outside (hR : R.Planar) (hc : R.IsRing c) {d : D} (hd : d ∈ c)
    (hrd : R.rev d ∉ c) : R.rev d ∈ R.outside c := by
  intro h
  exact ((R.rev_mem_inside_iff hR hc d).1 ⟨h, hrd⟩).2 hd

/-- At a vertex not on the cycle, every dart is inside if one is. -/
theorem mem_inside_of_tail_eq {x y : D} (hx : x ∈ R.inside c) (hv : ¬ R.OnCycle c (R.tail x))
    (hy : R.tail y = R.tail x) : y ∈ R.inside c := by
  have hF : x ∈ R.dualMap.diskF c := ⟨hx.1, fun h => hv ((R.mem_fband_iff c x).1 h)⟩
  have hyF : y ∈ R.dualMap.diskF c :=
    ((R.dualMap.diskF_face c).connect_iff ((R.dualMap_cface_iff x y).2 hy.symm)).1 hF
  exact ⟨hyF.1, fun h => hyF.2 (R.dualMap.ring_fband c y h)⟩

/-- At a vertex not on the cycle, every dart is outside if one is. -/
theorem mem_outside_of_tail_eq {x y : D} (hx : x ∈ R.outside c) (hv : ¬ R.OnCycle c (R.tail x))
    (hy : R.tail y = R.tail x) : y ∈ R.outside c := by
  have hF : x ∈ R.dualMap.diskFC c := ⟨hx, fun h => hv ((R.mem_fband_iff c x).1 h)⟩
  have hyF : y ∈ R.dualMap.diskFC c :=
    ((R.dualMap.diskFC_face c).connect_iff ((R.dualMap_cface_iff x y).2 hy.symm)).1 hF
  exact hyF.1

/-- **(b)** A walk of darts that starts inside and visits no vertex of the cycle stays inside. -/
theorem walk_mem_inside (hR : R.Planar) (hc : R.IsRing c) {x : D} {p : List D}
    (hw : path R.link x p) (hv : ∀ y ∈ p, ¬ R.OnCycle c (R.tail y)) (hx : x ∈ R.inside c) :
    last x p ∈ R.inside c := by
  induction p generalizing x with
  | nil => exact hx
  | cons y p ih =>
    have hxy : R.tail (R.rev x) = R.tail y := hw.1
    have hy : y ∈ R.inside c := by
      refine R.mem_inside_of_tail_eq (R.rev_mem_inside hR hc hx) ?_ hxy.symm
      rw [hxy]
      exact hv y List.mem_cons_self
    exact ih hw.2 (fun z hz => hv z (List.mem_cons_of_mem _ hz)) hy

/-- **(b)** A walk of darts that starts outside and visits no vertex of the cycle stays
outside. -/
theorem walk_mem_outside (hR : R.Planar) (hc : R.IsRing c) {x : D} {p : List D}
    (hw : path R.link x p) (hv : ∀ y ∈ p, ¬ R.OnCycle c (R.tail y)) (hx : x ∈ R.outside c) :
    last x p ∈ R.outside c := by
  induction p generalizing x with
  | nil => exact hx
  | cons y p ih =>
    have hxy : R.tail (R.rev x) = R.tail y := hw.1
    have hvy := hv y List.mem_cons_self
    have hrx : R.rev x ∉ c := fun h => hvy ⟨R.rev x, h, hxy⟩
    have hy : y ∈ R.outside c := by
      refine R.mem_outside_of_tail_eq (R.rev_mem_outside hR hc hx hrx) ?_ hxy.symm
      rw [hxy]
      exact hvy
    exact ih hw.2 (fun z hz => hv z (List.mem_cons_of_mem _ hz)) hy

/-- **(b)** for darts: a walk from a dart inside to a dart outside visits a vertex of the cycle
after its first dart. -/
theorem walk_meets_cycle (hR : R.Planar) (hc : R.IsRing c) {x : D} {p : List D}
    (hw : path R.link x p) (hx : x ∈ R.inside c) (hl : last x p ∈ R.outside c) :
    ∃ y ∈ p, R.OnCycle c (R.tail y) := by
  by_contra h
  push Not at h
  exact hl (R.walk_mem_inside hR hc hw h hx).1

/-- **(b)** for darts: a walk from a dart outside to a dart inside visits a vertex of the cycle
after its first dart. -/
theorem walk_meets_cycle' (hR : R.Planar) (hc : R.IsRing c) {x : D} {p : List D}
    (hw : path R.link x p) (hx : x ∈ R.outside c) (hl : last x p ∈ R.inside c) :
    ∃ y ∈ p, R.OnCycle c (R.tail y) := by
  by_contra h
  push Not at h
  exact (R.walk_mem_outside hR hc hw h hx) hl.1

/-! ### The sides of a vertex -/

/-- The vertex `v` is off the cycle and has a dart inside, hence all its darts inside. -/
def InsideVertex (c : List D) (v : R.Vertex) : Prop :=
  ¬ R.OnCycle c v ∧ ∃ x, R.tail x = v ∧ x ∈ R.inside c

/-- The vertex `v` is off the cycle and has a dart outside, hence all its darts outside. -/
def OutsideVertex (c : List D) (v : R.Vertex) : Prop :=
  ¬ R.OnCycle c v ∧ ∃ x, R.tail x = v ∧ x ∈ R.outside c

variable {R} in
theorem InsideVertex.mem {v : R.Vertex} (h : R.InsideVertex c v) {x : D} (hx : R.tail x = v) :
    x ∈ R.inside c := by
  obtain ⟨hv, y, rfl, hy⟩ := h
  exact R.mem_inside_of_tail_eq hy hv hx

variable {R} in
theorem OutsideVertex.mem {v : R.Vertex} (h : R.OutsideVertex c v) {x : D} (hx : R.tail x = v) :
    x ∈ R.outside c := by
  obtain ⟨hv, y, rfl, hy⟩ := h
  exact R.mem_outside_of_tail_eq hy hv hx

/-- **(a)** for vertices: a vertex off the cycle lies on exactly one side. -/
theorem vertex_exactly_one_side {v : R.Vertex} (hv : ¬ R.OnCycle c v) :
    (R.InsideVertex c v ∧ ¬ R.OutsideVertex c v) ∨
      (R.OutsideVertex c v ∧ ¬ R.InsideVertex c v) := by
  obtain ⟨x, rfl⟩ := R.exists_tail_eq v
  have hxc : x ∉ c := fun h => hv ⟨x, h, rfl⟩
  rcases R.exactly_one_side hxc with ⟨h, -⟩ | ⟨h, -⟩
  · have hi : R.InsideVertex c (R.tail x) := ⟨hv, x, rfl, h⟩
    exact Or.inl ⟨hi, fun ho => ho.mem rfl h.1⟩
  · have ho : R.OutsideVertex c (R.tail x) := ⟨hv, x, rfl, h⟩
    exact Or.inr ⟨ho, fun hi => h (hi.mem rfl).1⟩

/-- A walk from `tail x` that starts with `x` is a path of links with the right last head. -/
theorem isWalk_tail_iff (x : D) (p : List D) (v : R.Vertex) :
    R.IsWalk (R.tail x) (x :: p) v ↔ path R.link x p ∧ R.head (last x p) = v := by
  induction p generalizing x with
  | nil => exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨rfl, h.2⟩⟩
  | cons y p ih =>
    constructor
    · rintro ⟨-, hxy, hw⟩
      have h := (ih y).1 ⟨rfl, hw⟩
      exact ⟨⟨hxy.symm, h.1⟩, h.2⟩
    · rintro ⟨⟨hxy, hp⟩, hl⟩
      have h := (ih y).2 ⟨hp, hl⟩
      exact ⟨rfl, hxy.symm, h.2⟩

/-- **(b)** A walk of darts from a vertex inside to a vertex outside passes through a vertex of
the cycle. -/
theorem isWalk_meets_cycle (hR : R.Planar) (hc : R.IsRing c) {u v : R.Vertex} {p : List D}
    (hw : R.IsWalk u p v) (hu : R.InsideVertex c u) (hv : R.OutsideVertex c v) :
    ∃ y ∈ p, R.OnCycle c (R.tail y) := by
  cases p with
  | nil =>
    obtain rfl : u = v := hw
    rcases R.vertex_exactly_one_side hu.1 with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd hv h
    · exact absurd hu h
  | cons x q =>
    obtain rfl : R.tail x = u := hw.1
    obtain ⟨hp, hl⟩ := (R.isWalk_tail_iff x q v).1 hw
    have hz : R.rev (last x q) ∈ R.outside c := hv.mem hl
    have hzc : last x q ∉ c := fun h => hv.1 (hl ▸ onCycle_head hc.1 h)
    have hz' : last x q ∈ R.outside c := by
      have h := R.rev_mem_outside hR hc hz (by rwa [R.rev_rev])
      rwa [R.rev_rev] at h
    obtain ⟨y, hy, hyc⟩ := R.walk_meets_cycle hR hc hp (hu.mem rfl) hz'
    exact ⟨y, List.mem_cons_of_mem _ hy, hyc⟩

/-- **(b)** A walk of darts from a vertex outside to a vertex inside passes through a vertex of
the cycle. -/
theorem isWalk_meets_cycle' (hR : R.Planar) (hc : R.IsRing c) {u v : R.Vertex} {p : List D}
    (hw : R.IsWalk u p v) (hu : R.OutsideVertex c u) (hv : R.InsideVertex c v) :
    ∃ y ∈ p, R.OnCycle c (R.tail y) := by
  cases p with
  | nil =>
    obtain rfl : u = v := hw
    rcases R.vertex_exactly_one_side hu.1 with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd hu h
    · exact absurd hv h
  | cons x q =>
    obtain rfl : R.tail x = u := hw.1
    obtain ⟨hp, hl⟩ := (R.isWalk_tail_iff x q v).1 hw
    have hz' : last x q ∈ R.inside c :=
      (R.rev_mem_inside_iff hR hc _).1 (hv.mem hl)
    obtain ⟨y, hy, hyc⟩ := R.walk_meets_cycle' hR hc hp (hu.mem rfl) hz'
    exact ⟨y, List.mem_cons_of_mem _ hy, hyc⟩

/-! ### The two planar maps of the cut -/

/-- The planar map of the inside: the disk map of the cut of the dual along the cycle; its darts
are the cycle and the inside (`mem_diskN_iff`). -/
noncomputable def insideMap (hR : R.Planar) (hc : R.IsRing c) :
    Hypermap (R.dualMap.SnipdDart c) :=
  R.dualMap.snipDisk (R.planar_dualMap hR) ((R.isRing_iff c).1 hc)

/-- The planar map of the outside: the remainder map of the cut of the dual along the cycle; its
darts are the cycle and the outside. -/
noncomputable def outsideMap (hR : R.Planar) (hc : R.IsRing c) :
    Hypermap (R.dualMap.SniprDart c) :=
  R.dualMap.snipRem (R.planar_dualMap hR) ((R.isRing_iff c).1 hc)

theorem insideMap_planar (hR : R.Planar) (hc : R.IsRing c) : (R.insideMap hR hc).Planar :=
  R.dualMap.planar_snipd _ _

theorem outsideMap_planar (hR : R.Planar) (hc : R.IsRing c) : (R.outsideMap hR hc).Planar :=
  R.dualMap.planar_snipr _ _

/-- The dual hypermap is the patch of the two maps of the cut (`Hypermap.snip_patch`). -/
theorem patch_inside_outside (hR : R.Planar) (hc : R.IsRing c) :
    R.dualMap.Patch (R.insideMap hR hc) (R.outsideMap hR hc) (R.dualMap.snipd c)
      (R.dualMap.snipr c) (R.dualMap.snipdRing c) (R.dualMap.sniprRing c) :=
  R.dualMap.snip_patch _ _

/-- The darts of the outside map are the cycle and the outside. -/
theorem mem_outsideMap_iff (x : D) : x ∉ R.dualMap.diskE c ↔ x ∈ c ∨ x ∈ R.outside c := by
  constructor
  · intro h
    by_cases hx : x ∈ c
    · exact Or.inl hx
    · exact Or.inr fun hd => h ⟨hd, hx⟩
  · rintro (h | h) he
    · exact he.2 h
    · exact h he.1

/-! ### Reversing the cycle swaps the sides -/

/-- The sides are closed under a step of the rotation away from the cycle. -/
theorem rot_mem_outside {x : D} (hx : x ∈ R.outside c) (h : R.rot x ∉ c) :
    R.rot x ∈ R.outside c := by
  intro hm
  have hd := R.dualMap.diskN_dlink c hm ⟨h, Or.inr (R.dualMap_face (R.rot x))⟩
  rw [Equiv.symm_apply_apply] at hd
  exact hx hd

/-- The disk is closed under `rot`, except that it stops before the reverse of a cycle dart. -/
theorem rot_mem_diskN (hR : R.Planar) (hc : R.IsRing c) {x : D} (hx : x ∈ R.dualMap.diskN c)
    (h : R.rev (R.rot x) ∉ c) : R.rot x ∈ R.dualMap.diskN c := by
  have h1 : R.rev (R.rot x) ∈ R.dualMap.diskN c := ((R.dualMap.diskN_node c) x _ rfl).1 hx
  exact ((R.rev_mem_inside_iff hR hc (R.rot x)).1 ⟨h1, h⟩).1

/-- The disk is closed under the face permutation of the hypermap. -/
theorem face_mem_diskN_iff (x : D) :
    R.rot.symm (R.rev x) ∈ R.dualMap.diskN c ↔ x ∈ R.dualMap.diskN c :=
  (R.dualMap.diskN_node c) (R.rot.symm (R.rev x)) x (by
    show R.rev (R.rot (R.rot.symm (R.rev x))) = x
    rw [Equiv.apply_symm_apply, R.rev_rev])

private theorem cycle_exists_pred {α : Type*} {e : α → α → Prop} {c : List α} (hc : cycle e c)
    {x : α} (hx : x ∈ c) : ∃ y ∈ c, e y x := by
  have key : ∀ (q : List α) (a : α), path e a q → x ∈ q → ∃ y ∈ belast a q, e y x := by
    intro q
    induction q with
    | nil => intro _ _ h; simp at h
    | cons b q ih =>
      intro a h hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact ⟨a, by simp, h.1⟩
      · obtain ⟨y, hy, hxy⟩ := ih b h.2 hm
        exact ⟨y, by simp [hy], hxy⟩
  cases c with
  | nil => simp at hx
  | cons a p =>
    have hm : x ∈ p ++ [a] := by
      rcases List.mem_cons.1 hx with rfl | h
      · simp
      · simp [h]
    obtain ⟨y, hy, hxy⟩ := key _ a hc hm
    rw [belast_concat] at hy
    exact ⟨y, hy, hxy⟩

/-- The dart before a dart of a simple cycle in the rotation is outside: going forward in the
rotation from the reverse of the dart that enters the vertex, the darts stay outside until the
dart that leaves it. -/
theorem rot_symm_mem_outside (hR : R.Planar) (hc : R.IsCycle c) {d : D} (hd : d ∈ c) :
    R.rot.symm d ∈ R.outside c := by
  obtain ⟨e, he, hl⟩ := cycle_exists_pred hc.ring.1 hd
  have hre : R.rev e ∈ R.outside c :=
    R.rev_cycle_mem_outside hR hc.ring he (hc.rev_not_mem e he)
  have htl : R.tail (R.rev e) = R.tail d := hl
  obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 ((R.tail_eq_iff _ _).1 htl)
  have key : ∀ (n : ℕ) (x : D), x ∈ R.outside c → R.tail x = R.tail d → (⇑R.rot)^[n] x = d →
      R.rot.symm d ∈ R.outside c := by
    intro n
    induction n with
    | zero =>
      intro x hx _ h
      have hxd : x = d := h
      exact absurd (hxd ▸ hd) (R.not_mem_of_mem_outside hx)
    | succ n ih =>
      intro x hx ht h
      rw [Function.iterate_succ_apply] at h
      by_cases hrd : R.rot x = d
      · rw [← hrd, Equiv.symm_apply_apply]
        exact hx
      · have ht' : R.tail (R.rot x) = R.tail d := (R.tail_rot x).trans ht
        have hnc : R.rot x ∉ c := fun hm =>
          hrd (List.inj_on_of_nodup_map hc.ring.2 hm hd ht')
        exact ih (R.rot x) (R.rot_mem_outside hx hnc) ht' h
  exact key n _ hre htl hn

/-- The cycle run backwards: the reverses of its darts, in the opposite order. -/
def reverseCycle (c : List D) : List D := (c.map R.rev).reverse

theorem mem_reverseCycle {x : D} : x ∈ R.reverseCycle c ↔ R.rev x ∈ c := by
  simp only [reverseCycle, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rwa [R.rev_rev]
  · intro h
    exact ⟨_, h, R.rev_rev x⟩

theorem reverseCycle_reverseCycle (c : List D) : R.reverseCycle (R.reverseCycle c) = c := by
  simp only [reverseCycle, List.map_reverse, List.reverse_reverse, List.map_map]
  have h : R.rev ∘ R.rev = id := funext R.rev_rev
  rw [h, List.map_id]

theorem link_rev_iff (x y : D) : R.link (R.rev y) (R.rev x) ↔ R.link x y := by
  show R.tail (R.rev (R.rev y)) = R.tail (R.rev x) ↔ R.tail (R.rev x) = R.tail y
  rw [R.rev_rev]
  exact eq_comm

private theorem cycle_reverseCycle (hc : cycle R.link c) : cycle R.link (R.reverseCycle c) := by
  cases c with
  | nil => trivial
  | cons x p =>
    have h1 : path (fun a b => R.link (R.rev a) (R.rev b)) x (x :: p).reverse := by
      have h := (path_reverse (e := fun a b => R.link (R.rev a) (R.rev b)) (x := x)
        (p := p ++ [x])).2 (path.mono (fun a b hab => (R.link_rev_iff a b).2 hab) hc)
      rwa [last_concat, belast_concat] at h
    have h2 : path R.link (R.rev x) ((x :: p).reverse.map R.rev) := path_map.2 h1
    have h3 : (x :: p).reverse.map R.rev = p.reverse.map R.rev ++ [R.rev x] := by simp
    have h4 : R.reverseCycle (x :: p) = p.reverse.map R.rev ++ [R.rev x] := by
      simp [reverseCycle]
    rw [h4, cycle_rotate_one, cycle_cons, ← h3]
    exact h2

private theorem map_head_belast {a : D} {q : List D} (h : path R.link a q) :
    (belast a q).map R.head = q.map R.tail := by
  induction q generalizing a with
  | nil => rfl
  | cons b q ih =>
    simp only [belast_cons, List.map_cons, ih h.2]
    rw [show R.head a = R.tail b from h.1]

private theorem nodup_map_head (hc : R.IsRing c) : (c.map R.head).Nodup := by
  cases c with
  | nil => exact List.nodup_nil
  | cons x p =>
    have h := R.map_head_belast (a := x) (q := p ++ [x]) hc.1
    rw [belast_concat] at h
    rw [h]
    exact ((List.perm_append_singleton x p).map R.tail).nodup_iff.2 hc.2

/-- The reversal of a closed walk with distinct tail vertices is another one. -/
theorem isRing_reverseCycle (hc : R.IsRing c) : R.IsRing (R.reverseCycle c) := by
  refine ⟨R.cycle_reverseCycle hc.1, ?_⟩
  have h : (R.reverseCycle c).map R.tail = (c.map R.head).reverse := by
    simp only [reverseCycle, List.map_reverse, List.map_map]
    rfl
  rw [h, List.nodup_reverse]
  exact R.nodup_map_head hc

/-- The reversal of a simple cycle is a simple cycle. -/
theorem isCycle_reverseCycle (hc : R.IsCycle c) : R.IsCycle (R.reverseCycle c) where
  ring := R.isRing_reverseCycle hc.ring
  ne_nil := by simpa [reverseCycle] using hc.ne_nil
  rev_not_mem := by
    intro d hd hrd
    exact hc.rev_not_mem _ (R.mem_reverseCycle.1 hd) (R.mem_reverseCycle.1 hrd)

/-- The disk of the reversed cycle is outside. -/
theorem diskN_reverseCycle_subset (hR : R.Planar) (hc : R.IsCycle c) {x : D}
    (hx : x ∈ R.dualMap.diskN (R.reverseCycle c)) : x ∈ R.outside c := by
  obtain ⟨y, hy, hxy⟩ := hx
  have hstart : R.dualMap.face (R.dualMap.edge y) ∈ R.outside c := by
    rw [dualMap_edge, dualMap_face]
    exact R.rot_symm_mem_outside hR hc (R.mem_reverseCycle.1 hy)
  refine mem_of_connect_of_forward (a := R.outside c) ?_ hxy hstart
  rintro a b ⟨ha, hab⟩ hao hb
  rcases hab with hab | hab
  · exact hao (((R.dualMap.diskN_node c) b a hab.symm).1 hb)
  · have hb' : R.rot.symm a = b := by rw [← R.dualMap_face a]; exact hab
    have h := R.rot_mem_diskN hR hc.ring hb (by
      rw [← hb', Equiv.apply_symm_apply]
      exact fun hm => ha (R.mem_reverseCycle.2 hm))
    rw [← hb', Equiv.apply_symm_apply] at h
    exact hao h

private theorem closure_step (hR : R.Planar) (hc : R.IsRing c) {a b : D}
    (hab : R.toHypermap.glink a b) (ha : a ∈ R.dualMap.diskN c) :
    b ∈ R.dualMap.diskN c ∨ b ∈ R.dualMap.diskN (R.reverseCycle c) := by
  rcases hab with hab | hab | hab
  · have hb : R.rev a = b := hab
    subst hb
    by_cases hac : a ∈ c
    · refine Or.inr (R.dualMap.mem_diskN_of_mem _ (R.mem_reverseCycle.2 ?_))
      rwa [R.rev_rev]
    · exact Or.inl ((R.rev_mem_inside hR hc ⟨ha, hac⟩).1)
  · have hb : R.rot a = b := hab
    subst hb
    by_cases h : R.rev (R.rot a) ∈ c
    · exact Or.inr (R.dualMap.mem_diskN_of_mem _ (R.mem_reverseCycle.2 h))
    · exact Or.inl (R.rot_mem_diskN hR hc ha h)
  · have hb : R.rot.symm (R.rev a) = b := hab
    subst hb
    exact Or.inl ((R.face_mem_diskN_iff _).2 ha)

/-- In a connected planar rotation system, every dart is on the disk of a simple cycle or on the
disk of its reversal. -/
theorem mem_diskN_or_reverseCycle (hR : R.Planar) (hconn : R.Connected) (hc : R.IsCycle c)
    (x : D) : x ∈ R.dualMap.diskN c ∨ x ∈ R.dualMap.diskN (R.reverseCycle c) := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil c hc.ne_nil
  have hconnect : R.toHypermap.gcomp d x :=
    connect_of_nComp_eq_one R.toHypermap.glinkC hconn (Set.mem_univ d) (Set.mem_univ x)
  refine mem_of_connect_of_forward
    (a := {z | z ∈ R.dualMap.diskN c ∨ z ∈ R.dualMap.diskN (R.reverseCycle c)}) ?_ hconnect
    (Or.inl (R.dualMap.mem_diskN_of_mem c hd))
  rintro a b hab (ha | ha)
  · exact R.closure_step hR hc.ring hab ha
  · have h := R.closure_step hR (R.isRing_reverseCycle hc.ring) hab ha
    rw [R.reverseCycle_reverseCycle] at h
    exact h.symm

/-- **The sides swap, one half.** In a connected planar rotation system, the outside of the
reversal of a simple cycle is the cycle and its inside. -/
theorem mem_outside_reverseCycle_iff (hR : R.Planar) (hconn : R.Connected) (hc : R.IsCycle c)
    (x : D) : x ∈ R.outside (R.reverseCycle c) ↔ x ∈ c ∨ x ∈ R.inside c := by
  rw [← mem_diskN_iff]
  constructor
  · intro h
    exact (R.mem_diskN_or_reverseCycle hR hconn hc x).resolve_right h
  · intro h
    refine R.diskN_reverseCycle_subset hR (R.isCycle_reverseCycle hc) ?_
    rwa [R.reverseCycle_reverseCycle]

/-- **The sides swap, other half.** In a connected planar rotation system, the inside of the
reversal of a simple cycle is the outside without the reverses of the cycle darts. -/
theorem mem_inside_reverseCycle_iff (hR : R.Planar) (hconn : R.Connected) (hc : R.IsCycle c)
    (x : D) : x ∈ R.inside (R.reverseCycle c) ↔ x ∈ R.outside c ∧ R.rev x ∉ c := by
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨R.diskN_reverseCycle_subset hR hc h, fun hm => hx (R.mem_reverseCycle.2 hm)⟩
  · rintro ⟨h, hx⟩
    exact ⟨(R.mem_diskN_or_reverseCycle hR hconn hc x).resolve_left h,
      fun hm => hx (R.mem_reverseCycle.1 hm)⟩

/-! ### An instance -/

section Instance

theorem fconnect_iff_label {α β : Type*} (f : α → α) (label : α → β)
    (hinv : ∀ x, label (f x) = label x) (hconn : ∀ x y, label x = label y → ∃ n, f^[n] x = y)
    (x y : α) : fconnect f x y ↔ label x = label y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih => rw [ih, ← hbc, hinv]
  · intro h
    exact fconnect_iff_iterate.2 (hconn x y h)

theorem fcard_eq_card_image {α β : Type*} [Fintype α] [DecidableEq β] {f : α → α}
    (hs : ConnectSym (frel f)) (label : α → β) (h : ∀ x y, fconnect f x y ↔ label x = label y) :
    fcard f Set.univ = (Finset.univ.image label).card := by
  have hk : ∀ x ∈ (Set.univ : Set α), ∀ y ∈ (Set.univ : Set α),
      comp (frel f) x = comp (frel f) y ↔ label x = label y :=
    fun x _ y _ => (comp_eq_iff hs).trans (h x y)
  rw [fcard, nComp, ncard_image_eq_of_ker _ label hk, ← Set.ncard_coe_finset]
  simp

/-- A triangle `a, b, c` with a pendant edge at `a` on each side. The darts `0, 2, 4` run around
the triangle and `1, 3, 5` are their reverses; `6` runs from `a` to the pendant vertex `p`, and
`8` from `a` to the pendant vertex `q`. The rotation at `a` is `0, 6, 5, 8`. -/
def triangle : RotSystem (Fin 10) where
  rev := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8]
  rev_rev := by decide
  rev_ne := by decide
  rot :=
    { toFun := ![6, 2, 1, 4, 3, 8, 5, 7, 0, 9]
      invFun := ![8, 2, 1, 4, 3, 6, 0, 7, 5, 9]
      left_inv := fun x => by revert x; decide
      right_inv := fun x => by revert x; decide }

/-- The cycle around the triangle. -/
def triangleCycle : List (Fin 10) := [0, 2, 4]

private def vertexLabel : Fin 10 → Fin 5 := ![0, 1, 1, 2, 2, 0, 0, 3, 0, 4]

private def faceLabel : Fin 10 → Fin 2 := ![0, 1, 0, 1, 0, 1, 0, 0, 1, 1]

private theorem triangle_cnode_iff (x y : Fin 10) :
    triangle.toHypermap.cnode x y ↔ vertexLabel x = vertexLabel y := by
  refine fconnect_iff_label _ _ (by decide) (fun x y h => ?_) x y
  have key : ∀ x y : Fin 10, vertexLabel x = vertexLabel y →
      ∃ n : Fin 4, (triangle.toHypermap.node)^[(n : ℕ)] x = y := by decide
  obtain ⟨n, hn⟩ := key x y h
  exact ⟨n, hn⟩

private theorem triangle_cface_iff (x y : Fin 10) :
    triangle.toHypermap.cface x y ↔ faceLabel x = faceLabel y := by
  refine fconnect_iff_label _ _ (by decide) (fun x y h => ?_) x y
  have key : ∀ x y : Fin 10, faceLabel x = faceLabel y →
      ∃ n : Fin 5, (triangle.toHypermap.face)^[(n : ℕ)] x = y := by decide
  obtain ⟨n, hn⟩ := key x y h
  exact ⟨n, hn⟩

private theorem triangle_tail_eq_iff (x y : Fin 10) :
    triangle.tail x = triangle.tail y ↔ vertexLabel x = vertexLabel y :=
  (triangle.tail_eq_iff x y).trans (triangle_cnode_iff x y)

theorem triangle_numVertices : triangle.numVertices = 5 :=
  (fcard_eq_card_image triangle.toHypermap.cnode_sym vertexLabel triangle_cnode_iff).trans
    (by decide)

theorem triangle_numFaces : triangle.numFaces = 2 :=
  (fcard_eq_card_image triangle.toHypermap.cface_sym faceLabel triangle_cface_iff).trans
    (by decide)

theorem triangle_numEdges : triangle.numEdges = 5 := by
  rw [numEdges_eq, Fintype.card_fin]

theorem triangle_connected : triangle.Connected := by
  rw [connected_iff]
  refine ⟨⟨0⟩, fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := triangle.exists_tail_eq u
  obtain ⟨y, rfl⟩ := triangle.exists_tail_eq v
  have h0 : ∀ z, triangle.toHypermap.gcomp z 0 := by
    intro z
    have hl : ∀ z : Fin 10, faceLabel z = faceLabel 0 ∨ faceLabel z = faceLabel 1 := by decide
    rcases hl z with h | h
    · exact triangle.toHypermap.gcomp_of_cface ((triangle_cface_iff z 0).2 h)
    · exact connect_trans (triangle.toHypermap.gcomp_of_cface ((triangle_cface_iff z 1).2 h))
        (connect_of_rel (Or.inl (by decide)))
  exact (triangle.gcomp_iff x y).1
    (connect_trans (h0 x) (triangle.toHypermap.glinkC _ _ (h0 y)))

theorem triangle_planar : triangle.Planar := by
  rw [planar_iff_euler _ triangle_connected, triangle_numVertices, triangle_numFaces,
    triangle_numEdges]

theorem triangle_isCycle : triangle.IsCycle triangleCycle where
  ring := by
    refine ⟨⟨?_, ?_, ?_, trivial⟩, ?_⟩
    · exact (triangle_tail_eq_iff (triangle.rev 0) 2).2 (by decide)
    · exact (triangle_tail_eq_iff (triangle.rev 2) 4).2 (by decide)
    · exact (triangle_tail_eq_iff (triangle.rev 4) 0).2 (by decide)
    · exact (nodup_map_congr triangle_tail_eq_iff _).2 (by decide)
  ne_nil := List.cons_ne_nil _ _
  rev_not_mem := by decide

private theorem triangle_rev_mem {d e : Fin 10} (hd : d ∈ triangleCycle) (he : triangle.rev d = e)
    (h : e ∉ triangleCycle) : e ∈ triangle.outside triangleCycle := by
  subst he
  exact triangle.rev_cycle_mem_outside triangle_planar triangle_isCycle.ring hd h

private theorem six_mem_inside : (6 : Fin 10) ∈ triangle.inside triangleCycle :=
  triangle.rot_symm_rev_mem_inside (c := triangleCycle) (d := 4) (by decide) (by decide)

private theorem seven_mem_inside : (7 : Fin 10) ∈ triangle.inside triangleCycle := by
  have h := triangle.rev_mem_inside triangle_planar triangle_isCycle.ring six_mem_inside
  rwa [show triangle.rev 6 = 7 by decide] at h

private theorem five_mem_outside : (5 : Fin 10) ∈ triangle.outside triangleCycle :=
  triangle_rev_mem (d := 4) (by decide) (by decide) (by decide)

private theorem eight_mem_outside : (8 : Fin 10) ∈ triangle.outside triangleCycle := by
  have h := triangle.rot_mem_outside five_mem_outside (by decide)
  rwa [show triangle.rot 5 = 8 by decide] at h

private theorem nine_mem_outside : (9 : Fin 10) ∈ triangle.outside triangleCycle := by
  have h := triangle.rev_mem_outside triangle_planar triangle_isCycle.ring eight_mem_outside
    (by decide)
  rwa [show triangle.rev 8 = 9 by decide] at h

private theorem mem_outside_of_list {x : Fin 10} (h : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 8 ∨ x = 9) :
    x ∈ triangle.outside triangleCycle := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact triangle_rev_mem (d := 0) (by decide) (by decide) (by decide)
  · exact triangle_rev_mem (d := 2) (by decide) (by decide) (by decide)
  · exact five_mem_outside
  · exact eight_mem_outside
  · exact nine_mem_outside

private theorem darts_cases (x : Fin 10) : x ∈ triangleCycle ∨ (x = 6 ∨ x = 7) ∨
    (x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 8 ∨ x = 9) := by
  revert x
  decide

/-- The inside of the cycle: the pendant edge at `p`. -/
theorem triangle_inside (x : Fin 10) :
    x ∈ triangle.inside triangleCycle ↔ x = 6 ∨ x = 7 := by
  constructor
  · intro hx
    rcases darts_cases x with h | h | h
    · exact absurd h hx.2
    · exact h
    · exact absurd hx.1 (mem_outside_of_list h)
  · rintro (rfl | rfl)
    · exact six_mem_inside
    · exact seven_mem_inside

/-- The outside of the cycle: the pendant edge at `q` and the reverses of the cycle. -/
theorem triangle_outside (x : Fin 10) :
    x ∈ triangle.outside triangleCycle ↔ x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 8 ∨ x = 9 := by
  constructor
  · intro hx
    rcases darts_cases x with h | h | h
    · exact absurd h (triangle.not_mem_of_mem_outside hx)
    · exact absurd ((triangle_inside x).2 h).1 hx
    · exact h
  · exact mem_outside_of_list

/-- Reversing the cycle: its inside is the pendant edge at `q`. -/
theorem triangle_inside_reverse (x : Fin 10) :
    x ∈ triangle.inside (triangle.reverseCycle triangleCycle) ↔ x = 8 ∨ x = 9 := by
  rw [triangle.mem_inside_reverseCycle_iff triangle_planar triangle_connected triangle_isCycle,
    triangle_outside]
  revert x
  decide

/-- Both pendant vertices are off the cycle, one on each side. -/
theorem triangle_vertices :
    triangle.InsideVertex triangleCycle (triangle.tail 7) ∧
      triangle.OutsideVertex triangleCycle (triangle.tail 9) := by
  have key : ∀ d ∈ triangleCycle,
      vertexLabel d ≠ vertexLabel 7 ∧ vertexLabel d ≠ vertexLabel 9 := by
    decide
  refine ⟨⟨?_, 7, rfl, seven_mem_inside⟩, ?_, 9, rfl, nine_mem_outside⟩
  · rintro ⟨d, hd, h⟩
    exact (key d hd).1 ((triangle_tail_eq_iff d 7).1 h)
  · rintro ⟨d, hd, h⟩
    exact (key d hd).2 ((triangle_tail_eq_iff d 9).1 h)

end Instance

end RotSystem

end SsspFlow
