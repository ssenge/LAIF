import SsspFlow.Tour
import SsspFlow.NetPad

/-!
# Disks cut along walks up a tree

`RotSystem.cone Γ` glues all corners of a set `Γ` of one component of the split `R.split Γ` to one
vertex, in the cyclic order of the first return of the faces. It is planar if the split is, and every
one of its faces has at most one corner of `Γ`.

`RotSystem.double` replaces every edge by two parallel copies with a digon between them. A rooted tree
`RootedTree` of the original map marks one copy of every tree edge. For a set `Γ` of corners that is
closed under the parent, with both digon corners of the tree edge of each of its vertices (`IsLevel`),
the marked copies at the vertices without a corner in `Γ` form a spanning forest of the cone
(`IsLevel.spanForest`).

A larger level `Γ'` that contains two corners `x ≠ y` of one face of the cone splits the cycle of the
tour through them along the arc `(x, y]`: `side` is constant on the components of `R.double.split Γ'`
(`side_gcomp`). So the forest darts of a component lie on one side (`npOf_le_mass`), and they are at
most about three quarters of those of the cycle if the two arcs are balanced (`npOf_balance`).

`RootedTree.next` adds a set of corners and the walks up the tree from them to a level. The result is a
level again (`IsLevel.next`), and each walk adds at most twice the depth of its start in corners
(`card_railsUp_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-! ### The cone over a set of corners -/

/-- The cone over `Γ`: the rotation `rot * b`, with `b` the first return of the faces to `Γ`. -/
noncomputable def cone (Γ : Finset D) : RotSystem D := R.glue (R.faceReturn Γ)

theorem cone_rot_apply (Γ : Finset D) (z : D) : (R.cone Γ).rot z = R.rot (R.faceReturn Γ z) := rfl

theorem cone_rev (Γ : Finset D) : (R.cone Γ).rev = R.rev := rfl

theorem cone_rot_of_not_mem {Γ : Finset D} {z : D} (hz : z ∉ Γ) : (R.cone Γ).rot z = R.rot z := by
  rw [cone_rot_apply, R.fixesOff_faceReturn Γ z hz]

theorem cone_facePerm (Γ : Finset D) :
    (R.cone Γ).facePerm = (R.faceReturn Γ)⁻¹ * R.facePerm :=
  R.glue_facePerm _

theorem cone_nodeReturn (Γ : Finset D) : (R.cone Γ).nodeReturn Γ = R.psi Γ :=
  R.nodeReturn_glue (R.fixesOff_faceReturn Γ)

/-- Every face of the cone has at most one corner of `Γ`. -/
theorem cone_faceReturn (Γ : Finset D) : (R.cone Γ).faceReturn Γ = 1 := by
  rw [cone, R.faceReturn_glue (R.fixesOff_faceReturn Γ), inv_mul_cancel]

theorem cone_split (Γ : Finset D) : (R.cone Γ).split Γ = R.split Γ := by
  refine RotSystem.ext rfl ?_
  show R.rot * R.faceReturn Γ * ((R.cone Γ).nodeReturn Γ)⁻¹ = R.rot * (R.nodeReturn Γ)⁻¹
  rw [cone_nodeReturn, psi, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

/-- The cone has the components of the split. -/
theorem cone_gcomp_iff (Γ : Finset D) (x y : D) :
    (R.cone Γ).toHypermap.gcomp x y ↔ (R.split Γ).toHypermap.gcomp x y := by
  constructor
  · intro h
    refine (R.cone Γ).mem_of_gcomp (A := {z | (R.split Γ).toHypermap.gcomp x z}) ?_ ?_ h
      (connect_refl x)
    · intro z hz
      exact connect_trans hz (connect_of_rel (Or.inl rfl))
    · intro z hz
      have h1 : (R.split Γ).toHypermap.gcomp z (R.psi Γ z) :=
        R.gcomp_split_of_fconnect_psi (fconnect1 _ _)
      have h2 : (R.split Γ).toHypermap.gcomp (R.psi Γ z) ((R.split Γ).rot (R.psi Γ z)) :=
        connect_of_rel (Or.inr (Or.inl rfl))
      have e : (R.split Γ).rot (R.psi Γ z) = (R.cone Γ).rot z := by
        show R.rot ((R.nodeReturn Γ)⁻¹ (R.nodeReturn Γ (R.faceReturn Γ z))) =
          R.rot (R.faceReturn Γ z)
        rw [perm_inv_apply_self]
      rw [e] at h2
      exact connect_trans hz (connect_trans h1 h2)
  · intro h
    rw [← cone_split] at h
    exact (R.cone Γ).gcomp_of_gcomp_split h

theorem permMap_one_gcomp (ψ : Equiv.Perm D) (x y : D) :
    (permMap ψ 1).gcomp x y ↔ fconnect ψ x y := by
  constructor
  · refine connect_sub fun a b hab => ?_
    rcases hab with rfl | rfl | rfl
    · refine (fconnect_inv_iff ψ).1 ?_
      have : (permMap ψ 1).edge a = ψ⁻¹ a := by
        show (ψ * 1)⁻¹ a = ψ⁻¹ a
        rw [mul_one]
      rw [this]
      exact fconnect1 _ _
    · exact fconnect1 _ _
    · exact connect_refl a
  · exact connect_mono fun a b hab => Or.inr (Or.inl hab)

theorem permMap_one_nComp (ψ : Equiv.Perm D) : nComp (permMap ψ 1).glink Set.univ = orb ψ :=
  nComp_congr (permMap_one_gcomp ψ) Set.univ

theorem permMap_one_genus (ψ : Equiv.Perm D) : (permMap ψ 1).genus = 0 := by
  have h := (permMap ψ 1).evenGenus
  unfold Hypermap.EvenGenus Hypermap.eulerLhs Hypermap.eulerRhs at h
  have he : fcard (permMap ψ 1).edge Set.univ = orb ψ := by
    show orb ((ψ * 1)⁻¹) = _
    rw [mul_one, orb_inv]
  have hn : fcard (permMap ψ 1).node Set.univ = orb ψ := rfl
  have hf : fcard (permMap ψ 1).face Set.univ = Fintype.card D := orb_one
  rw [permMap_one_nComp] at h
  omega

/-- **The cone is planar.** -/
theorem cone_planar (hR : R.Planar) (hc : R.Connected) {Γ : Finset D} (hΓ : Γ.Nonempty)
    (hS : R.SkeletonConnected Γ) : (R.cone Γ).Planar := by
  have hid := (R.cone Γ).genus_split Γ
  have hsk : (R.cone Γ).skeleton Γ = permMap (R.psi Γ) 1 := by
    rw [skeleton, cone_nodeReturn, cone_faceReturn]
  have hpsi : (R.cone Γ).psi Γ = R.psi Γ := by
    rw [psi, cone_nodeReturn, cone_faceReturn, mul_one]
  rw [cone_split, hsk, hpsi, permMap_one_nComp, permMap_one_genus] at hid
  have hP : (R.split Γ).toHypermap.genus = 0 := (R.split_planar hR hc hΓ hS).1
  have hC : (R.split Γ).numComponents = (R.cone Γ).numComponents :=
    nComp_congr (fun x y => (R.cone_gcomp_iff Γ x y).symm) _
  show (R.cone Γ).toHypermap.genus = 0
  omega

/-- Corners of `Γ` in one component of the split lie at one vertex of the cone. -/
theorem fconnect_cone_of_gcomp (hR : R.Planar) (hc : R.Connected) {Γ : Finset D} (hΓ : Γ.Nonempty)
    (hS : R.SkeletonConnected Γ) {g g' : D} (hg : g ∈ Γ) (hg' : g' ∈ Γ)
    (h : (R.split Γ).toHypermap.gcomp g g') : fconnect (R.cone Γ).rot g g' := by
  have h1 := ((R.split_planar hR hc hΓ hS).2.2.2 g hg g' hg').1 h
  rw [← cone_nodeReturn] at h1
  exact fconnect_of_fconnect_firstReturn h1

/-- Off `Γ`, the iterates of the rotation of the cone are those of the rotation. -/
theorem iterate_cone {Γ : Finset D} {z : D} (n : ℕ) (h : ∀ i, i < n → R.rot^[i] z ∉ Γ) :
    (R.cone Γ).rot^[n] z = R.rot^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun i hi => h i (by omega), cone_rot_of_not_mem _ (h n (by omega))]

/-- From a dart at a vertex with a corner of `Γ`, the rotation of the cone reaches a corner of `Γ`. -/
theorem exists_mem_fconnect_cone {Γ : Finset D} {z g : D} (hg : g ∈ Γ) (h : fconnect R.rot z g) :
    ∃ g' ∈ Γ, fconnect (R.cone Γ).rot z g' := by
  classical
  have hex : ∃ n, R.rot^[n] z ∈ Γ := by
    obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 h
    exact ⟨n, hn ▸ hg⟩
  refine ⟨_, Nat.find_spec hex, fconnect_iff_iterate.2 ⟨Nat.find hex, ?_⟩⟩
  exact R.iterate_cone _ fun i hi => Nat.find_min hex hi

/-- At a vertex without a corner of `Γ`, the rotation of the cone is the rotation. -/
theorem fconnect_cone_of_forall {Γ : Finset D} {z w : D} (h : fconnect R.rot z w)
    (hn : ∀ u, fconnect R.rot z u → u ∉ Γ) : fconnect (R.cone Γ).rot z w := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
  refine fconnect_iff_iterate.2 ⟨n, R.iterate_cone n fun i _ => hn _ (fconnect_iterate _ _ _)⟩

/-! ### The doubled map -/

/-- The rotation of the doubled map: each dart, then its second copy. -/
def doubleRot : Equiv.Perm (D × Bool) where
  toFun z := bif z.2 then (R.rot z.1, false) else (z.1, true)
  invFun z := bif z.2 then (z.1, false) else (R.rot.symm z.1, true)
  left_inv := by rintro ⟨d, _ | _⟩ <;> simp
  right_inv := by rintro ⟨d, _ | _⟩ <;> simp

/-- The doubled map: `(d, false)` and `(rev d, true)` are one copy of the edge of `d`, and between
the two copies of an edge lies a digon with the corners `(d, false)` and `(rev d, false)`. -/
def double : RotSystem (D × Bool) where
  rev z := (R.rev z.1, !z.2)
  rev_rev z := by simp [R.rev_rev]
  rev_ne z h := by
    have := congrArg Prod.snd h
    simp at this
  rot := R.doubleRot

theorem double_rev (d : D) (b : Bool) : R.double.rev (d, b) = (R.rev d, !b) := rfl

theorem double_rot_false (d : D) : R.double.rot (d, false) = (d, true) := rfl

theorem double_rot_true (d : D) : R.double.rot (d, true) = (R.rot d, false) := rfl

theorem double_face_false (d : D) : R.double.facePerm (d, false) = (R.rev d, false) := rfl

theorem double_face_true (d : D) : R.double.facePerm (d, true) = (R.facePerm d, true) := rfl

/-- Darts at one vertex have copies at one vertex. -/
theorem fconnect_double {d d' : D} (h : fconnect R.rot d d') (b b' : Bool) :
    fconnect R.double.rot (d, b) (d', b') := by
  have h0 : ∀ e, fconnect R.double.rot (e, false) (e, true) := fun e => fconnect1 _ _
  have h1 : ∀ e, fconnect R.double.rot (e, true) (R.rot e, false) := fun e => fconnect1 _ _
  have h2 : fconnect R.double.rot (d, false) (d', false) := by
    induction h with
    | refl => exact connect_refl _
    | @tail e c _ hec ih =>
      obtain rfl : R.rot e = c := hec
      exact connect_trans ih (connect_trans (h0 e) (h1 e))
  have h3 : fconnect R.double.rot (d, b) (d, false) := by
    cases b
    · exact connect_refl _
    · exact fconnect_symm (h0 d)
  have h4 : fconnect R.double.rot (d', false) (d', b') := by
    cases b'
    · exact connect_refl _
    · exact h0 d'
  exact connect_trans h3 (connect_trans h2 h4)

/-- Darts in one component have copies in one component. -/
theorem gcomp_double {d d' : D} (h : R.toHypermap.gcomp d d') (b b' : Bool) :
    R.double.toHypermap.gcomp (d, b) (d', b') := by
  have hnode : ∀ {z z' : D × Bool}, fconnect R.double.rot z z' → R.double.toHypermap.gcomp z z' :=
    fun hz => R.double.toHypermap.gcomp_of_cnode hz
  have h2 : R.double.toHypermap.gcomp (d, false) (d', false) := by
    refine R.mem_of_gcomp (A := {e | R.double.toHypermap.gcomp (d, false) (e, false)}) ?_ ?_ h
      (connect_refl _)
    · intro e he
      exact connect_trans he (connect_trans (hnode (fconnect1 _ _)) (connect_of_rel (Or.inl rfl)))
    · intro e he
      exact connect_trans he (hnode (fconnect_double R (fconnect1 _ _) _ _))
  exact connect_trans (hnode (fconnect_double R (connect_refl d) b false))
    (connect_trans h2 (hnode (fconnect_double R (connect_refl d') false b')))

theorem double_connected (hc : R.Connected) : R.double.Connected := by
  have hne : Nonempty D := ((R.connected_iff).1 hc).1
  obtain ⟨d⟩ := hne
  refine nComp_eq_one_of_connect R.double.toHypermap.glinkC (s := Set.univ)
    ⟨(d, false), Set.mem_univ _⟩ fun x _ y _ => ?_
  obtain ⟨dx, bx⟩ := x
  obtain ⟨dy, by'⟩ := y
  exact R.gcomp_double (connect_of_nComp_eq_one R.toHypermap.glinkC hc (Set.mem_univ dx)
    (Set.mem_univ dy)) bx by'

/-- **The doubled map is planar.** -/
theorem double_planar (hR : R.Planar) (hc : R.Connected) : R.double.Planar := by
  refine R.double.planar_of_count (R.double_connected hc) ?_
  have hE := R.double.numEdges_eq
  have hE0 := R.card_eq
  have hcard : Fintype.card (D × Bool) = 2 * Fintype.card D := by
    rw [Fintype.card_prod, Fintype.card_bool, mul_comm]
  have hV : R.numVertices ≤ R.double.numVertices := by
    rw [← R.natCard_vertex, numVertices_eq_orb]
    refine card_le_orb _ (fun z => R.tail z.1) ?_ ?_
    · rintro ⟨d, _ | _⟩
      · rfl
      · exact ((R.tail_eq_iff _ _).2 (R.toHypermap.cnodeC.1 (fconnect1 (⇑R.rot) d)))
    · intro v
      obtain ⟨x, rfl⟩ := R.exists_tail_eq v
      exact ⟨(x, false), rfl⟩
  have hF : R.numFaces + R.numEdges ≤ R.double.numFaces := by
    have hc1 : Nat.card ↥(Set.univ.image (comp (frel R.toHypermap.edge))) = R.numEdges := by
      rw [Nat.card_coe_set_eq]
      rfl
    rw [← R.natCard_face, ← hc1, ← Nat.card_sum, numFaces_eq_orb]
    refine card_le_orb _ (fun z => bif z.2 then Sum.inl (R.faceOf z.1)
      else Sum.inr ⟨comp (frel R.toHypermap.edge) z.1, z.1, Set.mem_univ _, rfl⟩) ?_ ?_
    · rintro ⟨d, _ | _⟩
      · simp only [double_face_false, Bool.cond_false]
        congr 2
        exact (comp_eq_iff (fconnect_sym R.rev_injective)).2 (connect_of_rel (R.rev_rev d))
      · simp only [double_face_true, Bool.cond_true]
        congr 1
        exact (R.faceOf_eq_iff _ _).2 (R.toHypermap.cfaceC.1 (fconnect1 _ _))
    · rintro (f | ⟨_, x, _, rfl⟩)
      · obtain ⟨x, rfl⟩ := Quotient.exists_rep f
        exact ⟨(x, true), rfl⟩
      · exact ⟨(x, false), rfl⟩
  have hEu := R.euler_components hR
  have hC1 : R.numComponents = 1 := hc
  omega

/-! ### A rooted tree -/

/-- A rooted spanning tree of `R`, with an explicit type of vertices: every vertex except the root has
a dart `up v` to its parent, which has a smaller depth. -/
structure RootedTree (V : Type*) where
  /-- The vertex of a dart. -/
  vert : D → V
  vert_eq_iff : ∀ d d', vert d = vert d' ↔ fconnect R.rot d d'
  /-- The root. -/
  root : V
  /-- The depth of a vertex. -/
  dep : V → ℕ
  dep_root : dep root = 0
  /-- The dart to the parent. -/
  up : V → D
  vert_up : ∀ v, v ≠ root → vert (up v) = v
  dep_par : ∀ v, v ≠ root → dep (vert (R.rev (up v))) + 1 = dep v

namespace RootedTree

variable {R} {V : Type*} [Fintype V] [DecidableEq V] (t : R.RootedTree V)

/-- The vertex of a dart of the doubled map. -/
def vertM (z : D × Bool) : V := t.vert z.1

/-- The parent. -/
def par (v : V) : V := t.vert (R.rev (t.up v))

/-- The dart at `v` of the marked copy of the tree edge of `v`. -/
def c1 (v : V) : D × Bool := (t.up v, true)

/-- The dart at the parent of the marked copy of the tree edge of `v`. It is also a corner of the digon
of the tree edge. -/
def c0 (v : V) : D × Bool := (R.rev (t.up v), false)

/-- The corner at `v` of the digon of the tree edge of `v`. -/
def r0 (v : V) : D × Bool := (t.up v, false)

theorem vertM_c1 {v : V} (h : v ≠ t.root) : t.vertM (t.c1 v) = v := t.vert_up v h

theorem vertM_r0 {v : V} (h : v ≠ t.root) : t.vertM (t.r0 v) = v := t.vert_up v h

theorem vertM_c0 (v : V) : t.vertM (t.c0 v) = t.par v := rfl

theorem rev_c1 (v : V) : R.double.rev (t.c1 v) = t.c0 v := rfl

theorem rev_c0 (v : V) : R.double.rev (t.c0 v) = t.c1 v := by
  simp [c0, c1, double_rev, R.rev_rev]

theorem rot_r0 (v : V) : R.double.rot (t.r0 v) = t.c1 v := rfl

theorem dep_par_lt {v : V} (h : v ≠ t.root) : t.dep (t.par v) < t.dep v := by
  have := t.dep_par v h
  unfold par
  omega

theorem up_inj {v v' : V} (h : v ≠ t.root) (h' : v' ≠ t.root) (e : t.up v = t.up v') : v = v' := by
  rw [← t.vert_up v h, ← t.vert_up v' h', e]

theorem vertM_rot (z : D × Bool) : t.vertM (R.double.rot z) = t.vertM z := by
  obtain ⟨d, _ | _⟩ := z
  · rfl
  · exact (t.vert_eq_iff _ _).2 (fconnect_symm (fconnect1 (⇑R.rot) d))

theorem vertM_eq_iff (z z' : D × Bool) : t.vertM z = t.vertM z' ↔ fconnect R.double.rot z z' := by
  constructor
  · intro h
    obtain ⟨d, b⟩ := z
    obtain ⟨d', b'⟩ := z'
    exact R.fconnect_double ((t.vert_eq_iff d d').1 h) b b'
  · intro h
    induction h with
    | refl => rfl
    | @tail e c _ hec ih =>
      obtain rfl : R.double.rot e = c := hec
      exact ih.trans (t.vertM_rot e).symm

/-- `v` has no corner in `Γ`. -/
def NP (Γ : Finset (D × Bool)) (v : V) : Prop := ∀ z ∈ Γ, t.vertM z ≠ v

open Classical in
/-- The darts of the marked copies of the tree edges of the vertices without a corner in `Γ`. -/
noncomputable def marks (Γ : Finset (D × Bool)) : Finset (D × Bool) :=
  Finset.univ.filter fun z => ∃ v, t.NP Γ v ∧ (z = t.c1 v ∨ z = t.c0 v)

theorem mem_marks {Γ : Finset (D × Bool)} {z : D × Bool} :
    z ∈ t.marks Γ ↔ ∃ v, t.NP Γ v ∧ (z = t.c1 v ∨ z = t.c0 v) := by
  simp [marks]

theorem marks_revClosed (Γ : Finset (D × Bool)) : R.double.RevClosed (t.marks Γ) := by
  intro z hz
  obtain ⟨v, hv, rfl | rfl⟩ := t.mem_marks.1 hz
  · exact t.mem_marks.2 ⟨v, hv, Or.inr rfl⟩
  · exact t.mem_marks.2 ⟨v, hv, Or.inl (t.rev_c0 v)⟩

theorem cone_marks_revClosed (Γ : Finset (D × Bool)) :
    (R.double.cone Γ).RevClosed (t.marks Γ) :=
  t.marks_revClosed Γ

/-- A set of corners that is closed under the parent, with the digon corners of the tree edge of each
of its vertices. Digon corners come in pairs, and the set is connected. -/
structure IsLevel (Γ : Finset (D × Bool)) : Prop where
  root_mem : ∃ z ∈ Γ, t.vertM z = t.root
  rails : ∀ z ∈ Γ, t.vertM z ≠ t.root → t.r0 (t.vertM z) ∈ Γ ∧ t.c0 (t.vertM z) ∈ Γ
  pairs : ∀ d, (d, false) ∈ Γ → (R.rev d, false) ∈ Γ
  skel : R.double.SkeletonConnected Γ

/-- `v` is `w` or an ancestor of `w`. -/
inductive Anc (v : V) : V → Prop
  | refl : Anc v v
  | step {w : V} (hw : w ≠ t.root) (h : Anc v (t.par w)) : Anc v w

variable {t}

theorem NP.ne_root {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) {v : V} (hv : t.NP Γ v) :
    v ≠ t.root := by
  rintro rfl
  obtain ⟨z, hz, hzv⟩ := hL.root_mem
  exact hv z hz hzv

theorem NP.not_mem {Γ : Finset (D × Bool)} {v : V} (hv : t.NP Γ v) {z : D × Bool}
    (hz : t.vertM z = v) : z ∉ Γ := fun h => hv z h hz

theorem NP.mono {Γ Γ' : Finset (D × Bool)} (h : Γ ⊆ Γ') {v : V} (hv : t.NP Γ' v) : t.NP Γ v :=
  fun z hz => hv z (h hz)

/-- The digon corners of all ancestors of a vertex with a corner in a level are in the level. -/
theorem IsLevel.rails_of_anc {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) {v w : V}
    (h : t.Anc v w) (hv : v ≠ t.root) {z : D × Bool} (hz : z ∈ Γ) (hzw : t.vertM z = w) :
    t.r0 v ∈ Γ ∧ t.c0 v ∈ Γ := by
  induction h generalizing z with
  | refl =>
    have := hL.rails z hz (by rw [hzw]; exact hv)
    rwa [hzw] at this
  | @step w hw _ ih =>
    have := hL.rails z hz (by rw [hzw]; exact hw)
    rw [hzw] at this
    exact ih this.2 rfl

/-- A vertex without a corner has a digon of its tree edge without a corner in the level. -/
theorem IsLevel.c0_not_mem {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) {v : V} (hv : t.NP Γ v) :
    t.c0 v ∉ Γ := fun h => by
  have h1 := hL.pairs _ h
  rw [R.rev_rev] at h1
  exact hv.not_mem (t.vertM_r0 (hv.ne_root hL)) h1

/-! ### The forest of a level -/

section Forest

variable {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected)

include hL

theorem IsLevel.nonempty : Γ.Nonempty := by
  obtain ⟨z, hz, _⟩ := hL.root_mem
  exact ⟨z, hz⟩

/-- At a vertex without a corner, the rotation of the cone reaches the marked dart. -/
theorem IsLevel.fconnect_c1 {v : V} (hv : t.NP Γ v) {z : D × Bool} (hz : t.vertM z = v) :
    fconnect (R.double.cone Γ).rot z (t.c1 v) := by
  have hne := hv.ne_root hL
  have hzc : t.vertM z = t.vertM (t.c1 v) := by rw [hz, t.vertM_c1 hne]
  refine R.double.fconnect_cone_of_forall ((t.vertM_eq_iff _ _).1 hzc) fun u hu => ?_
  exact hv.not_mem (((t.vertM_eq_iff _ _).2 hu).symm.trans hz)

omit hL in
/-- Everything below a vertex: walking up along `F` reaches a corner of `Γ`, as long as `F` contains
the marked darts on the way. -/
theorem IsLevel.exists_port' (hL : t.IsLevel Γ) {F : Finset (D × Bool)}
    (hF : (R.double.cone Γ).RevClosed F) (n : ℕ) :
    ∀ z : D × Bool, t.dep (t.vertM z) = n → (∀ w, t.NP Γ w → t.Anc w (t.vertM z) → t.c1 w ∈ F) →
      ∃ g ∈ Γ, ((R.double.cone Γ).tourMap F).gcomp z g := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn hup
    have hnode : ∀ {a b : D × Bool}, fconnect (R.double.cone Γ).rot a b →
        ((R.double.cone Γ).tourMap F).gcomp a b := fun h =>
      connect_mono (fun _ _ hab => Or.inr (Or.inl hab)) h
    by_cases hv : t.NP Γ (t.vertM z)
    · have hne := hv.ne_root hL
      have h1 := hL.fconnect_c1 hv rfl
      have hc1 := hup _ hv Anc.refl
      have h2 : ((R.double.cone Γ).tourMap F).gcomp (t.c1 (t.vertM z)) (t.c0 (t.vertM z)) := by
        refine connect_of_rel (Or.inl ?_)
        show ((R.double.cone Γ).rot * ((R.double.cone Γ).rot⁻¹ * (R.double.cone Γ).revOn F))⁻¹ _ = _
        rw [(R.double.cone Γ).tourMap_edge_inv, revOn_of_mem hF hc1]
        exact t.rev_c1 _
      obtain ⟨g, hg, h3⟩ := ih (t.dep (t.vertM (t.c0 (t.vertM z))))
        (by rw [← hn, t.vertM_c0]; exact t.dep_par_lt hne) _ rfl
        (fun w hw ha => hup w hw (Anc.step hne ha))
      exact ⟨g, hg, connect_trans (hnode h1) (connect_trans h2 h3)⟩
    · have hv' : ∃ g ∈ Γ, t.vertM g = t.vertM z := by
        by_contra hn'
        push Not at hn'
        exact hv hn'
      obtain ⟨g, hg, hgz⟩ := hv'
      obtain ⟨g', hg', h1⟩ := R.double.exists_mem_fconnect_cone hg
        ((t.vertM_eq_iff z g).1 hgz.symm)
      exact ⟨g', hg', hnode h1⟩

include hR hc

theorem IsLevel.cone_planar : (R.double.cone Γ).Planar :=
  R.double.cone_planar (R.double_planar hR hc) (R.double_connected hc) hL.nonempty hL.skel

/-- Corners of `Γ` in one component of the cone lie at one vertex of the cone. -/
theorem IsLevel.fconnect_ports {g g' : D × Bool} (hg : g ∈ Γ) (hg' : g' ∈ Γ)
    (h : (R.double.cone Γ).toHypermap.gcomp g g') : fconnect (R.double.cone Γ).rot g g' :=
  R.double.fconnect_cone_of_gcomp (R.double_planar hR hc) (R.double_connected hc) hL.nonempty hL.skel
    hg hg' ((R.double.cone_gcomp_iff Γ _ _).1 h)

/-- Two darts in one component of the cone are joined along any `F` that contains the marked darts
above both of them. -/
theorem IsLevel.gcomp_of_up {F : Finset (D × Bool)} (hF : (R.double.cone Γ).RevClosed F)
    {x y : D × Bool} (hxy : (R.double.cone Γ).toHypermap.gcomp x y)
    (hx : ∀ w, t.NP Γ w → t.Anc w (t.vertM x) → t.c1 w ∈ F)
    (hy : ∀ w, t.NP Γ w → t.Anc w (t.vertM y) → t.c1 w ∈ F) :
    ((R.double.cone Γ).tourMap F).gcomp x y := by
  obtain ⟨g, hg, h1⟩ := hL.exists_port' hF _ x rfl hx
  obtain ⟨g', hg', h2⟩ := hL.exists_port' hF _ y rfl hy
  have h1' := gcomp_of_gcomp_tourMap hF h1
  have h2' := gcomp_of_gcomp_tourMap hF h2
  have hgg : (R.double.cone Γ).toHypermap.gcomp g g' :=
    connect_trans ((R.double.cone Γ).toHypermap.glinkC _ _ h1')
      (connect_trans hxy h2')
  have h3 := hL.fconnect_ports hR hc hg hg' hgg
  have h3' : ((R.double.cone Γ).tourMap F).gcomp g g' :=
    connect_mono (fun _ _ hab => Or.inr (Or.inl hab)) h3
  exact connect_trans h1 (connect_trans h3' (((R.double.cone Γ).tourMap F).glinkC _ _ h2))

/-- The number of marked darts is twice the number of vertices without a corner. -/
theorem IsLevel.marks_card : (t.marks Γ).card / 2 = Nat.card {v // t.NP Γ v} := by
  classical
  let U : Finset V := Finset.univ.filter (t.NP Γ)
  have hU : t.marks Γ = U.image t.c1 ∪ U.image t.c0 := by
    ext z
    simp only [t.mem_marks, Finset.mem_union, Finset.mem_image, U, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl | rfl⟩
      · exact Or.inl ⟨v, hv, rfl⟩
      · exact Or.inr ⟨v, hv, rfl⟩
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact ⟨v, hv, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr rfl⟩
  have hd : Disjoint (U.image t.c1) (U.image t.c0) := by
    refine Finset.disjoint_left.2 fun z h1 h2 => ?_
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v', _, h⟩ := Finset.mem_image.1 h2
    have := congrArg Prod.snd h
    simp [c0, c1] at this
  have h1 : (U.image t.c1).card = U.card := Finset.card_image_of_injOn fun v hv v' hv' e => by
    have hv1 : t.NP Γ v := (Finset.mem_filter.1 hv).2
    have hv2 : t.NP Γ v' := (Finset.mem_filter.1 hv').2
    exact t.up_inj (hv1.ne_root hL) (hv2.ne_root hL) (congrArg Prod.fst e)
  have h2 : (U.image t.c0).card = U.card := Finset.card_image_of_injOn fun v hv v' hv' e => by
    have hv1 : t.NP Γ v := (Finset.mem_filter.1 hv).2
    have hv2 : t.NP Γ v' := (Finset.mem_filter.1 hv').2
    exact t.up_inj (hv1.ne_root hL) (hv2.ne_root hL) (R.rev_injective (congrArg Prod.fst e))
  have h3 : Nat.card {v // t.NP Γ v} = U.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hU, Finset.card_union_of_disjoint hd, h1, h2, h3]
  omega

/-- **The marked darts are a spanning forest of the cone.** -/
theorem IsLevel.spanForest : (R.double.cone Γ).SpanForest (t.marks Γ) := by
  classical
  have hF := t.cone_marks_revClosed Γ
  have hspan : ∀ x, ((R.double.cone Γ).tourMap (t.marks Γ)).gcomp x ((R.double.cone Γ).rev x) :=
    fun x => hL.gcomp_of_up hR hc hF (connect_of_rel (Or.inl rfl))
      (fun w hw _ => t.mem_marks.2 ⟨w, hw, Or.inl rfl⟩)
      (fun w hw _ => t.mem_marks.2 ⟨w, hw, Or.inl rfl⟩)
  refine ⟨hF, le_antisymm (numVertices_le_of_span hF hspan) ?_, hspan⟩
  have hC : (R.double.cone Γ).numComponents = (R.double.split Γ).numComponents :=
    nComp_congr (R.double.cone_gcomp_iff Γ) _
  have hc1 : Nat.card ↥(Set.univ.image (comp (R.double.split Γ).toHypermap.glink)) =
      (R.double.split Γ).numComponents := by
    rw [Nat.card_coe_set_eq]
    rfl
  rw [hL.marks_card hR hc, hC, ← hc1, add_comm, ← Nat.card_sum, numVertices_eq_orb]
  have hne : ∀ {z : D × Bool}, ¬ t.NP Γ (t.vertM z) → ¬ t.NP Γ (t.vertM ((R.double.cone Γ).rot z)) := by
    intro z hz
    by_cases hzΓ : z ∈ Γ
    · intro h
      have hb := ((R.double.fixesOff_faceReturn Γ).mem_iff z).2 hzΓ
      have : t.vertM ((R.double.cone Γ).rot z) = t.vertM (R.double.faceReturn Γ z) := t.vertM_rot _
      exact h _ hb this.symm
    · rw [R.double.cone_rot_of_not_mem hzΓ, t.vertM_rot]
      exact hz
  have hg := (R.double.split Γ).toHypermap.glinkC
  refine card_le_orb _ (fun z => if h : t.NP Γ (t.vertM z) then Sum.inl ⟨t.vertM z, h⟩
    else Sum.inr ⟨comp (R.double.split Γ).toHypermap.glink z, z, Set.mem_univ _, rfl⟩) ?_ ?_
  · intro z
    by_cases h : t.NP Γ (t.vertM z)
    · have hzΓ := h.not_mem (z := z) rfl
      have e : t.vertM ((R.double.cone Γ).rot z) = t.vertM z := by
        rw [R.double.cone_rot_of_not_mem hzΓ, t.vertM_rot]
      have h' : t.NP Γ (t.vertM ((R.double.cone Γ).rot z)) := by rwa [e]
      beta_reduce
      rw [dite_eq_left h', dite_eq_left h]
      exact congrArg Sum.inl (Subtype.ext e)
    · have h' := hne h
      beta_reduce
      rw [dite_eq_right h', dite_eq_right h]
      have h1 : (R.double.split Γ).toHypermap.gcomp ((R.double.cone Γ).rot z) z :=
        (R.double.cone_gcomp_iff Γ _ _).1 ((R.double.cone Γ).toHypermap.glinkC _ _
          (connect_of_rel (Or.inr (Or.inl rfl))))
      exact congrArg Sum.inr (Subtype.ext ((comp_eq_iff hg).2 h1))
  · rintro (⟨v, hv⟩ | ⟨_, x, _, rfl⟩)
    · have e := t.vertM_c1 (hv.ne_root hL)
      have h' : t.NP Γ (t.vertM (t.c1 v)) := by rwa [e]
      refine ⟨t.c1 v, ?_⟩
      beta_reduce
      rw [dite_eq_left h']
      exact congrArg Sum.inl (Subtype.ext e)
    · obtain ⟨g, hg', hxg⟩ := R.double.split_meets (R.double_connected hc) hL.nonempty x
      have h' : ¬ t.NP Γ (t.vertM g) := fun h => h g hg' rfl
      refine ⟨g, ?_⟩
      beta_reduce
      rw [dite_eq_right h']
      exact congrArg Sum.inr (Subtype.ext ((comp_eq_iff hg).2 (hg _ _ hxg)))

end Forest

/-! ### The side of a cut -/

variable (t) in
/-- The tour of the marked darts on the cone. -/
noncomputable def tourL (Γ : Finset (D × Bool)) : Equiv.Perm (D × Bool) :=
  (R.double.cone Γ).tour (t.marks Γ)

open Classical in
variable (t) in
/-- The side of a dart with respect to the arc `(x, y]`. A marked dart at a parent takes the side of
its reverse. -/
def side (Γ : Finset (D × Bool)) (x y u : D × Bool) : Prop :=
  InArc (t.tourL Γ) x y (if ∃ v, t.NP Γ v ∧ u = t.c0 v then R.double.rev u else u)

section Side

variable {Γ : Finset (D × Bool)} {x y : D × Bool}

theorem c1_ne_c0 (v v' : V) : t.c1 v ≠ t.c0 v' := fun h => by
  have := congrArg Prod.snd h
  simp [c0, c1] at this

theorem side_c1 (v : V) : t.side Γ x y (t.c1 v) ↔ InArc (t.tourL Γ) x y (t.c1 v) := by
  unfold side
  rw [if_neg]
  rintro ⟨v', _, h⟩
  exact c1_ne_c0 v v' h

theorem side_c0 {v : V} (hv : t.NP Γ v) :
    t.side Γ x y (t.c0 v) ↔ InArc (t.tourL Γ) x y (t.c1 v) := by
  unfold side
  rw [if_pos ⟨v, hv, rfl⟩, t.rev_c0]

theorem side_of_not_c0 {u : D × Bool} (h : ¬ ∃ v, t.NP Γ v ∧ u = t.c0 v) :
    t.side Γ x y u ↔ InArc (t.tourL Γ) x y u := by
  unfold side
  rw [if_neg h]

theorem not_mem_marks_rev {u : D × Bool} (hu : u ∉ t.marks Γ) : R.double.rev u ∉ t.marks Γ := by
  intro h
  have := t.marks_revClosed Γ _ h
  rw [R.double.rev_rev] at this
  exact hu this

variable (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected)
  (hxy : x ≠ y) (hf : fconnect (⇑(R.double.cone Γ).facePerm⁻¹) x y)

include hL hR hc hxy hf

/-- The two darts of an edge lie on one side. -/
theorem side_rev (u : D × Bool) : t.side Γ x y (R.double.rev u) ↔ t.side Γ x y u := by
  by_cases hu : u ∈ t.marks Γ
  · obtain ⟨v, hv, rfl | rfl⟩ := t.mem_marks.1 hu
    · rw [t.rev_c1, side_c0 hv, side_c1]
    · rw [t.rev_c0, side_c0 hv, side_c1]
  · have h1 : ¬ ∃ v, t.NP Γ v ∧ u = t.c0 v := by
      rintro ⟨v, hv, rfl⟩
      exact hu (t.mem_marks.2 ⟨v, hv, Or.inr rfl⟩)
    have h2 : ¬ ∃ v, t.NP Γ v ∧ R.double.rev u = t.c0 v := by
      rintro ⟨v, hv, h⟩
      exact not_mem_marks_rev hu (t.mem_marks.2 ⟨v, hv, Or.inr h⟩)
    rw [side_of_not_c0 h1, side_of_not_c0 h2]
    have hS := hL.spanForest hR hc
    exact (inArc_iff_of_swap (hS.fconnect_tour_rev u)
      (hS.fconnect_swap_of_face (hL.cone_planar hR hc) hu hxy hf)).symm

variable {Γ' : Finset (D × Bool)} (hL' : t.IsLevel Γ') (hx : x ∈ Γ') (hy : y ∈ Γ')

include hL' hx hy

/-- A marked edge whose digon has a corner outside the larger level lies on one side. -/
theorem arc_c1_iff_c0 {v : V} (hv : t.NP Γ v) (hrail : t.r0 v ∉ Γ' ∨ t.c0 v ∉ Γ') :
    InArc (t.tourL Γ) x y (t.c1 v) ↔ InArc (t.tourL Γ) x y (t.c0 v) := by
  have hS := hL.spanForest hR hc
  have hne := hv.ne_root hL
  have hu : t.c1 v ∈ t.marks Γ := t.mem_marks.2 ⟨v, hv, Or.inl rfl⟩
  have hanc : ∀ {z : D × Bool}, z ∈ Γ' → ¬ t.Anc v (t.vertM z) := fun hz ha => by
    obtain ⟨h1, h2⟩ := hL'.rails_of_anc ha hne hz rfl
    rcases hrail with h | h
    · exact h h1
    · exact h h2
  have hup : ∀ {z : D × Bool}, z ∈ Γ' → ∀ w, t.NP Γ w → t.Anc w (t.vertM z) →
      t.c1 w ∈ ((t.marks Γ).erase (t.c1 v)).erase ((R.double.cone Γ).rev (t.c1 v)) := by
    intro z hz w hw ha
    have hwv : w ≠ v := by
      rintro rfl
      exact hanc hz ha
    simp only [Finset.mem_erase]
    refine ⟨?_, ?_, t.mem_marks.2 ⟨w, hw, Or.inl rfl⟩⟩
    · exact c1_ne_c0 w v
    · exact fun e => hwv (t.up_inj (hw.ne_root hL) hne (congrArg Prod.fst e))
  have hxy' : (R.double.cone Γ).toHypermap.gcomp x y :=
    (hS.fconnect_tour_iff _ _).1 (hS.fconnect_tour_of_face hf)
  have h1 := hL.gcomp_of_up hR hc (revClosed_erase hS.rev_closed (t.c1 v)) hxy' (hup hx) (hup hy)
  exact inArc_iff_of_swap (hS.fconnect_tour_rev (t.c1 v)) (hS.fconnect_swap_of_erase hu h1)

variable (hsub : Γ ⊆ Γ')

include hsub

/-- The side does not change along the rotation at a dart outside the larger level. -/
theorem side_rot {u : D × Bool} (hu : u ∉ Γ') :
    t.side Γ x y (R.double.rot u) ↔ t.side Γ x y u := by
  have hS := hL.spanForest hR hc
  have huΓ : u ∉ Γ := fun h => hu (hsub h)
  have hrot : (R.double.cone Γ).rot u = R.double.rot u := R.double.cone_rot_of_not_mem huΓ
  have hstep : InArc (t.tourL Γ) x y (t.tourL Γ u) ↔ InArc (t.tourL Γ) x y u :=
    inArc_apply_iff (fun e => hu (e ▸ hx)) (fun e => hu (e ▸ hy))
  have hside : t.side Γ x y u ↔ InArc (t.tourL Γ) x y u := by
    by_cases h : ∃ v, t.NP Γ v ∧ u = t.c0 v
    · obtain ⟨v, hv, rfl⟩ := h
      rw [side_c0 hv]
      exact arc_c1_iff_c0 hL hR hc hxy hf hL' hx hy hv (Or.inr hu)
    · exact side_of_not_c0 h
  have htour : t.tourL Γ u = (R.double.cone Γ).revOn (t.marks Γ) (R.double.rot u) := by
    show (R.double.cone Γ).revOn (t.marks Γ) ((R.double.cone Γ).rot u) = _
    rw [hrot]
  rw [hside, ← hstep, htour]
  by_cases hw : R.double.rot u ∈ t.marks Γ
  · rw [revOn_of_mem hS.rev_closed hw]
    obtain ⟨v, hv, h | h⟩ := t.mem_marks.1 hw
    · have hur : u = t.r0 v := R.double.rot.injective (h.trans (t.rot_r0 v).symm)
      rw [h]
      show t.side Γ x y (t.c1 v) ↔ InArc (t.tourL Γ) x y (R.double.rev (t.c1 v))
      rw [side_c1, t.rev_c1]
      exact arc_c1_iff_c0 hL hR hc hxy hf hL' hx hy hv (Or.inl (hur ▸ hu))
    · rw [h]
      show t.side Γ x y (t.c0 v) ↔ InArc (t.tourL Γ) x y (R.double.rev (t.c0 v))
      rw [side_c0 hv, t.rev_c0]
  · rw [revOn_of_not_mem hw]
    refine side_of_not_c0 ?_
    rintro ⟨v, hv, h⟩
    exact hw (t.mem_marks.2 ⟨v, hv, Or.inr h⟩)

/-- **The side is constant on the components of the split at the larger level.** -/
theorem side_gcomp {u u' : D × Bool} (h : (R.double.split Γ').toHypermap.gcomp u u') :
    t.side Γ x y u ↔ t.side Γ x y u' := by
  have h' := (R.double.gcomp_split_iff Γ' u u').1 h
  induction h' with
  | rel a b hab =>
    rcases hab with rfl | ⟨ha, rfl⟩
    · exact (side_rev hL hR hc hxy hf a).symm
    · exact (side_rot hL hR hc hxy hf hL' hx hy hsub ha).symm
  | refl a => exact Iff.rfl
  | symm a b hab ih =>
    exact (ih ((R.double.gcomp_split_iff Γ' a b).2 hab)).symm
  | trans a b c hab hbc ih1 ih2 =>
    exact (ih1 ((R.double.gcomp_split_iff Γ' a b).2 hab)).trans
      (ih2 ((R.double.gcomp_split_iff Γ' b c).2 hbc))

/-- Two corners of the cut that are not marked darts at a parent lie in different components. -/
theorem not_gcomp_of_cut (hnx : ¬ ∃ v, t.NP Γ v ∧ x = t.c0 v) (hny : ¬ ∃ v, t.NP Γ v ∧ y = t.c0 v) :
    ¬ (R.double.split Γ').toHypermap.gcomp x y := by
  intro h
  have hS := hL.spanForest hR hc
  have h1 := side_gcomp hL hR hc hxy hf hL' hx hy hsub h
  rw [side_of_not_c0 hnx, side_of_not_c0 hny] at h1
  exact not_inArc_start (h1.2 (inArc_end (hS.fconnect_tour_of_face hf) hxy.symm))

end Side

/-! ### Balance -/

section Balance

variable (t) in
open Classical in
/-- The number of marked darts in the component of `u` in the split at `Γ`. It is twice the number of
vertices without a corner in this component. -/
noncomputable def npOf (Γ : Finset (D × Bool)) (u : D × Bool) : ℕ :=
  ((t.marks Γ).filter ((R.double.split Γ).toHypermap.gcomp u)).card

variable {Γ Γ' : Finset (D × Bool)} {x y : D × Bool}

theorem marks_mono (hsub : Γ ⊆ Γ') : t.marks Γ' ⊆ t.marks Γ := fun z hz => by
  obtain ⟨v, hv, h⟩ := t.mem_marks.1 hz
  exact t.mem_marks.2 ⟨v, hv.mono hsub, h⟩

/-- A component of the split at a larger set lies in a component of the split. -/
theorem gcomp_split_mono (hsub : Γ ⊆ Γ') {u u' : D × Bool}
    (h : (R.double.split Γ').toHypermap.gcomp u u') : (R.double.split Γ).toHypermap.gcomp u u' := by
  rw [← R.double.split_split hsub] at h
  exact (R.double.split Γ).gcomp_of_gcomp_split h

/-- The number of marked darts of a component does not grow. -/
theorem npOf_mono (hsub : Γ ⊆ Γ') (u : D × Bool) : t.npOf Γ' u ≤ t.npOf Γ u := by
  classical
  refine Finset.card_le_card fun z hz => ?_
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨marks_mono hsub hz.1, gcomp_split_mono hsub hz.2⟩

theorem cycMass_eq_npOf (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected) (u : D × Bool) :
    cycMass (t.tourL Γ) (t.marks Γ) u = t.npOf Γ u := by
  classical
  have hS := hL.spanForest hR hc
  unfold cycMass npOf
  congr 1
  ext z
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  rw [show t.tourL Γ = (R.double.cone Γ).tour (t.marks Γ) from rfl, hS.fconnect_tour_iff,
    R.double.cone_gcomp_iff]

/-- **The marked darts of a component of the split at the larger level lie in one of the two arcs.** -/
theorem npOf_le_mass (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected) (hxy : x ≠ y)
    (hf : fconnect (⇑(R.double.cone Γ).facePerm⁻¹) x y) (hL' : t.IsLevel Γ') (hx : x ∈ Γ')
    (hy : y ∈ Γ') (hsub : Γ ⊆ Γ') {u : D × Bool}
    (hu : (R.double.split Γ).toHypermap.gcomp x u) :
    t.npOf Γ' u ≤ mass (t.tourL Γ) (t.marks Γ) x y ∨
      t.npOf Γ' u ≤ mass (t.tourL Γ) (t.marks Γ) y x := by
  classical
  have hS := hL.spanForest hR hc
  have hcxy : fconnect (t.tourL Γ) x y := hS.fconnect_tour_of_face hf
  have key : ∀ z ∈ t.marks Γ', (R.double.split Γ').toHypermap.gcomp u z →
      z ∈ t.marks Γ ∧ fconnect (t.tourL Γ) x z ∧ (t.side Γ x y u ↔ InArc (t.tourL Γ) x y z) := by
    intro z hz huz
    obtain ⟨v, hv, h⟩ := t.mem_marks.1 hz
    have hvΓ := hv.mono hsub
    have hcz : fconnect (t.tourL Γ) x z := by
      refine (hS.fconnect_tour_iff _ _).2 ((R.double.cone_gcomp_iff Γ _ _).2 ?_)
      exact connect_trans hu (gcomp_split_mono hsub huz)
    refine ⟨marks_mono hsub hz, hcz, (side_gcomp hL hR hc hxy hf hL' hx hy hsub huz).trans ?_⟩
    have harc := arc_c1_iff_c0 hL hR hc hxy hf hL' hx hy hvΓ
      (Or.inl (hv.not_mem (t.vertM_r0 (hv.ne_root hL'))))
    rcases h with rfl | rfl
    · exact side_c1 v
    · rw [side_c0 hvΓ]
      exact harc
  by_cases hs : t.side Γ x y u
  · left
    refine Finset.card_le_card fun z hz => ?_
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨h1, _, h3⟩ := key z hz.1 hz.2
    exact ⟨h1, h3.1 hs⟩
  · right
    refine Finset.card_le_card fun z hz => ?_
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨h1, h2, h3⟩ := key z hz.1 hz.2
    refine ⟨h1, ?_⟩
    have h4 := (inArc_compl hcxy hxy h2).not
    rw [not_not] at h4
    exact h4.1 fun h => hs (h3.2 h)

/-- **Balance.** If `x` and `y` cut the marks of a cycle in a balanced way, every component of the
split at the larger level has at most about three quarters of these marks. -/
theorem npOf_balance (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected) (hxy : x ≠ y)
    (hf : fconnect (⇑(R.double.cone Γ).facePerm⁻¹) x y) (hL' : t.IsLevel Γ') (hx : x ∈ Γ')
    (hy : y ∈ Γ') (hsub : Γ ⊆ Γ') {u : D × Bool}
    (hu : (R.double.split Γ).toHypermap.gcomp x u)
    (h1 : 4 * mass (t.tourL Γ) (t.marks Γ) x y + 2 ≤ 3 * t.npOf Γ x)
    (h2 : 4 * mass (t.tourL Γ) (t.marks Γ) y x + 2 ≤ 3 * t.npOf Γ x) :
    4 * t.npOf Γ' u + 2 ≤ 3 * t.npOf Γ x := by
  rcases npOf_le_mass hL hR hc hxy hf hL' hx hy hsub hu with h | h <;> omega

end Balance

/-! ### The next level -/

section Next

theorem Anc.par {v a : V} (h : t.Anc v a) (hv : v ≠ t.root) : t.Anc (t.par v) a := by
  induction h with
  | refl => exact Anc.step hv Anc.refl
  | step hw _ ih => exact Anc.step hw ih

theorem Anc.dep_le {v a : V} (h : t.Anc v a) : t.dep v ≤ t.dep a := by
  induction h with
  | refl => exact le_rfl
  | step hw _ ih => exact ih.trans (t.dep_par_lt hw).le

/-- Two ancestors of one depth are equal. -/
theorem Anc.eq_of_dep {v v' a : V} (h : t.Anc v a) (h' : t.Anc v' a) (e : t.dep v = t.dep v') :
    v = v' := by
  induction a using (measure t.dep).wf.induction with
  | _ a ih =>
    cases h with
    | refl =>
      cases h' with
      | refl => rfl
      | step hw h' =>
        have := h'.dep_le
        have := t.dep_par_lt hw
        omega
    | step hw h =>
      cases h' with
      | refl =>
        have := h.dep_le
        have := t.dep_par_lt hw
        omega
      | step _ h' => exact ih _ (t.dep_par_lt hw) h h'

/-- The root is an ancestor of every vertex. -/
theorem anc_root (a : V) : t.Anc t.root a := by
  induction a using (measure t.dep).wf.induction with
  | _ a ih =>
    by_cases ha : a = t.root
    · rw [ha]
      exact Anc.refl
    · exact Anc.step ha (ih _ (t.dep_par_lt ha))

/-- A vertex below a vertex without a corner has no corner. -/
theorem NP.of_anc {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) {w a : V} (hw : t.NP Γ w)
    (h : t.Anc w a) : t.NP Γ a := fun z hz hza =>
  hw.not_mem (t.vertM_r0 (hw.ne_root hL)) (hL.rails_of_anc h (hw.ne_root hL) hz hza).1

variable (t) in
open Classical in
/-- The digon corners of the tree edges above `z`, up to the first vertex with a corner in `Γ`. -/
noncomputable def railsUp (Γ : Finset (D × Bool)) (z : D × Bool) : Finset (D × Bool) :=
  Finset.univ.filter fun g => ∃ w, t.NP Γ w ∧ t.Anc w (t.vertM z) ∧ (g = t.r0 w ∨ g = t.c0 w)

theorem mem_railsUp {Γ : Finset (D × Bool)} {z g : D × Bool} :
    g ∈ t.railsUp Γ z ↔ ∃ w, t.NP Γ w ∧ t.Anc w (t.vertM z) ∧ (g = t.r0 w ∨ g = t.c0 w) := by
  simp [railsUp]

variable (t) in
/-- The corners added for the corners `C`: each of them, with the walk up the tree from it. -/
noncomputable def next (Γ C : Finset (D × Bool)) : Finset (D × Bool) :=
  Γ ∪ C.biUnion fun c => insert c (t.railsUp Γ c)

theorem mem_next {Γ C : Finset (D × Bool)} {z : D × Bool} :
    z ∈ t.next Γ C ↔ z ∈ Γ ∨ ∃ c ∈ C, z = c ∨ z ∈ t.railsUp Γ c := by
  simp [next]

theorem subset_next (Γ C : Finset (D × Bool)) : Γ ⊆ t.next Γ C := Finset.subset_union_left

/-- Two darts at a vertex without a corner lie in one component of the split. -/
theorem NP.gcomp {Γ : Finset (D × Bool)} {v : V} (hv : t.NP Γ v) {z z' : D × Bool}
    (hz : t.vertM z = v) (hz' : t.vertM z' = v) : (R.double.split Γ).toHypermap.gcomp z z' := by
  have h : fconnect R.double.rot z z' := (t.vertM_eq_iff _ _).1 (hz.trans hz'.symm)
  rw [R.double.gcomp_split_iff]
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | @tail e c he hec ih =>
    obtain rfl : R.double.rot e = c := hec
    have he' : t.vertM e = v := ((t.vertM_eq_iff _ _).2 he).symm.trans hz
    refine Relation.EqvGen.trans _ _ _ (ih he') (Relation.EqvGen.rel _ _ (Or.inr ⟨?_, rfl⟩))
    exact hv.not_mem he'

/-- A dart at a vertex without a corner lies in one component with the digon corners of its tree
edge. -/
theorem NP.gcomp_rails {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) {v : V} (hv : t.NP Γ v)
    {z : D × Bool} (hz : t.vertM z = v) :
    (R.double.split Γ).toHypermap.gcomp z (t.r0 v) ∧ (R.double.split Γ).toHypermap.gcomp z (t.c0 v) := by
  have hne := hv.ne_root hL
  have h1 := hv.gcomp hz (t.vertM_r0 hne)
  have h2 : (R.double.split Γ).toHypermap.gcomp z (t.c1 v) := hv.gcomp hz (t.vertM_c1 hne)
  exact ⟨h1, connect_trans h2
    ((R.double.gcomp_split_iff Γ _ _).2 (Relation.EqvGen.rel _ _ (Or.inl rfl)))⟩

/-- The corners of a walk up the tree lie in one component with its start. -/
theorem gcomp_of_mem_railsUp {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) {c g : D × Bool}
    (hg : g ∈ t.railsUp Γ c) : (R.double.split Γ).toHypermap.gcomp c g := by
  obtain ⟨w, hw, ha, hgw⟩ := mem_railsUp.1 hg
  clear hg
  suffices h : (R.double.split Γ).toHypermap.gcomp c (t.r0 w) ∧
      (R.double.split Γ).toHypermap.gcomp c (t.c0 w) by
    rcases hgw with rfl | rfl
    · exact h.1
    · exact h.2
  generalize hb : t.vertM c = b at ha
  induction ha generalizing c with
  | refl => exact hw.gcomp_rails hL hb
  | @step a ha' _ ih =>
    have hnp : t.NP Γ a := hw.of_anc hL (Anc.step ha' ‹_›)
    have h1 := (hnp.gcomp_rails hL hb).2
    obtain ⟨h2, h3⟩ := ih (c := t.c0 a) (t.vertM_c0 a)
    exact ⟨connect_trans h1 h2, connect_trans h1 h3⟩

/-- At a vertex with a corner in a level the digon corners of its tree edge are in the level, and they
are in the next level for a vertex without a corner on the walks. -/
theorem IsLevel.next_rails {Γ C : Finset (D × Bool)} (hL : t.IsLevel Γ) {z : D × Bool}
    (hz : z ∈ t.next Γ C) (hr : t.vertM z ≠ t.root) :
    t.r0 (t.vertM z) ∈ t.next Γ C ∧ t.c0 (t.vertM z) ∈ t.next Γ C := by
  by_cases hnp : t.NP Γ (t.vertM z)
  · have key : ∀ v, t.NP Γ v → ∀ c ∈ C, t.Anc v (t.vertM c) →
        t.r0 v ∈ t.next Γ C ∧ t.c0 v ∈ t.next Γ C := fun v hv c hc ha =>
      ⟨mem_next.2 (Or.inr ⟨c, hc, Or.inr (mem_railsUp.2 ⟨_, hv, ha, Or.inl rfl⟩)⟩),
        mem_next.2 (Or.inr ⟨c, hc, Or.inr (mem_railsUp.2 ⟨_, hv, ha, Or.inr rfl⟩)⟩)⟩
    rcases mem_next.1 hz with hzΓ | ⟨c, hc, rfl | hzc⟩
    · exact (hnp z hzΓ rfl).elim
    · exact key _ hnp z hc Anc.refl
    · obtain ⟨w, hw, ha, rfl | rfl⟩ := mem_railsUp.1 hzc
      · rw [t.vertM_r0 (hw.ne_root hL)]
        exact key w hw c hc ha
      · rw [t.vertM_c0] at hnp ⊢
        exact key _ hnp c hc (ha.par (hw.ne_root hL))
  · have h : ∃ g ∈ Γ, t.vertM g = t.vertM z := by
      by_contra hn
      push Not at hn
      exact hnp hn
    obtain ⟨g, hg, hgz⟩ := h
    have := hL.rails g hg (by rwa [hgz])
    rw [hgz] at this
    exact ⟨subset_next Γ C this.1, subset_next Γ C this.2⟩

/-- **The next level.** A set of corners with their walks up the tree is a level, if a digon corner
among them has its partner. -/
theorem IsLevel.next {Γ C : Finset (D × Bool)} (hL : t.IsLevel Γ)
    (hC : ∀ d, (d, false) ∈ C → (R.rev d, false) ∈ t.next Γ C) : t.IsLevel (t.next Γ C) := by
  have hrails : ∀ z ∈ t.next Γ C, t.vertM z ≠ t.root →
      t.r0 (t.vertM z) ∈ t.next Γ C ∧ t.c0 (t.vertM z) ∈ t.next Γ C :=
    fun z hz hr => hL.next_rails hz hr
  obtain ⟨z₀, hz₀, hz₀r⟩ := hL.root_mem
  refine ⟨⟨z₀, subset_next Γ C hz₀, hz₀r⟩, hrails, ?_, ?_⟩
  · intro d hd
    rcases mem_next.1 hd with h | ⟨c, hc, rfl | h⟩
    · exact subset_next Γ C (hL.pairs d h)
    · exact hC d hc
    · obtain ⟨w, hw, ha, h1 | h1⟩ := mem_railsUp.1 h
      · have e : (R.rev d, false) = t.c0 w := by
          have := congrArg Prod.fst h1
          simp only [r0] at this
          simp [c0, this]
        rw [e]
        exact mem_next.2 (Or.inr ⟨c, hc, Or.inr (mem_railsUp.2 ⟨w, hw, ha, Or.inr rfl⟩)⟩)
      · have e : (R.rev d, false) = t.r0 w := by
          have := congrArg Prod.fst h1
          simp only [c0] at this
          simp [r0, this, R.rev_rev]
        rw [e]
        exact mem_next.2 (Or.inr ⟨c, hc, Or.inr (mem_railsUp.2 ⟨w, hw, ha, Or.inl rfl⟩)⟩)
  · have hup : ∀ n, ∀ g ∈ t.next Γ C, t.dep (t.vertM g) = n →
        ∃ h ∈ Γ, connect (R.double.CornerLink (t.next Γ C)) g h := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro g hg hn
        by_cases hnp : t.NP Γ (t.vertM g)
        · have hne := hnp.ne_root hL
          obtain ⟨h1, h2⟩ := hrails g hg hne
          have e1 : R.double.toHypermap.cnode g (t.r0 (t.vertM g)) :=
            (t.vertM_eq_iff _ _).1 (t.vertM_r0 hne).symm
          have e2 : R.double.toHypermap.cface (t.r0 (t.vertM g)) (t.c0 (t.vertM g)) := by
            refine connect_of_rel ?_
            show R.double.facePerm (t.r0 (t.vertM g)) = t.c0 (t.vertM g)
            rfl
          obtain ⟨h, hh, h3⟩ := ih (t.dep (t.vertM (t.c0 (t.vertM g))))
            (by rw [t.vertM_c0, ← hn]; exact t.dep_par_lt hne) _ h2 rfl
          exact ⟨h, hh, connect_trans (connect_of_rel ⟨hg, h1, Or.inl e1⟩)
            (connect_trans (connect_of_rel ⟨h1, h2, Or.inr e2⟩) h3)⟩
        · have h : ∃ g' ∈ Γ, t.vertM g' = t.vertM g := by
            by_contra hn'
            push Not at hn'
            exact hnp hn'
          obtain ⟨h, hh, hhg⟩ := h
          exact ⟨h, hh, connect_of_rel ⟨hg, subset_next Γ C hh,
            Or.inl ((t.vertM_eq_iff _ _).1 hhg.symm)⟩⟩
    intro x hx y hy
    obtain ⟨a, ha, h1⟩ := hup _ x hx rfl
    obtain ⟨b, hb, h2⟩ := hup _ y hy rfl
    have h3 : connect (R.double.CornerLink (t.next Γ C)) a b := by
      refine connect_mono ?_ ((R.double.gcomp_skeleton_iff ha).1 (hL.skel a ha b hb))
      rintro u v ⟨hu, hv, h⟩
      exact ⟨subset_next Γ C hu, subset_next Γ C hv, h⟩
    refine (R.double.gcomp_skeleton_iff hx).2 (connect_trans h1 (connect_trans h3 ?_))
    have h4 := (R.double.gcomp_skeleton_iff hy).2 h2
    have hb' : b ∈ t.next Γ C := subset_next Γ C hb
    exact (R.double.gcomp_skeleton_iff hb').1 ((R.double.skeleton _).glinkC _ _ h4)

open Classical in
/-- The number of vertices without a corner on the way up from a vertex is at most its depth. -/
theorem card_ancNP_le {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) (a : V) :
    (Finset.univ.filter fun w => t.NP Γ w ∧ t.Anc w a).card ≤ t.dep a := by
  have hinj : Set.InjOn t.dep (Finset.univ.filter fun w => t.NP Γ w ∧ t.Anc w a : Finset V) := by
    intro w hw w' hw' e
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    exact hw.2.eq_of_dep hw'.2 e
  rw [← Finset.card_image_of_injOn hinj]
  refine (Finset.card_le_card (t := Finset.Ioc 0 (t.dep a)) fun d hd => ?_).trans (by simp)
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hd
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  have hne := hw.1.ne_root hL
  have := t.dep_par_lt hne
  have := hw.2.dep_le
  simp only [Finset.mem_Ioc]
  omega

/-- A walk up the tree has at most twice the depth of its start in corners. -/
theorem card_railsUp_le {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) (c : D × Bool) :
    (t.railsUp Γ c).card ≤ 2 * t.dep (t.vertM c) := by
  classical
  let W : Finset V := Finset.univ.filter fun w => t.NP Γ w ∧ t.Anc w (t.vertM c)
  have hsub : t.railsUp Γ c ⊆ W.image t.r0 ∪ W.image t.c0 := by
    intro g hg
    obtain ⟨w, hw, ha, h⟩ := mem_railsUp.1 hg
    have hmem : w ∈ W := by simp [W, hw, ha]
    rcases h with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmem)
  have h1 : W.card ≤ t.dep (t.vertM c) := by
    convert card_ancNP_le hL (t.vertM c)
  calc (t.railsUp Γ c).card ≤ (W.image t.r0 ∪ W.image t.c0).card := Finset.card_le_card hsub
    _ ≤ (W.image t.r0).card + (W.image t.c0).card := Finset.card_union_le _ _
    _ ≤ W.card + W.card := add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ 2 * t.dep (t.vertM c) := by omega

end Next

end RootedTree

end RotSystem

end SsspFlow
