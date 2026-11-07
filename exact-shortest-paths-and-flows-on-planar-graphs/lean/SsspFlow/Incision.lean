import SsspFlow.CutMap
import SsspFlow.Bags

/-!
# Cutting a disk of a split map along a chord

`RotSystem.double` gives every edge two copies with a digon between them, and the split
`R.double.split Γ` at a set `Γ` of corners has one vertex per sector between two consecutive
corners of `Γ` around a vertex of `R`. For planar connected `R` and a connected nonempty `Γ`, the
corners of `Γ` in one component of the split lie on one face, in the cyclic order of `ψ`
(`split_planar`). `Boundary Γ l` says that the list `l` is such an orbit of `ψ`, in this order;
then a corner of `Γ` lies in the component of the corners of `l` exactly if it lies in `l`
(`Boundary.gcomp_iff`), and `l` is drawn on one face (`Boundary.faceDrawn`).

A `DiskChord` is a walk of `R` along darts `d 0, …, d (n - 1)` from the vertex of the split at a
corner `ka` of `Γ` to the vertex at another corner `kb`. Its edges are not cut by `Γ`, its inner
vertices carry no corner of `Γ` and are pairwise distinct, and its edges are pairwise distinct.
Cutting along it adds the two digon corners `m j = (d j, false)` and `r j = (rev (d j), false)` of
every edge to `Γ`. If the boundary through `ka` and `kb` is `ka, a_1, …, a_p, kb, b_1, …, b_q`, the
cut has the two boundaries

* `ka, a_1, …, a_p, r (n - 1), …, r 0` (`DiskChord.boundary_two`) and
* `m 0, …, m (n - 1), kb, b_1, …, b_q` (`DiskChord.boundary_one`),

and the other boundaries stay (`DiskChord.boundary_of_boundary`). So the disk splits into two disks
along the chord (`DiskChord.gcomp_one_iff`, `DiskChord.gcomp_two_iff`, `DiskChord.not_gcomp`). Every
vertex of the chord splits into one vertex on each side (`DiskChord.cut_inner`,
`DiskChord.cut_start`, `DiskChord.cut_stop`), and the other vertices stay
(`DiskChord.fconnect_cut_iff`). The two copies of the chord are walks of the cut: the copy through
the darts `(d j, false)` on the side of `kb` (`DiskChord.isWalk_one`) and the copy through
`(d j, true)` on the side of `ka` (`DiskChord.isWalk_two`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

/-- A trail to `S` is a trail to every larger set that meets the forward orbit only in `S`. -/
theorem Trail.of_subset {D : Type*} [Fintype D] [DecidableEq D] {f : Equiv.Perm D}
    {S S' : Finset D} {y z : D} (h : Trail f S y z) (hS : S ⊆ S')
    (hS' : ∀ w, fconnect f y w → w ∈ S' → w ∈ S) : Trail f S' y z := by
  induction h with
  | here hy => exact Trail.here (hS hy)
  | @step y z hn _ ih =>
    exact Trail.step (fun hy => hn (hS' y (connect_refl y) hy))
      (ih fun w hw hw' => hS' w (connect_trans (fconnect1 f y) hw) hw')

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- The vertices of a split lie in vertices of the map. -/
theorem fconnect_of_fconnect_split {Γ : Finset D} {x y : D} (h : fconnect (R.split Γ).rot x y) :
    fconnect R.rot x y := by
  refine connect_sub (fun a _ hab => ?_) h
  obtain rfl : (R.split Γ).rot a = _ := hab
  rw [R.split_rot_apply]
  have h1 := fconnect_firstReturn R.rot Γ ((R.nodeReturn Γ)⁻¹ a)
  rw [show firstReturn R.rot Γ ((R.nodeReturn Γ)⁻¹ a) = a from
    Equiv.apply_symm_apply _ a] at h1
  exact connect_trans (fconnect_symm h1) (fconnect1 _ _)

/-- Where the first return of the rotation fixes every dart of a vertex, the split does not change
the vertex. -/
theorem fconnect_split_iff {Γ : Finset D} {x y : D}
    (hfix : ∀ w, fconnect R.rot x w → R.nodeReturn Γ w = w) :
    fconnect (R.split Γ).rot x y ↔ fconnect R.rot x y := by
  refine ⟨R.fconnect_of_fconnect_split, fun h => ?_⟩
  have key : ∀ k, (⇑(R.split Γ).rot)^[k] x = (⇑R.rot)^[k] x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, R.split_rot_apply,
        Equiv.Perm.inv_eq_iff_eq.2 (hfix _ (fconnect_iterate _ x k)).symm]
  obtain ⟨k, rfl⟩ := fconnect_iff_iterate.1 h
  exact fconnect_iff_iterate.2 ⟨k, key k⟩

/-- A vertex of a split has at most one corner of `Γ`. -/
theorem eq_of_fconnect_split {Γ : Finset D} {x y : D} (hx : x ∈ Γ) (hy : y ∈ Γ)
    (h : fconnect (R.split Γ).rot x y) : x = y := by
  have h1 := (fconnect_firstReturn_iff (R.split Γ).rot hx hy).2 h
  rw [show firstReturn (R.split Γ).rot Γ = 1 from R.nodeReturn_split Γ] at h1
  obtain ⟨k, hk⟩ := fconnect_iff_iterate.1 h1
  simpa using hk

/-- The `ψ` of a larger set of corners is its `ψ` in the split. -/
theorem psi_eq_psi_split {Γ Γ' : Finset D} (h : Γ ⊆ Γ') : R.psi Γ' = (R.split Γ).psi Γ' := by
  rw [← R.faceReturn_split Γ', ← R.split_split h, (R.split Γ).faceReturn_split Γ']

/-! ### Boundaries -/

/-- The corners of `Γ` on one face of the split `R.split Γ`, in their cyclic order along the face:
`l` has no repetition, lies in `Γ`, and `ψ` follows it. -/
structure Boundary (Γ : Finset D) (l : List D) : Prop where
  /-- No corner repeats. -/
  nodup : l.Nodup
  /-- The corners lie in `Γ`. -/
  sub : ∀ c ∈ l, c ∈ Γ
  /-- `ψ` follows the list, cyclically. -/
  psi : ∀ c ∈ l, R.psi Γ c = l.formPerm c

variable {R}

section Boundary

variable {Γ : Finset D} {l : List D}

theorem Boundary.psi_getElem (hb : R.Boundary Γ l) {i : ℕ} (hi : i + 1 < l.length) :
    R.psi Γ l[i] = l[i + 1] := by
  rw [hb.psi _ (List.getElem_mem _), List.formPerm_apply_lt_getElem l hb.nodup i hi]

theorem Boundary.psi_last (hb : R.Boundary Γ l) {i : ℕ} (hi : i < l.length)
    (h1 : i + 1 = l.length) : R.psi Γ l[i] = l[0]'(by omega) := by
  rw [hb.psi _ (List.getElem_mem _), List.formPerm_apply_getElem l hb.nodup i hi]
  congr 1
  rw [h1, Nat.mod_self]

theorem boundary_of_steps (hn : l.Nodup) (hs : ∀ c ∈ l, c ∈ Γ)
    (hstep : ∀ i (hi : i + 1 < l.length), R.psi Γ l[i] = l[i + 1])
    (hlast : ∀ i (hi : i < l.length), i + 1 = l.length → R.psi Γ l[i] = l[0]'(by omega)) :
    R.Boundary Γ l := by
  refine ⟨hn, hs, fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  by_cases h : i + 1 < l.length
  · rw [hstep i h, List.formPerm_apply_lt_getElem l hn i h]
  · have h1 : i + 1 = l.length := by omega
    rw [hlast i hi h1, List.formPerm_apply_getElem l hn i hi]
    congr 1
    rw [h1, Nat.mod_self]

/-- A boundary is closed under `ψ`. -/
theorem Boundary.mem_of_fconnect (hb : R.Boundary Γ l) {x y : D} (hx : x ∈ l)
    (h : fconnect (R.psi Γ) x y) : y ∈ l := by
  induction h with
  | refl => exact hx
  | @tail b c _ hbc ih =>
    obtain rfl : R.psi Γ b = c := hbc
    rw [hb.psi b ih]
    exact List.formPerm_apply_mem_of_mem ih

/-- A boundary is one orbit of `ψ`. -/
theorem Boundary.fconnect (hb : R.Boundary Γ l) {x y : D} (hx : x ∈ l) (hy : y ∈ l) :
    fconnect (R.psi Γ) x y := by
  have hc := hb.nodup.isCycleOn_formPerm.2 (show x ∈ {a | a ∈ l} from hx)
    (show y ∈ {a | a ∈ l} from hy)
  obtain ⟨k, hk⟩ := fconnect_iff_iterate.1 ((sameCycle_iff_fconnect _).1 hc)
  have key : ∀ j, (⇑(R.psi Γ))^[j] x = (⇑l.formPerm)^[j] x ∧ (⇑l.formPerm)^[j] x ∈ l := by
    intro j
    induction j with
    | zero => exact ⟨rfl, hx⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
      exact ⟨hb.psi _ ih.2, List.formPerm_apply_mem_of_mem ih.2⟩
  exact fconnect_iff_iterate.2 ⟨k, (key k).1.trans hk⟩

/-- A boundary is drawn on one face of the split. -/
theorem Boundary.faceDrawn (hb : R.Boundary Γ l) (hP : (R.split Γ).Planar) :
    (R.split Γ).FaceDrawn l where
  planar := hP
  tails_nodup := List.Nodup.map_on (fun x hx y hy h => R.eq_of_fconnect_split (hb.sub x hx)
    (hb.sub y hy) (((R.split Γ).tail_eq_iff x y).1 h)) hb.nodup
  order := by
    have hsub : l.toFinset ⊆ Γ := fun c hc => hb.sub c (List.mem_toFinset.1 hc)
    rw [← firstReturn_firstReturn _ hsub]
    show firstReturn ((R.split Γ).faceReturn Γ) l.toFinset = l.formPerm
    rw [R.faceReturn_split]
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ l
    · have hx' := List.mem_toFinset.2 hx
      have hm : R.psi Γ x ∈ l.toFinset := by
        rw [hb.psi x hx]
        exact List.mem_toFinset.2 (List.formPerm_apply_mem_of_mem hx)
      rw [firstReturn_eq_of_trail _ hx' (Trail.here hm), hb.psi x hx]
    · rw [firstReturn_of_not_mem _ (fun h => hx (List.mem_toFinset.1 h)),
        List.formPerm_apply_of_notMem hx]

/-- **Components of the split.** A corner of `Γ` lies in the component of a corner of a boundary
exactly if it lies on the boundary. -/
theorem Boundary.gcomp_iff (hR : R.Planar) (hc : R.Connected) (hΓ : Γ.Nonempty)
    (hS : R.SkeletonConnected Γ) (hb : R.Boundary Γ l) {x y : D} (hx : x ∈ l) (hy : y ∈ Γ) :
    (R.split Γ).toHypermap.gcomp x y ↔ y ∈ l := by
  rw [(R.split_planar hR hc hΓ hS).2.2.2 x (hb.sub x hx) y hy]
  exact ⟨hb.mem_of_fconnect hx, hb.fconnect hx⟩

theorem Boundary.psi_append_left {P Q : List D} (hb : R.Boundary Γ (P ++ Q)) {i : ℕ}
    (hi : i + 1 < P.length) : R.psi Γ P[i] = P[i + 1] := by
  have h := hb.psi_getElem (i := i) (by simp; omega)
  rwa [List.getElem_append_left (by omega), List.getElem_append_left hi] at h

theorem Boundary.psi_append_mid {P Q : List D} (hb : R.Boundary Γ (P ++ Q)) (hP : 0 < P.length)
    (hQ : 0 < Q.length) : R.psi Γ (P[P.length - 1]'(by omega)) = Q[0] := by
  have h := hb.psi_getElem (i := P.length - 1) (by simp; omega)
  rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)] at h
  simp only [show P.length - 1 + 1 - P.length = 0 by omega] at h
  exact h

theorem Boundary.psi_append_right {P Q : List D} (hb : R.Boundary Γ (P ++ Q)) {j : ℕ}
    (hj : j + 1 < Q.length) : R.psi Γ Q[j] = Q[j + 1] := by
  have h := hb.psi_getElem (i := P.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)] at h
  simp only [show P.length + j - P.length = j by omega,
    show P.length + j + 1 - P.length = j + 1 by omega] at h
  exact h

theorem Boundary.psi_append_last {P Q : List D} (hb : R.Boundary Γ (P ++ Q)) (hP : 0 < P.length)
    (hQ : 0 < Q.length) : R.psi Γ (Q[Q.length - 1]'(by omega)) = P[0] := by
  have h := hb.psi_last (i := P.length + Q.length - 1) (by simp; omega) (by simp; omega)
  rw [List.getElem_append_right (by omega), List.getElem_append_left hP] at h
  simp only [show P.length + Q.length - 1 - P.length = Q.length - 1 by omega] at h
  exact h

/-- A boundary from its two parts. -/
theorem boundary_append {P Q : List D} (hn : (P ++ Q).Nodup) (hs : ∀ c ∈ P ++ Q, c ∈ Γ)
    (hP : 0 < P.length) (hQ : 0 < Q.length)
    (h1 : ∀ i (hi : i + 1 < P.length), R.psi Γ P[i] = P[i + 1])
    (h2 : R.psi Γ (P[P.length - 1]'(by omega)) = Q[0])
    (h3 : ∀ j (hj : j + 1 < Q.length), R.psi Γ Q[j] = Q[j + 1])
    (h4 : R.psi Γ (Q[Q.length - 1]'(by omega)) = P[0]) : R.Boundary Γ (P ++ Q) := by
  refine boundary_of_steps hn hs (fun i hi => ?_) (fun i hi hl => ?_)
  · rw [List.length_append] at hi
    by_cases hiP : i + 1 < P.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left hiP]
      exact h1 i hiP
    by_cases hiP' : i + 1 = P.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      simp only [show i = P.length - 1 by omega, show P.length - 1 + 1 - P.length = 0 by omega]
      exact h2
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have := h3 (i - P.length) (by omega)
      simp only [show i + 1 - P.length = i - P.length + 1 by omega]
      exact this
  · rw [List.length_append] at hl hi
    rw [List.getElem_append_right (by omega), List.getElem_append_left hP]
    simp only [show i - P.length = Q.length - 1 by omega]
    exact h4

end Boundary

/-- Darts whose heads are the tails of the next ones form a walk. -/
theorem isWalk_map_range (M : RotSystem D) (f : ℕ → D) (n : ℕ) {u v : M.Vertex}
    (hu : M.tail (f 0) = u) (hv : M.head (f n) = v)
    (h : ∀ j, j < n → M.head (f j) = M.tail (f (j + 1))) :
    M.IsWalk u ((List.range (n + 1)).map f) v := by
  subst hu hv
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact (ih fun j hj => h j (by omega)).append ⟨(h n (by omega)).symm, rfl⟩

/-! ### Chords -/

variable (R) in
/-- A chord of the split `R.double.split Γ`: the darts `d 0, …, d (n - 1)` of a walk of `R` whose
edges are not cut by `Γ`, whose inner vertices carry no corner of `Γ` and are pairwise distinct,
and whose edges are pairwise distinct. It runs from the vertex of the split at the corner `ka` of
`Γ` to the vertex at the corner `kb`. -/
structure DiskChord (Γ : Finset (D × Bool)) where
  /-- The number of edges. -/
  n : ℕ
  /-- The darts. -/
  d : ℕ → D
  /-- The corner of `Γ` at the first vertex. -/
  ka : D × Bool
  /-- The corner of `Γ` at the last vertex. -/
  kb : D × Bool
  pos : 0 < n
  walk : ∀ j, j + 1 < n → R.head (d j) = R.tail (d (j + 1))
  new : ∀ j, j < n → (d j, false) ∉ Γ ∧ (R.rev (d j), false) ∉ Γ
  inner : ∀ j, 0 < j → j < n → ∀ c ∈ Γ, R.tail c.1 ≠ R.tail (d j)
  inj : ∀ i j, 0 < i → i < n → 0 < j → j < n → R.tail (d i) = R.tail (d j) → i = j
  edges : ∀ i j, i < n → j < n → (d i = d j ∨ d i = R.rev (d j)) → i = j
  ka_mem : ka ∈ Γ
  kb_mem : kb ∈ Γ
  ne : ka ≠ kb
  start : fconnect (R.double.split Γ).rot (d 0, false) ka
  stop : fconnect (R.double.split Γ).rot (R.rev (d (n - 1)), false) kb

namespace DiskChord

variable {Γ : Finset (D × Bool)} (K : R.DiskChord Γ)

/-- The digon corner of the `j`-th edge at its tail. -/
def m (j : ℕ) : D × Bool := (K.d j, false)

/-- The digon corner of the `j`-th edge at its head. -/
def r (j : ℕ) : D × Bool := (R.rev (K.d j), false)

/-- The digon corners of the chord. -/
def Δ : Finset (D × Bool) := (Finset.range K.n).image K.m ∪ (Finset.range K.n).image K.r

/-- The corners of the cut along the chord. -/
def Γ' : Finset (D × Bool) := Γ ∪ K.Δ

theorem mem_Δ {z : D × Bool} : z ∈ K.Δ ↔ ∃ j, j < K.n ∧ (z = K.m j ∨ z = K.r j) := by
  simp only [Δ, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨j, hj, Or.inl rfl⟩
    · exact ⟨j, hj, Or.inr rfl⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

theorem subset_Γ' : Γ ⊆ K.Γ' := Finset.subset_union_left

theorem mem_Γ' {z : D × Bool} : z ∈ K.Γ' ↔ z ∈ Γ ∨ z ∈ K.Δ := Finset.mem_union

theorem m_mem {j : ℕ} (hj : j < K.n) : K.m j ∈ K.Γ' :=
  K.mem_Γ'.2 (Or.inr (K.mem_Δ.2 ⟨j, hj, Or.inl rfl⟩))

theorem r_mem {j : ℕ} (hj : j < K.n) : K.r j ∈ K.Γ' :=
  K.mem_Γ'.2 (Or.inr (K.mem_Δ.2 ⟨j, hj, Or.inr rfl⟩))

theorem m_not_mem {j : ℕ} (hj : j < K.n) : K.m j ∉ Γ := (K.new j hj).1

theorem r_not_mem {j : ℕ} (hj : j < K.n) : K.r j ∉ Γ := (K.new j hj).2

theorem m_ne_r {i j : ℕ} (hi : i < K.n) (hj : j < K.n) : K.m i ≠ K.r j := by
  intro h
  have h1 : K.d i = R.rev (K.d j) := congrArg Prod.fst h
  obtain rfl := K.edges i j hi hj (Or.inr h1)
  exact R.rev_ne _ h1.symm

theorem m_inj {i j : ℕ} (hi : i < K.n) (hj : j < K.n) (h : K.m i = K.m j) : i = j :=
  K.edges i j hi hj (Or.inl (congrArg Prod.fst h))

theorem r_inj {i j : ℕ} (hi : i < K.n) (hj : j < K.n) (h : K.r i = K.r j) : i = j := by
  have h1 : R.rev (K.d i) = R.rev (K.d j) := congrArg Prod.fst h
  have h2 : K.d i = K.d j := by rw [← R.rev_rev (K.d i), h1, R.rev_rev]
  exact K.edges i j hi hj (Or.inl h2)

/-- Darts at one vertex of the split lie at one vertex of `R`. -/
theorem tail_fst {x y : D × Bool} (h : fconnect (R.double.split Γ).rot x y) :
    R.tail x.1 = R.tail y.1 :=
  (R.tail_eq_iff _ _).2 (R.fconnect_of_double (R.double.fconnect_of_fconnect_split h))

theorem tail_ka : R.tail K.ka.1 = R.tail (K.d 0) := (tail_fst K.start).symm

theorem tail_kb : R.tail K.kb.1 = R.head (K.d (K.n - 1)) := (tail_fst K.stop).symm

theorem tail_r_succ {j : ℕ} (hj : j + 1 < K.n) : R.tail (K.r j).1 = R.tail (K.d (j + 1)) :=
  K.walk j hj

theorem not_mem_of_tail {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) {z : D × Bool}
    (hz : R.tail z.1 = R.tail (K.d j)) : z ∉ Γ := fun h => K.inner j hj0 hjn z h hz

/-- An inner vertex of the chord is a whole vertex of the split. -/
theorem fconnect_inner {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) {z : D × Bool}
    (hz : R.tail z.1 = R.tail (K.d j)) : fconnect (R.double.split Γ).rot (K.m j) z := by
  have hfix : ∀ w, fconnect R.double.rot (K.m j) w → R.double.nodeReturn Γ w = w := by
    intro w hw
    have hw' : R.tail w.1 = R.tail (K.d j) :=
      ((R.tail_eq_iff _ _).2 (R.fconnect_of_double hw)).symm
    exact R.double.fixesOff_nodeReturn Γ w (K.not_mem_of_tail hj0 hjn hw')
  refine (R.double.fconnect_split_iff hfix).2 ?_
  have h := (R.tail_eq_iff _ _).1 hz.symm
  obtain ⟨z1, z2⟩ := z
  exact R.fconnect_double h false z2

theorem fconnect_m_r {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) :
    fconnect (R.double.split Γ).rot (K.m j) (K.r (j - 1)) :=
  K.fconnect_inner hj0 hjn (by
    have := K.tail_r_succ (j := j - 1) (by omega)
    rwa [show j - 1 + 1 = j by omega] at this)

/-- The digon corners of the chord at a vertex of the split with a corner `c` of `Γ`: the first
one at `ka`, the last one at `kb`, and none elsewhere. -/
theorem delta_at_corner {c z : D × Bool} (hc : c ∈ Γ) (hz : z ∈ K.Δ)
    (h : fconnect (R.double.split Γ).rot c z) :
    (z = K.m 0 ∧ c = K.ka) ∨ (z = K.r (K.n - 1) ∧ c = K.kb) := by
  have hcz := tail_fst h
  obtain ⟨i, hi, rfl | rfl⟩ := K.mem_Δ.1 hz
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Or.inl ⟨rfl, R.double.eq_of_fconnect_split hc K.ka_mem (connect_trans h K.start)⟩
    · exact absurd hcz (K.inner i hi0 hi c hc)
  · by_cases hlast : i + 1 < K.n
    · exact absurd (hcz.trans (K.tail_r_succ hlast)) (K.inner (i + 1) (Nat.succ_pos i) hlast c hc)
    · obtain rfl : i = K.n - 1 := by omega
      exact Or.inr ⟨rfl, R.double.eq_of_fconnect_split hc K.kb_mem (connect_trans h K.stop)⟩

/-- The digon corners of the chord at an inner vertex: those of its two edges. -/
theorem delta_at_inner {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) {z : D × Bool} (hz : z ∈ K.Δ)
    (h : fconnect (R.double.split Γ).rot (K.m j) z) : z = K.m j ∨ z = K.r (j - 1) := by
  have hcz := tail_fst h
  obtain ⟨i, hi, rfl | rfl⟩ := K.mem_Δ.1 hz
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact absurd (K.tail_ka.trans hcz.symm) (K.inner j hj0 hjn K.ka K.ka_mem)
    · exact Or.inl (by rw [K.inj i j hi0 hi hj0 hjn hcz.symm])
  · by_cases hlast : i + 1 < K.n
    · have := K.inj (i + 1) j (Nat.succ_pos i) hlast hj0 hjn
        ((K.tail_r_succ hlast).symm.trans hcz.symm)
      exact Or.inr (by rw [show i = j - 1 by omega])
    · obtain rfl : i = K.n - 1 := by omega
      exact absurd (K.tail_kb.trans hcz.symm) (K.inner j hj0 hjn K.kb K.kb_mem)

theorem ka_ne_m {j : ℕ} (hj : j < K.n) : K.ka ≠ K.m j := fun h => K.m_not_mem hj (h ▸ K.ka_mem)

theorem kb_ne_r {j : ℕ} (hj : j < K.n) : K.kb ≠ K.r j := fun h => K.r_not_mem hj (h ▸ K.kb_mem)

theorem last_lt : K.n - 1 < K.n := by have := K.pos; omega

/-! ### The first return of the rotation of the split to the new corners -/

theorem nodeReturn_ka : (R.double.split Γ).nodeReturn K.Γ' K.ka = K.m 0 := by
  refine firstReturn_eq_of_pair (K.subset_Γ' K.ka_mem) (K.m_mem K.pos) (K.ka_ne_m K.pos)
    (fconnect_symm K.start) fun z hz h => ?_
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact Or.inl (R.double.eq_of_fconnect_split K.ka_mem hz h).symm
  · rcases K.delta_at_corner K.ka_mem hz h with ⟨rfl, -⟩ | ⟨-, e⟩
    · exact Or.inr rfl
    · exact absurd e K.ne

theorem nodeReturn_m_zero : (R.double.split Γ).nodeReturn K.Γ' (K.m 0) = K.ka := by
  refine firstReturn_eq_of_pair (K.m_mem K.pos) (K.subset_Γ' K.ka_mem) (K.ka_ne_m K.pos).symm
    K.start fun z hz h => ?_
  have h' := connect_trans (fconnect_symm K.start) h
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact Or.inr (R.double.eq_of_fconnect_split K.ka_mem hz h').symm
  · rcases K.delta_at_corner K.ka_mem hz h' with ⟨rfl, -⟩ | ⟨-, e⟩
    · exact Or.inl rfl
    · exact absurd e K.ne

theorem nodeReturn_kb : (R.double.split Γ).nodeReturn K.Γ' K.kb = K.r (K.n - 1) := by
  refine firstReturn_eq_of_pair (K.subset_Γ' K.kb_mem) (K.r_mem K.last_lt) (K.kb_ne_r K.last_lt)
    (fconnect_symm K.stop) fun z hz h => ?_
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact Or.inl (R.double.eq_of_fconnect_split K.kb_mem hz h).symm
  · rcases K.delta_at_corner K.kb_mem hz h with ⟨-, e⟩ | ⟨rfl, -⟩
    · exact absurd e.symm K.ne
    · exact Or.inr rfl

theorem nodeReturn_r_last : (R.double.split Γ).nodeReturn K.Γ' (K.r (K.n - 1)) = K.kb := by
  refine firstReturn_eq_of_pair (K.r_mem K.last_lt) (K.subset_Γ' K.kb_mem)
    (K.kb_ne_r K.last_lt).symm K.stop fun z hz h => ?_
  have h' := connect_trans (fconnect_symm K.stop) h
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact Or.inr (R.double.eq_of_fconnect_split K.kb_mem hz h').symm
  · rcases K.delta_at_corner K.kb_mem hz h' with ⟨-, e⟩ | ⟨rfl, -⟩
    · exact absurd e.symm K.ne
    · exact Or.inl rfl

theorem nodeReturn_m_inner {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) :
    (R.double.split Γ).nodeReturn K.Γ' (K.m j) = K.r (j - 1) := by
  refine firstReturn_eq_of_pair (K.m_mem hjn) (K.r_mem (by omega)) (K.m_ne_r hjn (by omega))
    (K.fconnect_m_r hj0 hjn) fun z hz h => ?_
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact absurd hz (K.not_mem_of_tail hj0 hjn (tail_fst h).symm)
  · exact K.delta_at_inner hj0 hjn hz h

theorem nodeReturn_r_inner {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) :
    (R.double.split Γ).nodeReturn K.Γ' (K.r (j - 1)) = K.m j := by
  refine firstReturn_eq_of_pair (K.r_mem (by omega)) (K.m_mem hjn) (K.m_ne_r hjn (by omega)).symm
    (fconnect_symm (K.fconnect_m_r hj0 hjn)) fun z hz h => ?_
  have h' := connect_trans (K.fconnect_m_r hj0 hjn) h
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact absurd hz (K.not_mem_of_tail hj0 hjn (tail_fst h').symm)
  · exact (K.delta_at_inner hj0 hjn hz h').symm

theorem nodeReturn_of_mem {c : D × Bool} (hc : c ∈ Γ) (ha : c ≠ K.ka) (hb : c ≠ K.kb) :
    (R.double.split Γ).nodeReturn K.Γ' c = c := by
  refine firstReturn_eq_self_of (K.subset_Γ' hc) fun z hz h => ?_
  rcases K.mem_Γ'.1 hz with hz | hz
  · exact (R.double.eq_of_fconnect_split hc hz h).symm
  · rcases K.delta_at_corner hc hz h with ⟨-, e⟩ | ⟨-, e⟩
    · exact absurd e ha
    · exact absurd e hb

/-! ### The first return of the faces of the split to the new corners -/

theorem facePerm_m {j : ℕ} (hj : j < K.n) : (R.double.split Γ).facePerm (K.m j) = K.r j := by
  rw [R.double.split_facePerm, Equiv.Perm.mul_apply]
  show R.double.nodeReturn Γ (R.double.facePerm (K.d j, false)) = _
  rw [R.double_face_false]
  exact R.double.fixesOff_nodeReturn Γ _ (K.r_not_mem hj)

theorem facePerm_r {j : ℕ} (hj : j < K.n) : (R.double.split Γ).facePerm (K.r j) = K.m j := by
  rw [R.double.split_facePerm, Equiv.Perm.mul_apply]
  show R.double.nodeReturn Γ (R.double.facePerm (R.rev (K.d j), false)) = _
  rw [R.double_face_false, R.rev_rev]
  exact R.double.fixesOff_nodeReturn Γ _ (K.m_not_mem hj)

theorem faceReturn_m {j : ℕ} (hj : j < K.n) :
    (R.double.split Γ).faceReturn K.Γ' (K.m j) = K.r j :=
  firstReturn_eq_of_trail _ (K.m_mem hj) (by rw [K.facePerm_m hj]; exact Trail.here (K.r_mem hj))

theorem faceReturn_r {j : ℕ} (hj : j < K.n) :
    (R.double.split Γ).faceReturn K.Γ' (K.r j) = K.m j :=
  firstReturn_eq_of_trail _ (K.r_mem hj) (by rw [K.facePerm_r hj]; exact Trail.here (K.m_mem hj))

/-- The face of the split through a digon corner of the chord is the digon. -/
theorem mem_digon_split {j : ℕ} (hj : j < K.n) {z : D × Bool}
    (h : fconnect (R.double.split Γ).facePerm (K.m j) z) : z = K.m j ∨ z = K.r j := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a c _ hac ih =>
    obtain rfl : (R.double.split Γ).facePerm a = c := hac
    rcases ih with rfl | rfl
    · exact Or.inr (K.facePerm_m hj)
    · exact Or.inl (K.facePerm_r hj)

theorem faceReturn_of_mem {c : D × Bool} (hc : c ∈ Γ) :
    (R.double.split Γ).faceReturn K.Γ' c = R.double.psi Γ c := by
  rw [← R.double.faceReturn_split Γ]
  refine firstReturn_eq_of_trail _ (K.subset_Γ' hc) ?_
  refine (firstReturn_trail _ hc).of_subset K.subset_Γ' fun w hw hw' => ?_
  rcases K.mem_Γ'.1 hw' with hw' | hw'
  · exact hw'
  · exfalso
    have hcw : fconnect (R.double.split Γ).facePerm w c :=
      fconnect_symm (connect_trans (fconnect1 _ c) hw)
    obtain ⟨i, hi, rfl | rfl⟩ := K.mem_Δ.1 hw'
    · rcases K.mem_digon_split hi hcw with rfl | rfl
      · exact K.m_not_mem hi hc
      · exact K.r_not_mem hi hc
    · have h1 : fconnect (R.double.split Γ).facePerm (K.m i) c := by
        refine connect_trans ?_ hcw
        have := fconnect1 (R.double.split Γ).facePerm (K.m i)
        rwa [K.facePerm_m hi] at this
      rcases K.mem_digon_split hi h1 with rfl | rfl
      · exact K.m_not_mem hi hc
      · exact K.r_not_mem hi hc

/-! ### `ψ` of the cut -/

theorem psi_eq : R.double.psi K.Γ' =
    (R.double.split Γ).nodeReturn K.Γ' * (R.double.split Γ).faceReturn K.Γ' :=
  R.double.psi_eq_psi_split K.subset_Γ'

theorem psi_m {j : ℕ} (hj : j + 1 < K.n) : R.double.psi K.Γ' (K.m j) = K.m (j + 1) := by
  rw [K.psi_eq, Equiv.Perm.mul_apply, K.faceReturn_m (by omega)]
  have := K.nodeReturn_r_inner (j := j + 1) (Nat.succ_pos j) hj
  rwa [Nat.add_sub_cancel] at this

theorem psi_m_last : R.double.psi K.Γ' (K.m (K.n - 1)) = K.kb := by
  rw [K.psi_eq, Equiv.Perm.mul_apply, K.faceReturn_m K.last_lt, K.nodeReturn_r_last]

theorem psi_r {j : ℕ} (hj : j + 1 < K.n) : R.double.psi K.Γ' (K.r (j + 1)) = K.r j := by
  rw [K.psi_eq, Equiv.Perm.mul_apply, K.faceReturn_r hj]
  have := K.nodeReturn_m_inner (j := j + 1) (Nat.succ_pos j) hj
  rwa [Nat.add_sub_cancel] at this

theorem psi_r_zero : R.double.psi K.Γ' (K.r 0) = K.ka := by
  rw [K.psi_eq, Equiv.Perm.mul_apply, K.faceReturn_r K.pos, K.nodeReturn_m_zero]

theorem psi_of_mem {c : D × Bool} (hc : c ∈ Γ) :
    R.double.psi K.Γ' c = (R.double.split Γ).nodeReturn K.Γ' (R.double.psi Γ c) := by
  rw [K.psi_eq, Equiv.Perm.mul_apply, K.faceReturn_of_mem hc]

theorem psi_of_mem_of_ne {c : D × Bool} (hc : c ∈ Γ) (ha : R.double.psi Γ c ≠ K.ka)
    (hb : R.double.psi Γ c ≠ K.kb) : R.double.psi K.Γ' c = R.double.psi Γ c := by
  rw [K.psi_of_mem hc, K.nodeReturn_of_mem (((R.double.fixesOff_psi Γ).mem_iff c).2 hc) ha hb]

theorem psi_to_ka {c : D × Bool} (hc : c ∈ Γ) (h : R.double.psi Γ c = K.ka) :
    R.double.psi K.Γ' c = K.m 0 := by
  rw [K.psi_of_mem hc, h, K.nodeReturn_ka]

theorem psi_to_kb {c : D × Bool} (hc : c ∈ Γ) (h : R.double.psi Γ c = K.kb) :
    R.double.psi K.Γ' c = K.r (K.n - 1) := by
  rw [K.psi_of_mem hc, h, K.nodeReturn_kb]

/-! ### The two boundaries of the cut -/

/-- The digon corners at the tails of the edges, in the order of the chord. -/
def ms : List (D × Bool) := (List.range K.n).map K.m

/-- The digon corners at the heads of the edges, in the reverse order. -/
def rs : List (D × Bool) := (List.range K.n).map fun k => K.r (K.n - 1 - k)

@[simp] theorem length_ms : K.ms.length = K.n := by simp [ms]

@[simp] theorem length_rs : K.rs.length = K.n := by simp [rs]

theorem getElem_ms {i : ℕ} (hi : i < K.ms.length) : K.ms[i] = K.m i := by simp [ms]

theorem getElem_rs {i : ℕ} (hi : i < K.rs.length) : K.rs[i] = K.r (K.n - 1 - i) := by simp [rs]

theorem mem_ms {z : D × Bool} : z ∈ K.ms ↔ ∃ j, j < K.n ∧ z = K.m j := by
  simp only [ms, List.mem_map, List.mem_range]
  exact ⟨fun ⟨j, hj, e⟩ => ⟨j, hj, e.symm⟩, fun ⟨j, hj, e⟩ => ⟨j, hj, e.symm⟩⟩

theorem mem_rs {z : D × Bool} : z ∈ K.rs ↔ ∃ j, j < K.n ∧ z = K.r j := by
  simp only [rs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨K.n - 1 - k, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨K.n - 1 - j, by omega, by rw [show K.n - 1 - (K.n - 1 - j) = j by omega]⟩

theorem nodup_ms : K.ms.Nodup :=
  List.Nodup.map_on (fun _ hi _ hj h => K.m_inj (List.mem_range.1 hi) (List.mem_range.1 hj) h)
    List.nodup_range

theorem nodup_rs : K.rs.Nodup :=
  List.Nodup.map_on (fun i hi j hj h => by
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    have := K.r_inj (by omega) (by omega) h
    omega) List.nodup_range

theorem not_mem_of_mem_ms {z : D × Bool} (hz : z ∈ K.ms) : z ∉ Γ := by
  obtain ⟨j, hj, rfl⟩ := K.mem_ms.1 hz
  exact K.m_not_mem hj

theorem not_mem_of_mem_rs {z : D × Bool} (hz : z ∈ K.rs) : z ∉ Γ := by
  obtain ⟨j, hj, rfl⟩ := K.mem_rs.1 hz
  exact K.r_not_mem hj

theorem mem_of_mem_ms {z : D × Bool} (hz : z ∈ K.ms) : z ∈ K.Γ' := by
  obtain ⟨j, hj, rfl⟩ := K.mem_ms.1 hz
  exact K.m_mem hj

theorem mem_of_mem_rs {z : D × Bool} (hz : z ∈ K.rs) : z ∈ K.Γ' := by
  obtain ⟨j, hj, rfl⟩ := K.mem_rs.1 hz
  exact K.r_mem hj

variable {A B : List (D × Bool)}

/-- **The side of `ka`.** If the boundary through the two ends is `ka, a_1, …, a_p, kb, b_1, …,
b_q`, the cut has the boundary `ka, a_1, …, a_p, r (n - 1), …, r 0`. -/
theorem boundary_two (hb : R.double.Boundary Γ ((K.ka :: A) ++ (K.kb :: B))) :
    R.double.Boundary K.Γ' ((K.ka :: A) ++ K.rs) := by
  obtain ⟨hn1, hn2, hn3⟩ := List.nodup_append.1 hb.nodup
  have hP : ∀ c ∈ K.ka :: A, c ∈ Γ := fun c hc => hb.sub c (List.mem_append_left _ hc)
  have hkb : K.kb ∉ K.ka :: A := fun h => hn3 _ h _ List.mem_cons_self rfl
  refine boundary_append ?_ ?_ (by simp) (by simpa using K.pos) (fun i hi => ?_) ?_
    (fun j hj => ?_) ?_
  · refine List.nodup_append.2 ⟨hn1, K.nodup_rs, fun a ha b hb' e => ?_⟩
    exact K.not_mem_of_mem_rs hb' (e ▸ hP a ha)
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact K.subset_Γ' (hP c hc)
    · exact K.mem_of_mem_rs hc
  · have h := hb.psi_append_left hi
    rw [K.psi_of_mem_of_ne (hP _ (List.getElem_mem _)) ?_ ?_, h]
    · rw [h, List.getElem_cons_succ]
      exact fun e => (List.nodup_cons.1 hn1).1 (e ▸ List.getElem_mem _)
    · rw [h]
      exact fun e => hkb (e ▸ List.getElem_mem _)
  · have h := hb.psi_append_mid (by simp) (by simp)
    rw [K.psi_to_kb (hP _ (List.getElem_mem _)) h, K.getElem_rs]
    simp
  · rw [K.getElem_rs, K.getElem_rs]
    have e : K.n - 1 - j = K.n - 1 - (j + 1) + 1 := by simp at hj; omega
    rw [e, K.psi_r (by omega)]
  · rw [K.getElem_rs]
    simp only [length_rs, show K.n - 1 - (K.n - 1) = 0 by omega]
    exact K.psi_r_zero

/-- **The side of `kb`.** If the boundary through the two ends is `ka, a_1, …, a_p, kb, b_1, …,
b_q`, the cut has the boundary `m 0, …, m (n - 1), kb, b_1, …, b_q`. -/
theorem boundary_one (hb : R.double.Boundary Γ ((K.ka :: A) ++ (K.kb :: B))) :
    R.double.Boundary K.Γ' (K.ms ++ (K.kb :: B)) := by
  obtain ⟨hn1, hn2, hn3⟩ := List.nodup_append.1 hb.nodup
  have hQ : ∀ c ∈ K.kb :: B, c ∈ Γ := fun c hc => hb.sub c (List.mem_append_right _ hc)
  have hka : K.ka ∉ K.kb :: B := fun h => hn3 _ List.mem_cons_self _ h rfl
  refine boundary_append ?_ ?_ (by simpa using K.pos) (by simp) (fun i hi => ?_) ?_
    (fun j hj => ?_) ?_
  · refine List.nodup_append.2 ⟨K.nodup_ms, hn2, fun a ha b hb' e => ?_⟩
    exact K.not_mem_of_mem_ms ha (e ▸ hQ b hb')
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact K.mem_of_mem_ms hc
    · exact K.subset_Γ' (hQ c hc)
  · rw [K.getElem_ms, K.getElem_ms]
    exact K.psi_m (by simpa using hi)
  · rw [K.getElem_ms]
    simp only [length_ms, List.getElem_cons_zero]
    exact K.psi_m_last
  · have h := hb.psi_append_right hj
    rw [K.psi_of_mem_of_ne (hQ _ (List.getElem_mem _)) ?_ ?_, h]
    · rw [h]
      exact fun e => hka (e ▸ List.getElem_mem _)
    · rw [h, List.getElem_cons_succ]
      exact fun e => (List.nodup_cons.1 hn2).1 (e ▸ List.getElem_mem _)
  · have h := hb.psi_append_last (by simp) (by simp)
    rw [K.psi_to_ka (hQ _ (List.getElem_mem _)) h, K.getElem_ms]

/-- A boundary of `Γ` through neither end of the chord is a boundary of the cut. -/
theorem boundary_of_boundary {l : List (D × Bool)} (hl : R.double.Boundary Γ l)
    (ha : K.ka ∉ l) (hb : K.kb ∉ l) : R.double.Boundary K.Γ' l := by
  refine ⟨hl.nodup, fun c hc => K.subset_Γ' (hl.sub c hc), fun c hc => ?_⟩
  have hm : R.double.psi Γ c ∈ l := by
    rw [hl.psi c hc]
    exact List.formPerm_apply_mem_of_mem hc
  rw [K.psi_of_mem_of_ne (hl.sub c hc) (fun e => ha (e ▸ hm)) (fun e => hb (e ▸ hm)), hl.psi c hc]

/-! ### The vertices of the cut -/

/-- The cut along the chord. -/
noncomputable def cut : RotSystem (D × Bool) := R.double.split K.Γ'

theorem cut_eq : K.cut = (R.double.split Γ).split K.Γ' :=
  (R.double.split_split K.subset_Γ').symm

theorem cut_rot_apply (x : D × Bool) :
    K.cut.rot x = (R.double.split Γ).rot (((R.double.split Γ).nodeReturn K.Γ')⁻¹ x) := by
  rw [K.cut_eq]
  rfl

theorem cut_rot_m {j : ℕ} (hj : j + 1 < K.n) : K.cut.rot (K.m (j + 1)) = (R.rev (K.d j), true) := by
  have h := K.nodeReturn_r_inner (j := j + 1) (Nat.succ_pos j) hj
  rw [Nat.add_sub_cancel] at h
  rw [K.cut_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 h.symm,
    R.double.split_rot_of_not_mem (K.r_not_mem (by omega))]
  rfl

theorem cut_rot_r {j : ℕ} (hj : j + 1 < K.n) : K.cut.rot (K.r j) = (K.d (j + 1), true) := by
  have h := K.nodeReturn_m_inner (j := j + 1) (Nat.succ_pos j) hj
  rw [Nat.add_sub_cancel] at h
  rw [K.cut_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 h.symm,
    R.double.split_rot_of_not_mem (K.m_not_mem hj)]
  rfl

theorem cut_rot_ka : K.cut.rot K.ka = (K.d 0, true) := by
  rw [K.cut_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 K.nodeReturn_m_zero.symm,
    R.double.split_rot_of_not_mem (K.m_not_mem K.pos)]
  rfl

theorem cut_rot_kb : K.cut.rot K.kb = (R.rev (K.d (K.n - 1)), true) := by
  rw [K.cut_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 K.nodeReturn_r_last.symm,
    R.double.split_rot_of_not_mem (K.r_not_mem K.last_lt)]
  rfl

/-- A dart lies at the vertex of the cut of the first corner of the cut after it. -/
theorem fconnect_cut_of_trail {z c : D × Bool} (h : Trail (R.double.split Γ).rot K.Γ' z c) :
    fconnect K.cut.rot z c := by
  rw [K.cut_eq]
  exact (h.congr fun w hw => (R.double.split Γ).split_rot_of_not_mem hw).to_fconnect

/-- **An inner vertex of the chord splits in two.** Every dart at the `j`-th vertex lies at the
vertex of the cut of `m j` or at the vertex of `r (j - 1)`. -/
theorem cut_inner {j : ℕ} (hj0 : 0 < j) (hjn : j < K.n) {z : D × Bool}
    (hz : R.tail z.1 = R.tail (K.d j)) :
    fconnect K.cut.rot z (K.m j) ∨ fconnect K.cut.rot z (K.r (j - 1)) := by
  have hmz := K.fconnect_inner hj0 hjn hz
  obtain ⟨c, hc⟩ := exists_trail (K.m_mem hjn) (fconnect_symm hmz)
  have hmc : fconnect (R.double.split Γ).rot (K.m j) c := connect_trans hmz hc.to_fconnect
  rcases K.mem_Γ'.1 hc.mem with h | h
  · exact absurd h (K.not_mem_of_tail hj0 hjn (tail_fst hmc).symm)
  · rcases K.delta_at_inner hj0 hjn h hmc with rfl | rfl
    · exact Or.inl (K.fconnect_cut_of_trail hc)
    · exact Or.inr (K.fconnect_cut_of_trail hc)

/-- **The first vertex splits in two.** Every dart at the vertex of the split of `ka` lies at the
vertex of the cut of `m 0` or at the vertex of `ka`. -/
theorem cut_start {z : D × Bool} (hz : fconnect (R.double.split Γ).rot z K.ka) :
    fconnect K.cut.rot z (K.m 0) ∨ fconnect K.cut.rot z K.ka := by
  obtain ⟨c, hc⟩ := exists_trail (K.subset_Γ' K.ka_mem) hz
  have hac : fconnect (R.double.split Γ).rot K.ka c :=
    connect_trans (fconnect_symm hz) hc.to_fconnect
  rcases K.mem_Γ'.1 hc.mem with h | h
  · obtain rfl := R.double.eq_of_fconnect_split K.ka_mem h hac
    exact Or.inr (K.fconnect_cut_of_trail hc)
  · rcases K.delta_at_corner K.ka_mem h hac with ⟨rfl, -⟩ | ⟨-, e⟩
    · exact Or.inl (K.fconnect_cut_of_trail hc)
    · exact absurd e K.ne

/-- **The last vertex splits in two.** Every dart at the vertex of the split of `kb` lies at the
vertex of the cut of `r (n - 1)` or at the vertex of `kb`. -/
theorem cut_stop {z : D × Bool} (hz : fconnect (R.double.split Γ).rot z K.kb) :
    fconnect K.cut.rot z (K.r (K.n - 1)) ∨ fconnect K.cut.rot z K.kb := by
  obtain ⟨c, hc⟩ := exists_trail (K.subset_Γ' K.kb_mem) hz
  have hbc : fconnect (R.double.split Γ).rot K.kb c :=
    connect_trans (fconnect_symm hz) hc.to_fconnect
  rcases K.mem_Γ'.1 hc.mem with h | h
  · obtain rfl := R.double.eq_of_fconnect_split K.kb_mem h hbc
    exact Or.inr (K.fconnect_cut_of_trail hc)
  · rcases K.delta_at_corner K.kb_mem h hbc with ⟨-, e⟩ | ⟨rfl, -⟩
    · exact absurd e.symm K.ne
    · exact Or.inl (K.fconnect_cut_of_trail hc)

/-- **The other vertices stay.** A vertex of the split without a digon corner of the chord is a
vertex of the cut. -/
theorem fconnect_cut_iff {z y : D × Bool}
    (hz : ∀ w ∈ K.Δ, ¬ fconnect (R.double.split Γ).rot z w) :
    fconnect K.cut.rot z y ↔ fconnect (R.double.split Γ).rot z y := by
  rw [K.cut_eq]
  refine (R.double.split Γ).fconnect_split_iff fun w hw => ?_
  by_cases hwΓ : w ∈ K.Γ'
  · refine firstReturn_eq_self_of hwΓ fun c hc h => ?_
    rcases K.mem_Γ'.1 hc with hc | hc
    · rcases K.mem_Γ'.1 hwΓ with hw' | hw'
      · exact (R.double.eq_of_fconnect_split hw' hc h).symm
      · exact absurd hw (hz w hw')
    · exact absurd (connect_trans hw h) (hz c hc)
  · exact (R.double.split Γ).fixesOff_nodeReturn K.Γ' w hwΓ

/-! ### The two copies of the chord -/

/-- The copy of the chord through the darts `(d j, false)`. -/
def copyOne : List (D × Bool) := (List.range K.n).map fun j => (K.d j, false)

/-- The copy of the chord through the darts `(d j, true)`. -/
def copyTwo : List (D × Bool) := (List.range K.n).map fun j => (K.d j, true)

/-- The darts `(d j, false)` form a walk of the cut from the vertex of `m 0` to the vertex of
`kb`. -/
theorem isWalk_one : K.cut.IsWalk (K.cut.tail (K.m 0)) K.copyOne (K.cut.tail K.kb) := by
  have e1 : K.n - 1 + 1 = K.n := by have := K.pos; omega
  have h := isWalk_map_range K.cut (fun j => (K.d j, false)) (K.n - 1)
    (u := K.cut.tail (K.m 0)) (v := K.cut.tail K.kb) rfl
    (by
      show K.cut.tail (R.rev (K.d (K.n - 1)), true) = _
      rw [← K.cut_rot_kb, K.cut.tail_rot])
    fun j hj => by
      show K.cut.tail (R.rev (K.d j), true) = K.cut.tail (K.m (j + 1))
      rw [← K.cut_rot_m (j := j) (by omega), K.cut.tail_rot]
  rwa [e1] at h

/-- The darts `(d j, true)` form a walk of the cut from the vertex of `ka` to the vertex of
`r (n - 1)`. -/
theorem isWalk_two : K.cut.IsWalk (K.cut.tail K.ka) K.copyTwo (K.cut.tail (K.r (K.n - 1))) := by
  have e1 : K.n - 1 + 1 = K.n := by have := K.pos; omega
  have h := isWalk_map_range K.cut (fun j => (K.d j, true)) (K.n - 1)
    (u := K.cut.tail K.ka) (v := K.cut.tail (K.r (K.n - 1)))
    (by
      show K.cut.tail (K.d 0, true) = _
      rw [← K.cut_rot_ka, K.cut.tail_rot])
    rfl
    fun j hj => by
      show K.cut.tail (K.r j) = K.cut.tail (K.d (j + 1), true)
      rw [← K.cut_rot_r (j := j) (by omega), K.cut.tail_rot]
  rwa [e1] at h

/-! ### The two sides -/

theorem connect_ka (j : ℕ) (hj : j < K.n) :
    connect (R.double.CornerLink K.Γ') K.ka (K.m j) ∧
      connect (R.double.CornerLink K.Γ') K.ka (K.r j) := by
  induction j with
  | zero =>
    have h0 : connect (R.double.CornerLink K.Γ') K.ka (K.m 0) :=
      connect_of_rel ⟨K.subset_Γ' K.ka_mem, K.m_mem K.pos,
        Or.inl (fconnect_symm (R.double.fconnect_of_fconnect_split K.start))⟩
    exact ⟨h0, connect_trans h0
      (connect_of_rel ⟨K.m_mem K.pos, K.r_mem K.pos, Or.inr (fconnect1 _ _)⟩)⟩
  | succ j ih =>
    have h1 := (ih (by omega)).2
    have h2 : connect (R.double.CornerLink K.Γ') K.ka (K.m (j + 1)) :=
      connect_trans h1 (connect_of_rel ⟨K.r_mem (by omega), K.m_mem hj, Or.inl
        (R.fconnect_double ((R.tail_eq_iff (R.rev (K.d j)) (K.d (j + 1))).1 (K.walk j hj))
          false false)⟩)
    exact ⟨h2, connect_trans h2 (connect_of_rel ⟨K.m_mem hj, K.r_mem hj, Or.inr (fconnect1 _ _)⟩)⟩

/-- Cutting along a chord keeps the corners connected. -/
theorem skeletonConnected (hS : R.double.SkeletonConnected Γ) :
    R.double.SkeletonConnected K.Γ' := by
  have hka : ∀ x ∈ K.Γ', connect (R.double.CornerLink K.Γ') K.ka x := by
    intro x hx
    rcases K.mem_Γ'.1 hx with hx | hx
    · refine connect_sub (fun u v (huv : R.double.CornerLink Γ u v) =>
        connect_of_rel ⟨K.subset_Γ' huv.1, K.subset_Γ' huv.2.1, huv.2.2⟩) ?_
      exact (R.double.gcomp_skeleton_iff K.ka_mem).1 (hS _ K.ka_mem _ hx)
    · obtain ⟨j, hj, rfl | rfl⟩ := K.mem_Δ.1 hx
      · exact (K.connect_ka j hj).1
      · exact (K.connect_ka j hj).2
  intro x hx y hy
  have h1 := (R.double.gcomp_skeleton_iff (K.subset_Γ' K.ka_mem)).2 (hka x hx)
  have h2 := (R.double.gcomp_skeleton_iff (K.subset_Γ' K.ka_mem)).2 (hka y hy)
  exact connect_trans ((R.double.skeleton K.Γ').glinkC _ _ h1) h2

variable (hR : R.Planar) (hc : R.Connected) (hS : R.double.SkeletonConnected Γ)
  (hb : R.double.Boundary Γ ((K.ka :: A) ++ (K.kb :: B)))
include hR hc hS hb

/-- **The two disks.** A corner of the cut lies in the component of `m 0` exactly if it lies on the
boundary `m 0, …, m (n - 1), kb, b_1, …, b_q`. -/
theorem gcomp_one_iff {y : D × Bool} (hy : y ∈ K.Γ') :
    K.cut.toHypermap.gcomp (K.m 0) y ↔ y ∈ K.ms ++ (K.kb :: B) :=
  (K.boundary_one hb).gcomp_iff (R.double_planar hR hc) (R.double_connected hc)
    (⟨K.ka, K.subset_Γ' K.ka_mem⟩ : K.Γ'.Nonempty) (K.skeletonConnected hS)
    (List.mem_append_left _ (K.mem_ms.2 ⟨0, K.pos, rfl⟩)) hy

/-- **The two disks.** A corner of the cut lies in the component of `ka` exactly if it lies on the
boundary `ka, a_1, …, a_p, r (n - 1), …, r 0`. -/
theorem gcomp_two_iff {y : D × Bool} (hy : y ∈ K.Γ') :
    K.cut.toHypermap.gcomp K.ka y ↔ y ∈ (K.ka :: A) ++ K.rs :=
  (K.boundary_two hb).gcomp_iff (R.double_planar hR hc) (R.double_connected hc)
    (⟨K.ka, K.subset_Γ' K.ka_mem⟩ : K.Γ'.Nonempty) (K.skeletonConnected hS)
    (List.mem_append_left _ List.mem_cons_self) hy

/-- The two sides of the chord are different components of the cut. -/
theorem not_gcomp : ¬ K.cut.toHypermap.gcomp (K.m 0) K.ka := by
  rw [K.gcomp_one_iff hR hc hS hb (K.subset_Γ' K.ka_mem)]
  intro h
  obtain ⟨-, -, hn3⟩ := List.nodup_append.1 hb.nodup
  rcases List.mem_append.1 h with h | h
  · exact K.not_mem_of_mem_ms h K.ka_mem
  · exact hn3 _ List.mem_cons_self _ h rfl

end DiskChord

end RotSystem

end SsspFlow
