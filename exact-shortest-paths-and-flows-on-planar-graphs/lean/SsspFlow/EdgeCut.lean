import SsspFlow.Incision

/-!
# Cutting one edge of a split map

An `EdgeCut Γ` is a dart `d` of `R` whose digon corners `m = (d, false)` and `r = (rev d, false)` of
`R.double` are not in `Γ`, with the corner `k1` of `Γ` at the vertex of the split `R.double.split Γ`
where `d` starts. Cutting the edge adds `m` and `r` to `Γ`. There are two cases at the head.

* The vertex of the split at the head has no corner of `Γ` (`HeadFree`). Then the boundary
  `k1, a_1, …, a_p` becomes `k1, a_1, …, a_p, m, r` (`EdgeCut.boundary_slit`): the cut is a slit
  into the disk, and the vertex at the head stays one vertex (`EdgeCut.cut_head_free`).
* The vertex at the head has a corner `k2` of `Γ`. Then the boundary `k1, a_1, …, a_p, k2, b_1, …,
  b_q` becomes the two boundaries `k1, a_1, …, a_p, r` (`EdgeCut.boundary_hi`) and
  `m, k2, b_1, …, b_q` (`EdgeCut.boundary_lo`), and the vertex of `k2` splits into the vertices of
  `r` and of `k2` (`EdgeCut.cut_head`).

In both cases the vertex of `k1` splits into the vertices of `m` and of `k1` (`EdgeCut.cut_tail`),
the copy `(d, true)` of the edge starts at the vertex of `k1` (`EdgeCut.cut_rot_k1`) and ends at the
vertex of `r`, the other boundaries stay (`EdgeCut.boundary_of_boundary`), the other vertices stay
(`EdgeCut.fconnect_cut_iff`), and the corners stay connected (`EdgeCut.skeletonConnected`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A vertex of a split without corners of a larger set outside the smaller one is a vertex of the
larger split. -/
theorem fconnect_split_split_iff (R : RotSystem D) {Γ Γ' : Finset D} (h : Γ ⊆ Γ') {z y : D}
    (hz : ∀ w ∈ Γ', w ∉ Γ → ¬ fconnect (R.split Γ).rot z w) :
    fconnect (R.split Γ').rot z y ↔ fconnect (R.split Γ).rot z y := by
  rw [← R.split_split h]
  refine (R.split Γ).fconnect_split_iff fun w hw => ?_
  by_cases hwΓ : w ∈ Γ'
  · refine firstReturn_eq_self_of hwΓ fun c hc h' => ?_
    by_cases hw0 : w ∈ Γ
    · by_cases hc0 : c ∈ Γ
      · exact (R.eq_of_fconnect_split hw0 hc0 h').symm
      · exact absurd (connect_trans hw h') (hz c hc hc0)
    · exact absurd hw (hz w hwΓ hw0)
  · exact (R.split Γ).fixesOff_nodeReturn Γ' w hwΓ

/-- A boundary read from another of its corners. -/
theorem Boundary.append_comm {R : RotSystem D} {Γ : Finset D} {P Q : List D}
    (hb : R.Boundary Γ (P ++ Q)) : R.Boundary Γ (Q ++ P) := by
  have hm : ∀ c, c ∈ Q ++ P → c ∈ P ++ Q := fun c hc =>
    List.mem_append.2 (List.mem_append.1 hc).symm
  refine ⟨List.nodup_append_comm.1 hb.nodup, fun c hc => hb.sub c (hm c hc), fun c hc => ?_⟩
  rw [hb.psi c (hm c hc), ← List.formPerm_rotate (P ++ Q) hb.nodup P.length, List.rotate_append_length_eq]

variable {R : RotSystem D}

variable (R) in
/-- An edge of `R` whose two digon corners in `R.double` are not in `Γ`, with the corner `k1` of `Γ`
at the vertex of the split where the edge starts. -/
structure EdgeCut (Γ : Finset (D × Bool)) where
  /-- The dart. -/
  d : D
  /-- The corner of `Γ` at the vertex of the split where `d` starts. -/
  k1 : D × Bool
  k1_mem : k1 ∈ Γ
  new_m : (d, false) ∉ Γ
  new_r : (R.rev d, false) ∉ Γ
  tail : fconnect (R.double.split Γ).rot (d, false) k1

namespace EdgeCut

variable {Γ : Finset (D × Bool)} (E : R.EdgeCut Γ)

/-- The digon corner at the tail. -/
def m : D × Bool := (E.d, false)

/-- The digon corner at the head. -/
def r : D × Bool := (R.rev E.d, false)

/-- The corners after the cut. -/
def Γ' : Finset (D × Bool) := insert E.m (insert E.r Γ)

/-- The vertex of the split at the head carries no corner of `Γ`. -/
def HeadFree : Prop := ∀ c ∈ Γ, ¬ fconnect (R.double.split Γ).rot E.r c

theorem m_not_mem : E.m ∉ Γ := E.new_m

theorem r_not_mem : E.r ∉ Γ := E.new_r

theorem mem_Γ' {z : D × Bool} : z ∈ E.Γ' ↔ z = E.m ∨ z = E.r ∨ z ∈ Γ := by
  simp only [Γ', Finset.mem_insert]

theorem subset : Γ ⊆ E.Γ' := fun _ hz => E.mem_Γ'.2 (Or.inr (Or.inr hz))

theorem m_mem : E.m ∈ E.Γ' := E.mem_Γ'.2 (Or.inl rfl)

theorem r_mem : E.r ∈ E.Γ' := E.mem_Γ'.2 (Or.inr (Or.inl rfl))

theorem m_ne_r : E.m ≠ E.r := fun h => R.rev_ne E.d (congrArg Prod.fst h).symm

theorem k1_ne_m : E.k1 ≠ E.m := fun h => E.m_not_mem (h ▸ E.k1_mem)

theorem ne_r {c : D × Bool} (hc : c ∈ Γ) : c ≠ E.r := fun h => E.r_not_mem (h ▸ hc)

theorem r_not_k1_of_free (ha : E.HeadFree) : ¬ fconnect (R.double.split Γ).rot E.r E.k1 :=
  ha _ E.k1_mem

theorem r_not_k1_of_k2 {k2 : D × Bool} (hk2 : k2 ∈ Γ) (h2 : fconnect (R.double.split Γ).rot E.r k2)
    (hne : E.k1 ≠ k2) : ¬ fconnect (R.double.split Γ).rot E.r E.k1 := fun h =>
  hne (R.double.eq_of_fconnect_split E.k1_mem hk2 (connect_trans (fconnect_symm h) h2))

/-! ### The first return of the rotation -/

section Node

variable (hr : ¬ fconnect (R.double.split Γ).rot E.r E.k1)
include hr

theorem nodeReturn_k1 : (R.double.split Γ).nodeReturn E.Γ' E.k1 = E.m := by
  refine firstReturn_eq_of_pair (E.subset E.k1_mem) E.m_mem E.k1_ne_m (fconnect_symm E.tail)
    fun z hz h => ?_
  rcases E.mem_Γ'.1 hz with rfl | rfl | hz
  · exact Or.inr rfl
  · exact absurd (fconnect_symm h) hr
  · exact Or.inl (R.double.eq_of_fconnect_split E.k1_mem hz h).symm

theorem nodeReturn_m : (R.double.split Γ).nodeReturn E.Γ' E.m = E.k1 := by
  refine firstReturn_eq_of_pair E.m_mem (E.subset E.k1_mem) E.k1_ne_m.symm E.tail
    fun z hz h => ?_
  have h' := connect_trans (fconnect_symm E.tail) h
  rcases E.mem_Γ'.1 hz with rfl | rfl | hz
  · exact Or.inl rfl
  · exact absurd (fconnect_symm h') hr
  · exact Or.inr (R.double.eq_of_fconnect_split E.k1_mem hz h').symm

omit hr in
/-- A corner of `Γ` away from both ends is fixed. -/
theorem nodeReturn_of_mem {c : D × Bool} (hc : c ∈ Γ) (h1 : c ≠ E.k1)
    (h2 : ¬ fconnect (R.double.split Γ).rot c E.r) :
    (R.double.split Γ).nodeReturn E.Γ' c = c := by
  refine firstReturn_eq_self_of (E.subset hc) fun z hz h => ?_
  rcases E.mem_Γ'.1 hz with rfl | rfl | hz
  · exact absurd (R.double.eq_of_fconnect_split hc E.k1_mem (connect_trans h E.tail)) h1
  · exact absurd h h2
  · exact (R.double.eq_of_fconnect_split hc hz h).symm

end Node

theorem nodeReturn_r_of_free (ha : E.HeadFree) :
    (R.double.split Γ).nodeReturn E.Γ' E.r = E.r := by
  refine firstReturn_eq_self_of E.r_mem fun z hz h => ?_
  rcases E.mem_Γ'.1 hz with rfl | rfl | hz
  · exact absurd (connect_trans h E.tail) (ha _ E.k1_mem)
  · rfl
  · exact absurd h (ha z hz)

section Chord

variable {k2 : D × Bool} (hk2 : k2 ∈ Γ) (h2 : fconnect (R.double.split Γ).rot E.r k2)
  (hne : E.k1 ≠ k2)
include hk2 h2 hne

theorem nodeReturn_k2 : (R.double.split Γ).nodeReturn E.Γ' k2 = E.r := by
  refine firstReturn_eq_of_pair (E.subset hk2) E.r_mem (E.ne_r hk2) (fconnect_symm h2)
    fun z hz h => ?_
  rcases E.mem_Γ'.1 hz with rfl | rfl | hz
  · exact absurd (R.double.eq_of_fconnect_split E.k1_mem hk2
      (connect_trans (fconnect_symm E.tail) (fconnect_symm h))) hne
  · exact Or.inr rfl
  · exact Or.inl (R.double.eq_of_fconnect_split hk2 hz h).symm

theorem nodeReturn_r_of_k2 : (R.double.split Γ).nodeReturn E.Γ' E.r = k2 := by
  refine firstReturn_eq_of_pair E.r_mem (E.subset hk2) (E.ne_r hk2).symm h2 fun z hz h => ?_
  have h' := connect_trans (fconnect_symm h2) h
  rcases E.mem_Γ'.1 hz with rfl | rfl | hz
  · exact absurd (R.double.eq_of_fconnect_split E.k1_mem hk2
      (connect_trans (fconnect_symm E.tail) (fconnect_symm h'))) hne
  · exact Or.inl rfl
  · exact Or.inr (R.double.eq_of_fconnect_split hk2 hz h').symm

end Chord

/-! ### The first return of the faces -/

theorem facePerm_m : (R.double.split Γ).facePerm E.m = E.r := by
  rw [R.double.split_facePerm, Equiv.Perm.mul_apply]
  show R.double.nodeReturn Γ (R.double.facePerm (E.d, false)) = _
  rw [R.double_face_false]
  exact R.double.fixesOff_nodeReturn Γ _ E.r_not_mem

theorem facePerm_r : (R.double.split Γ).facePerm E.r = E.m := by
  rw [R.double.split_facePerm, Equiv.Perm.mul_apply]
  show R.double.nodeReturn Γ (R.double.facePerm (R.rev E.d, false)) = _
  rw [R.double_face_false, R.rev_rev]
  exact R.double.fixesOff_nodeReturn Γ _ E.m_not_mem

theorem faceReturn_m : (R.double.split Γ).faceReturn E.Γ' E.m = E.r :=
  firstReturn_eq_of_trail _ E.m_mem (by rw [E.facePerm_m]; exact Trail.here E.r_mem)

theorem faceReturn_r : (R.double.split Γ).faceReturn E.Γ' E.r = E.m :=
  firstReturn_eq_of_trail _ E.r_mem (by rw [E.facePerm_r]; exact Trail.here E.m_mem)

/-- The face of the split through `m` is the digon. -/
theorem mem_digon_split {z : D × Bool} (h : fconnect (R.double.split Γ).facePerm E.m z) :
    z = E.m ∨ z = E.r := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a c _ hac ih =>
    obtain rfl : (R.double.split Γ).facePerm a = c := hac
    rcases ih with rfl | rfl
    · exact Or.inr E.facePerm_m
    · exact Or.inl E.facePerm_r

theorem faceReturn_of_mem {c : D × Bool} (hc : c ∈ Γ) :
    (R.double.split Γ).faceReturn E.Γ' c = R.double.psi Γ c := by
  rw [← R.double.faceReturn_split Γ]
  refine firstReturn_eq_of_trail _ (E.subset hc) ?_
  refine (firstReturn_trail _ hc).of_subset E.subset fun w hw hw' => ?_
  have hcw : fconnect (R.double.split Γ).facePerm w c :=
    fconnect_symm (connect_trans (fconnect1 _ c) hw)
  rcases E.mem_Γ'.1 hw' with rfl | rfl | hw'
  · rcases E.mem_digon_split hcw with rfl | rfl
    · exact absurd hc E.m_not_mem
    · exact absurd hc E.r_not_mem
  · have h1 : fconnect (R.double.split Γ).facePerm E.m c := by
      refine connect_trans ?_ hcw
      have := fconnect1 (R.double.split Γ).facePerm E.m
      rwa [E.facePerm_m] at this
    rcases E.mem_digon_split h1 with rfl | rfl
    · exact absurd hc E.m_not_mem
    · exact absurd hc E.r_not_mem
  · exact hw'

/-! ### `ψ` after the cut -/

theorem psi_eq : R.double.psi E.Γ' =
    (R.double.split Γ).nodeReturn E.Γ' * (R.double.split Γ).faceReturn E.Γ' :=
  R.double.psi_eq_psi_split E.subset

theorem psi_of_mem {c : D × Bool} (hc : c ∈ Γ) :
    R.double.psi E.Γ' c = (R.double.split Γ).nodeReturn E.Γ' (R.double.psi Γ c) := by
  rw [E.psi_eq, Equiv.Perm.mul_apply, E.faceReturn_of_mem hc]

section Psi

variable (hr : ¬ fconnect (R.double.split Γ).rot E.r E.k1)
include hr

theorem psi_r : R.double.psi E.Γ' E.r = E.k1 := by
  rw [E.psi_eq, Equiv.Perm.mul_apply, E.faceReturn_r, E.nodeReturn_m hr]

omit hr in
theorem psi_of_mem_of_ne {c : D × Bool} (hc : c ∈ Γ) (h1 : R.double.psi Γ c ≠ E.k1)
    (h2 : ¬ fconnect (R.double.split Γ).rot (R.double.psi Γ c) E.r) :
    R.double.psi E.Γ' c = R.double.psi Γ c := by
  rw [E.psi_of_mem hc, E.nodeReturn_of_mem (((R.double.fixesOff_psi Γ).mem_iff c).2 hc) h1 h2]

theorem psi_to_k1 {c : D × Bool} (hc : c ∈ Γ) (h : R.double.psi Γ c = E.k1) :
    R.double.psi E.Γ' c = E.m := by
  rw [E.psi_of_mem hc, h, E.nodeReturn_k1 hr]

end Psi

theorem psi_m_of_free (ha : E.HeadFree) : R.double.psi E.Γ' E.m = E.r := by
  rw [E.psi_eq, Equiv.Perm.mul_apply, E.faceReturn_m, E.nodeReturn_r_of_free ha]

section Chord

variable {k2 : D × Bool} (hk2 : k2 ∈ Γ) (h2 : fconnect (R.double.split Γ).rot E.r k2)
  (hne : E.k1 ≠ k2)
include hk2 h2 hne

theorem psi_m_of_k2 : R.double.psi E.Γ' E.m = k2 := by
  rw [E.psi_eq, Equiv.Perm.mul_apply, E.faceReturn_m, E.nodeReturn_r_of_k2 hk2 h2 hne]

theorem psi_to_k2 {c : D × Bool} (hc : c ∈ Γ) (h : R.double.psi Γ c = k2) :
    R.double.psi E.Γ' c = E.r := by
  rw [E.psi_of_mem hc, h, E.nodeReturn_k2 hk2 h2 hne]

end Chord

/-! ### The boundaries after the cut -/

variable {A B : List (D × Bool)}

/-- **The slit.** If the head carries no corner, the boundary `k1, a_1, …, a_p` becomes
`k1, a_1, …, a_p, m, r`. -/
theorem boundary_slit (ha : E.HeadFree) (hb : R.double.Boundary Γ (E.k1 :: A)) :
    R.double.Boundary E.Γ' ((E.k1 :: A) ++ [E.m, E.r]) := by
  have hr := E.r_not_k1_of_free ha
  have hP : ∀ c ∈ E.k1 :: A, c ∈ Γ := hb.sub
  refine boundary_append ?_ ?_ (by simp) (by simp) (fun i hi => ?_) ?_ (fun j hj => ?_) ?_
  · refine List.nodup_append.2 ⟨hb.nodup, by simp [E.m_ne_r], fun a ha b hb' e => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl
    · exact E.m_not_mem (e ▸ hP a ha)
    · exact E.r_not_mem (e ▸ hP a ha)
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact E.subset (hP c hc)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact E.m_mem
      · exact E.r_mem
  · have h := hb.psi_getElem hi
    rw [E.psi_of_mem_of_ne (hP _ (List.getElem_mem _)) ?_ ?_, h]
    · rw [h, List.getElem_cons_succ]
      exact fun e => (List.nodup_cons.1 hb.nodup).1 (e ▸ List.getElem_mem _)
    · rw [h]
      exact fun hf => ha _ (hP _ (List.getElem_mem _)) (fconnect_symm hf)
  · have h := hb.psi_last (i := (E.k1 :: A).length - 1) (by simp) (by simp)
    rw [E.psi_to_k1 hr (hP _ (List.getElem_mem _)) h]
    rfl
  · obtain rfl : j = 0 := by simp at hj; omega
    exact E.psi_m_of_free ha
  · exact E.psi_r hr

/-- **The chord, the side of `k1`.** If the head carries the corner `k2` and the boundary through
`k1` is `k1, a_1, …, a_p, k2, b_1, …, b_q`, the cut has the boundary `k1, a_1, …, a_p, r`. -/
theorem boundary_hi {k2 : D × Bool} (hk2 : k2 ∈ Γ) (h2 : fconnect (R.double.split Γ).rot E.r k2)
    (hb : R.double.Boundary Γ ((E.k1 :: A) ++ (k2 :: B))) :
    R.double.Boundary E.Γ' ((E.k1 :: A) ++ [E.r]) := by
  obtain ⟨hn1, -, hn3⟩ := List.nodup_append.1 hb.nodup
  have hne : E.k1 ≠ k2 := hn3 _ List.mem_cons_self _ List.mem_cons_self
  have hr := E.r_not_k1_of_k2 hk2 h2 hne
  have hP : ∀ c ∈ E.k1 :: A, c ∈ Γ := fun c hc => hb.sub c (List.mem_append_left _ hc)
  have hk2P : k2 ∉ E.k1 :: A := fun h => hn3 _ h _ List.mem_cons_self rfl
  refine boundary_append ?_ ?_ (by simp) (by simp) (fun i hi => ?_) ?_ (fun j hj => ?_) ?_
  · refine List.nodup_append.2 ⟨hn1, List.nodup_singleton _, fun a ha b hb' e => ?_⟩
    rw [List.mem_singleton] at hb'
    subst hb'
    exact E.r_not_mem (e ▸ hP a ha)
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact E.subset (hP c hc)
    · rw [List.mem_singleton.1 hc]
      exact E.r_mem
  · have h := hb.psi_append_left hi
    rw [E.psi_of_mem_of_ne (hP _ (List.getElem_mem _)) ?_ ?_, h]
    · rw [h, List.getElem_cons_succ]
      exact fun e => (List.nodup_cons.1 hn1).1 (e ▸ List.getElem_mem _)
    · rw [h]
      intro hf
      have e := R.double.eq_of_fconnect_split (hP _ (List.getElem_mem _)) hk2 (connect_trans hf h2)
      exact hk2P (e ▸ List.getElem_mem _)
  · have h := hb.psi_append_mid (by simp) (by simp)
    rw [E.psi_to_k2 hk2 h2 hne (hP _ (List.getElem_mem _)) h]
    rfl
  · simp at hj
  · exact E.psi_r hr

/-- **The chord, the side of `k2`.** If the head carries the corner `k2` and the boundary through
`k1` is `k1, a_1, …, a_p, k2, b_1, …, b_q`, the cut has the boundary `m, k2, b_1, …, b_q`. -/
theorem boundary_lo {k2 : D × Bool} (hk2 : k2 ∈ Γ) (h2 : fconnect (R.double.split Γ).rot E.r k2)
    (hb : R.double.Boundary Γ ((E.k1 :: A) ++ (k2 :: B))) :
    R.double.Boundary E.Γ' ([E.m] ++ (k2 :: B)) := by
  obtain ⟨-, hn2, hn3⟩ := List.nodup_append.1 hb.nodup
  have hne : E.k1 ≠ k2 := hn3 _ List.mem_cons_self _ List.mem_cons_self
  have hr := E.r_not_k1_of_k2 hk2 h2 hne
  have hQ : ∀ c ∈ k2 :: B, c ∈ Γ := fun c hc => hb.sub c (List.mem_append_right _ hc)
  have hk1Q : E.k1 ∉ k2 :: B := fun h => hn3 _ List.mem_cons_self _ h rfl
  refine boundary_append ?_ ?_ (by simp) (by simp) (fun i hi => ?_) ?_ (fun j hj => ?_) ?_
  · refine List.nodup_append.2 ⟨List.nodup_singleton _, hn2, fun a ha b hb' e => ?_⟩
    rw [List.mem_singleton] at ha
    subst ha
    exact E.m_not_mem (e ▸ hQ b hb')
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · rw [List.mem_singleton.1 hc]
      exact E.m_mem
    · exact E.subset (hQ c hc)
  · simp at hi
  · exact E.psi_m_of_k2 hk2 h2 hne
  · have h := hb.psi_append_right hj
    rw [E.psi_of_mem_of_ne (hQ _ (List.getElem_mem _)) ?_ ?_, h]
    · rw [h]
      exact fun e => hk1Q (e ▸ List.getElem_mem _)
    · rw [h, List.getElem_cons_succ]
      intro hf
      have e := R.double.eq_of_fconnect_split (hQ _ (List.mem_cons_of_mem _ (List.getElem_mem _)))
        hk2 (connect_trans hf h2)
      exact (List.nodup_cons.1 hn2).1 (e ▸ List.getElem_mem _)
  · have h := hb.psi_append_last (by simp) (by simp)
    rw [E.psi_to_k1 hr (hQ _ (List.getElem_mem _)) h]
    rfl

/-- A boundary of `Γ` through neither end is a boundary after the cut. -/
theorem boundary_of_boundary {l : List (D × Bool)} (hl : R.double.Boundary Γ l) (h1 : E.k1 ∉ l)
    (h2 : ∀ c ∈ l, ¬ fconnect (R.double.split Γ).rot c E.r) : R.double.Boundary E.Γ' l := by
  refine ⟨hl.nodup, fun c hc => E.subset (hl.sub c hc), fun c hc => ?_⟩
  have hm : R.double.psi Γ c ∈ l := by
    rw [hl.psi c hc]
    exact List.formPerm_apply_mem_of_mem hc
  rw [E.psi_of_mem_of_ne (hl.sub c hc) (fun e => h1 (e ▸ hm)) (h2 _ hm), hl.psi c hc]

/-! ### The vertices after the cut -/

/-- The split after the cut. -/
noncomputable def cut : RotSystem (D × Bool) := R.double.split E.Γ'

theorem cut_eq : E.cut = (R.double.split Γ).split E.Γ' :=
  (R.double.split_split E.subset).symm

theorem cut_rot_apply (x : D × Bool) :
    E.cut.rot x = (R.double.split Γ).rot (((R.double.split Γ).nodeReturn E.Γ')⁻¹ x) := by
  rw [E.cut_eq]
  rfl

/-- A dart lies at the vertex of the cut of the first corner of the cut after it. -/
theorem fconnect_cut_of_trail {z c : D × Bool} (h : Trail (R.double.split Γ).rot E.Γ' z c) :
    fconnect E.cut.rot z c := by
  rw [E.cut_eq]
  exact (h.congr fun w hw => (R.double.split Γ).split_rot_of_not_mem hw).to_fconnect

/-- The copy `(d, true)` of the edge starts at the vertex of `k1`. -/
theorem cut_rot_k1 (hr : ¬ fconnect (R.double.split Γ).rot E.r E.k1) :
    E.cut.rot E.k1 = (E.d, true) := by
  rw [E.cut_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 (E.nodeReturn_m hr).symm,
    R.double.split_rot_of_not_mem E.m_not_mem]
  rfl

/-- **The tail splits in two.** Every dart at the vertex of `k1` lies at the vertex of `m` or at
the vertex of `k1` after the cut. -/
theorem cut_tail (hr : ¬ fconnect (R.double.split Γ).rot E.r E.k1) {z : D × Bool}
    (hz : fconnect (R.double.split Γ).rot z E.k1) :
    fconnect E.cut.rot z E.m ∨ fconnect E.cut.rot z E.k1 := by
  obtain ⟨c, hc⟩ := exists_trail (E.subset E.k1_mem) hz
  have hkc : fconnect (R.double.split Γ).rot E.k1 c :=
    connect_trans (fconnect_symm hz) hc.to_fconnect
  rcases E.mem_Γ'.1 hc.mem with rfl | rfl | h
  · exact Or.inl (E.fconnect_cut_of_trail hc)
  · exact absurd (fconnect_symm hkc) hr
  · obtain rfl := R.double.eq_of_fconnect_split E.k1_mem h hkc
    exact Or.inr (E.fconnect_cut_of_trail hc)

section Chord

variable {k2 : D × Bool} (hk2 : k2 ∈ Γ) (h2 : fconnect (R.double.split Γ).rot E.r k2)
  (hne : E.k1 ≠ k2)
include hk2 h2 hne

/-- The copy `(rev d, true)` of the edge starts at the vertex of `k2`. -/
theorem cut_rot_k2 : E.cut.rot k2 = (R.rev E.d, true) := by
  rw [E.cut_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 (E.nodeReturn_r_of_k2 hk2 h2 hne).symm,
    R.double.split_rot_of_not_mem E.r_not_mem]
  rfl

omit h2 in
/-- **The head splits in two.** Every dart at the vertex of `k2` lies at the vertex of `r` or at
the vertex of `k2` after the cut. -/
theorem cut_head {z : D × Bool} (hz : fconnect (R.double.split Γ).rot z k2) :
    fconnect E.cut.rot z E.r ∨ fconnect E.cut.rot z k2 := by
  obtain ⟨c, hc⟩ := exists_trail (E.subset hk2) hz
  have hkc : fconnect (R.double.split Γ).rot k2 c :=
    connect_trans (fconnect_symm hz) hc.to_fconnect
  rcases E.mem_Γ'.1 hc.mem with rfl | rfl | h
  · exact absurd (R.double.eq_of_fconnect_split E.k1_mem hk2
      (connect_trans (fconnect_symm E.tail) (fconnect_symm hkc))) hne
  · exact Or.inl (E.fconnect_cut_of_trail hc)
  · obtain rfl := R.double.eq_of_fconnect_split hk2 h hkc
    exact Or.inr (E.fconnect_cut_of_trail hc)

end Chord

/-- **The head of a slit stays one vertex.** -/
theorem cut_head_free (ha : E.HeadFree) {z : D × Bool} :
    fconnect E.cut.rot z E.r ↔ fconnect (R.double.split Γ).rot z E.r := by
  constructor
  · intro h
    rw [E.cut_eq] at h
    exact (R.double.split Γ).fconnect_of_fconnect_split h
  · intro hz
    obtain ⟨c, hc⟩ := exists_trail E.r_mem hz
    have hrc : fconnect (R.double.split Γ).rot E.r c :=
      connect_trans (fconnect_symm hz) hc.to_fconnect
    rcases E.mem_Γ'.1 hc.mem with rfl | rfl | h
    · exact absurd (connect_trans hrc E.tail) (ha _ E.k1_mem)
    · exact E.fconnect_cut_of_trail hc
    · exact absurd hrc (ha _ h)

/-- **The other vertices stay.** -/
theorem fconnect_cut_iff {z y : D × Bool} (hm : ¬ fconnect (R.double.split Γ).rot z E.m)
    (hr : ¬ fconnect (R.double.split Γ).rot z E.r) :
    fconnect E.cut.rot z y ↔ fconnect (R.double.split Γ).rot z y :=
  R.double.fconnect_split_split_iff E.subset fun w hw hw0 => by
    rcases E.mem_Γ'.1 hw with rfl | rfl | h
    · exact hm
    · exact hr
    · exact absurd h hw0

/-- Cutting an edge keeps the corners connected. -/
theorem skeletonConnected (hS : R.double.SkeletonConnected Γ) :
    R.double.SkeletonConnected E.Γ' := by
  have hm : connect (R.double.CornerLink E.Γ') E.k1 E.m :=
    connect_of_rel ⟨E.subset E.k1_mem, E.m_mem,
      Or.inl (fconnect_symm (R.double.fconnect_of_fconnect_split E.tail))⟩
  have hk : ∀ x ∈ E.Γ', connect (R.double.CornerLink E.Γ') E.k1 x := by
    intro x hx
    rcases E.mem_Γ'.1 hx with rfl | rfl | hx
    · exact hm
    · exact connect_trans hm (connect_of_rel ⟨E.m_mem, E.r_mem, Or.inr (fconnect1 _ _)⟩)
    · refine connect_sub (fun u v (huv : R.double.CornerLink Γ u v) =>
        connect_of_rel ⟨E.subset huv.1, E.subset huv.2.1, huv.2.2⟩) ?_
      exact (R.double.gcomp_skeleton_iff E.k1_mem).1 (hS _ E.k1_mem _ hx)
  intro x hx y hy
  have h1 := (R.double.gcomp_skeleton_iff (E.subset E.k1_mem)).2 (hk x hx)
  have h2 := (R.double.gcomp_skeleton_iff (E.subset E.k1_mem)).2 (hk y hy)
  exact connect_trans ((R.double.skeleton E.Γ').glinkC _ _ h1) h2

end EdgeCut

end RotSystem

end SsspFlow
