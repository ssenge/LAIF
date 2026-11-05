import SsspFlow.Levels

/-!
# The number of edges of a planar graph

A planar rotation system without loops and without parallel edges has at most `4` edges per vertex on any set of
darts closed under reversal (`card_le_of_planar`). The proof restricts the map to the set. Then Euler's formula
gives `|A| / 2 ≤ V + F`, each face has at least three darts unless it is a single isolated edge, and the darts off
the set are isolated edges that do not change the count.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

variable {D : Type*} [Fintype D] [DecidableEq D]

section Reps

variable {f : Equiv.Perm D} {code : D → ℕ}

/-- Representatives of orbits: three darts for each one, except for orbits of two darts. -/
theorem card_reps_le (hinj : Function.Injective code) (Rp S : Finset D)
    (hR : ∀ a ∈ Rp, startOf f code a = a) (hS : ∀ a ∈ Rp, ∀ i, (⇑f)^[i] a ∈ S) (hfix : ∀ a ∈ Rp, f a ≠ a) :
    3 * Rp.card ≤ S.card + (Rp.filter fun a => f (f a) = a).card := by
  classical
  set P := Rp.filter fun a => f (f a) = a with hP
  have hsub : P ×ˢ ({2} : Finset ℕ) ⊆ Rp ×ˢ Finset.range 3 := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    refine Finset.mem_product.2 ⟨(Finset.mem_filter.1 h1).1, ?_⟩
    rw [Finset.mem_singleton.1 h2]
    simp
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_product, Finset.card_product, Finset.card_singleton, Finset.card_range, mul_one] at hcard
  have hinjOn : Set.InjOn (fun q : D × ℕ => (⇑f)^[q.2] q.1)
      (((Rp ×ˢ Finset.range 3) \ (P ×ˢ ({2} : Finset ℕ)) : Finset (D × ℕ)) : Set (D × ℕ)) := by
    rintro ⟨a, i⟩ hq ⟨b, j⟩ hq' he
    obtain ⟨hq1, hq2⟩ := Finset.mem_sdiff.1 hq
    obtain ⟨hq3, hq4⟩ := Finset.mem_sdiff.1 hq'
    obtain ⟨ha, hi⟩ := Finset.mem_product.1 hq1
    obtain ⟨hb, hj⟩ := Finset.mem_product.1 hq3
    have he' : (⇑f)^[i] a = (⇑f)^[j] b := he
    have hab : fconnect f a b := by
      have h1 : fconnect f a ((⇑f)^[i] a) := fconnect_iterate _ _ _
      rw [he'] at h1
      exact connect_trans h1 (fconnect_sym f.injective _ _ (fconnect_iterate _ _ _))
    have heq : a = b := by
      rw [← hR a ha, ← hR b hb]
      exact startOf_congr f hinj hab
    subst heq
    have hij : i = j := by
      have hi' : i < 3 := Finset.mem_range.1 hi
      have hj' : j < 3 := Finset.mem_range.1 hj
      have hf1 := hfix a ha
      have hf2 : f (f a) ≠ f a := fun h => hf1 (f.injective h)
      have hq2' : i = 2 → f (f a) = a → False := fun h2 h =>
        hq2 (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨ha, h⟩, Finset.mem_singleton.2 h2⟩)
      have hq4' : j = 2 → f (f a) = a → False := fun h2 h =>
        hq4 (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨ha, h⟩, Finset.mem_singleton.2 h2⟩)
      interval_cases i <;> interval_cases j <;> first
        | rfl
        | exact (hf1 he'.symm).elim
        | exact (hf1 he').elim
        | exact (hf2 he'.symm).elim
        | exact (hf2 he').elim
        | exact (hq4' rfl he'.symm).elim
        | exact (hq2' rfl he').elim
    subst hij
    rfl
  have hle := Finset.card_le_card_of_injOn (fun q : D × ℕ => (⇑f)^[q.2] q.1) (t := S) (fun q hq => by
    obtain ⟨hq1, -⟩ := Finset.mem_sdiff.1 hq
    exact hS _ (Finset.mem_product.1 hq1).1 _) hinjOn
  omega

/-- Representatives of orbits: two darts for each one. -/
theorem card_reps_two (hinj : Function.Injective code) (Rp S : Finset D)
    (hR : ∀ a ∈ Rp, startOf f code a = a) (hS : ∀ a ∈ Rp, a ∈ S ∧ f a ∈ S) (hfix : ∀ a ∈ Rp, f a ≠ a) :
    2 * Rp.card ≤ S.card := by
  classical
  have hdis : Disjoint Rp (Rp.image f) := by
    rw [Finset.disjoint_left]
    intro a ha hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hm
    have h1 : startOf f code b = startOf f code (f b) := startOf_congr f hinj (fconnect1 f b)
    rw [hR b hb, hR _ ha] at h1
    exact hfix b hb h1.symm
  have h2 : (Rp ∪ Rp.image f).card = Rp.card + Rp.card := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ f.injective]
  have h3 : (Rp ∪ Rp.image f) ⊆ S := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · exact (hS a h).1
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h
      exact (hS b hb).2
  have := Finset.card_le_card h3
  omega

variable (f code)

/-- The representatives of the orbits of a permutation. -/
noncomputable def repsOf : Finset D := by
  classical
  exact Finset.univ.image (startOf f code)

variable {f code}

theorem mem_repsOf {a : D} : a ∈ repsOf f code ↔ ∃ x, startOf f code x = a := by
  classical
  simp [repsOf]

theorem startOf_of_mem (hinj : Function.Injective code) {a : D} (h : a ∈ repsOf f code) :
    startOf f code a = a := by
  obtain ⟨x, rfl⟩ := mem_repsOf.1 h
  exact (startOf_congr f hinj (fconnect_startOf f code x)).symm

theorem orb_eq_card_reps (hinj : Function.Injective code) : orb f = (repsOf f code).card := by
  classical
  have h1 : fcard f Set.univ = (startOf f code '' Set.univ).ncard := by
    refine ncard_image_eq_of_ker _ _ fun x _ y _ => ?_
    rw [comp_eq_iff (fconnect_sym f.injective)]
    refine ⟨fun h => startOf_congr f hinj h, fun h => ?_⟩
    have h2 := fconnect_startOf f code x
    rw [h] at h2
    exact connect_trans h2 (fconnect_sym f.injective _ _ (fconnect_startOf f code y))
  have h2 : startOf f code '' Set.univ = (repsOf f code : Set D) := by
    ext a
    simp [mem_repsOf]
  rw [orb, h1, h2, Set.ncard_coe_finset]

end Reps

namespace RotSystem

variable {R : RotSystem D}

section Bound

variable {V : Type*} [DecidableEq V] {τ : D → V} (hτ : ∀ x y, τ x = τ y ↔ fconnect R.rot x y)
  (hloop : ∀ x, τ (R.rev x) ≠ τ x)
  (hsimple : ∀ x y, τ x = τ y → τ (R.rev x) = τ (R.rev y) → x = y)
  {A : Finset D} (hA : R.RevClosed A)

include hτ in
theorem tau_firstReturn (S : Finset D) (x : D) : τ (firstReturn R.rot S x) = τ x :=
  ((hτ _ _).2 (fconnect_firstReturn R.rot S x)).symm

theorem fixesOff_restrict : FixesOff (R.restrict A).rot A := fun _ hx => restrict_rot_of_not_mem hx

theorem face_restrict_apply_rot (x : D) :
    (R.restrict A).rot ((R.restrict A).facePerm x) = R.rev x := by
  show (R.restrict A).rot ((R.restrict A).rot.symm (R.rev x)) = _
  exact (R.restrict A).rot.apply_symm_apply _

include hτ hloop in
theorem face_restrict_ne (x : D) : (R.restrict A).facePerm x ≠ x := by
  intro h
  have h1 := face_restrict_apply_rot (R := R) (A := A) x
  rw [h] at h1
  have h2 : τ (firstReturn R.rot A x) = τ x := tau_firstReturn hτ A x
  have h3 : (R.restrict A).rot x = firstReturn R.rot A x := rfl
  rw [h3] at h1
  rw [h1] at h2
  exact hloop x h2

include hA in
theorem face_mem_iff (x : D) : (R.restrict A).facePerm x ∈ A ↔ x ∈ A := by
  have h1 := (fixesOff_restrict (R := R) (A := A)).inv.mem_iff (R.rev x)
  have h2 : ((R.restrict A).rot)⁻¹ (R.rev x) = (R.restrict A).facePerm x := rfl
  rw [h2] at h1
  rw [h1]
  refine ⟨fun h => ?_, hA x⟩
  have h3 := hA _ h
  rwa [R.rev_rev] at h3

include hτ hsimple in
/-- A face with two darts of a restriction is an isolated edge. -/
theorem rot_fixed_of_digon {a : D} (h2 : (R.restrict A).facePerm ((R.restrict A).facePerm a) = a) :
    (R.restrict A).rot a = a := by
  set y := (R.restrict A).facePerm a with hy
  have h3 : (R.restrict A).rot y = R.rev a := face_restrict_apply_rot a
  have h4 : (R.restrict A).rot a = R.rev y := by
    have h5 := face_restrict_apply_rot (R := R) (A := A) y
    rwa [h2] at h5
  have h6 : τ y = τ (R.rev a) := by
    rw [← h3]
    exact (tau_firstReturn hτ A y).symm
  have h7 : τ (R.rev y) = τ a := by
    rw [← h4]
    exact tau_firstReturn hτ A a
  have h8 : y = R.rev a := hsimple _ _ h6 (by rw [R.rev_rev]; exact h7)
  rw [h4, h8, R.rev_rev]

/-- Two darts of a component of isolated edges. -/
theorem gcomp_isolated {x y : D} (hx : x ∉ A) (hx' : R.rev x ∉ A)
    (h : (R.restrict A).toHypermap.gcomp x y) : y = x ∨ y = R.rev x := by
  have hm : y ∈ ({x, R.rev x} : Set D) := by
    refine mem_of_gcomp (R := R.restrict A) ?_ ?_ h (Set.mem_insert _ _)
    · rintro z (rfl | rfl)
      · exact Or.inr rfl
      · left
        exact R.rev_rev _
    · rintro z (rfl | rfl)
      · left
        exact restrict_rot_of_not_mem hx
      · right
        exact restrict_rot_of_not_mem hx'
  exact hm

include hτ hloop hsimple hA in
/-- **A planar simple map has at most four edges per vertex**, on any set of darts closed under reversal. -/
theorem card_le_of_planar (hR : R.Planar) : A.card ≤ 8 * (A.image τ).card := by
  classical
  set R' := R.restrict A with hR'
  have hE := R'.euler_components (planar_restrict hR A)
  have hEd := R'.card_eq
  set T := Aᶜ with hT
  have hTc : T.card + A.card = Fintype.card D := by
    rw [hT, Finset.card_compl, Nat.sub_add_cancel (Finset.card_le_univ _)]
  have hTrev : ∀ x ∈ T, R.rev x ∈ T := fun x hx => by
    rw [hT, Finset.mem_compl] at hx ⊢
    intro h
    have h3 := hA _ h
    rw [R.rev_rev] at h3
    exact hx h3
  -- vertices
  have hV : R'.numVertices = (A.image τ).card + T.card := by
    rw [numVertices_eq_orb, orb_eq_add_card (fixesOff_restrict (R := R) (A := A))]
    congr 1
    have h1 : fcard R'.rot (A : Set D) = (τ '' (A : Set D)).ncard := by
      refine ncard_image_eq_of_ker _ _ fun x hx y hy => ?_
      rw [comp_eq_iff (fconnect_sym R'.rot.injective), hτ]
      exact fconnect_firstReturn_iff R.rot hx hy
    rw [h1, ← Finset.coe_image, Set.ncard_coe_finset]
  -- components
  have hC : T.card ≤ 2 * R'.numComponents := by
    have h1 : T.card ≤ 2 * (T.image (comp R'.toHypermap.glink)).card := by
      refine Finset.card_le_mul_card_image T 2 fun s hs => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
      have hxA : x ∉ A := Finset.mem_compl.1 hx
      have hxA' : R.rev x ∉ A := Finset.mem_compl.1 (hTrev x hx)
      refine (Finset.card_le_card (t := {x, R.rev x}) fun y hy => ?_).trans Finset.card_le_two
      have hy' := (Finset.mem_filter.1 hy).2
      have hsym : ConnectSym R'.toHypermap.glink := R'.toHypermap.glinkC
      have hg : R'.toHypermap.gcomp x y := (comp_eq_iff hsym).1 hy'.symm
      rcases gcomp_isolated hxA hxA' hg with rfl | rfl <;> simp
    have h2 : (T.image (comp R'.toHypermap.glink)).card ≤ R'.numComponents := by
      unfold numComponents nComp
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro s hs
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs)
      exact ⟨x, Set.mem_univ _, rfl⟩
    omega
  -- faces
  obtain ⟨e⟩ : Nonempty (D ≃ Fin (Fintype.card D)) := ⟨Fintype.equivFin D⟩
  set code : D → ℕ := fun x => (e x : ℕ) with hcode
  have hinj : Function.Injective code := fun x y h => e.injective (Fin.ext h)
  set f := R'.facePerm with hf
  set Rp := repsOf f code with hRp
  have hF : R'.numFaces = (Rp.filter (· ∈ A)).card + (Rp.filter (· ∉ A)).card := by
    rw [numFaces_eq_orb, orb_eq_card_reps hinj, Finset.card_filter_add_card_filter_not]
  have hfA : ∀ x i, x ∈ A → (⇑f)^[i] x ∈ A := by
    intro x i hx
    induction i with
    | zero => exact hx
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact (face_mem_iff hA _).2 ih
  have hrA := card_reps_le hinj (Rp.filter (· ∈ A)) A
    (fun a ha => startOf_of_mem hinj (Finset.mem_filter.1 ha).1)
    (fun a ha i => hfA a i (Finset.mem_filter.1 ha).2)
    (fun a _ => face_restrict_ne hτ hloop a)
  have hrT := card_reps_two hinj (Rp.filter (· ∉ A)) T
    (fun a ha => startOf_of_mem hinj (Finset.mem_filter.1 ha).1)
    (fun a ha => by
      have h1 := (Finset.mem_filter.1 ha).2
      exact ⟨Finset.mem_compl.2 h1, Finset.mem_compl.2 (mt (face_mem_iff hA a).1 h1)⟩)
    (fun a _ => face_restrict_ne hτ hloop a)
  -- digons
  have hdig : (((Rp.filter (· ∈ A)).filter fun a => f (f a) = a)).card ≤ (A.image τ).card := by
    refine Finset.card_le_card_of_injOn τ ?_ ?_
    · intro a ha
      obtain ⟨h1, -⟩ := Finset.mem_filter.1 ha
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.1 h1).2)
    · intro a ha b hb hab
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      obtain ⟨h3, h4⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      have ha' : R'.rot a = a := rot_fixed_of_digon hτ hsimple h2
      have hc : fconnect R.rot a b := (hτ _ _).1 hab
      have hc' : fconnect R'.rot a b :=
        (fconnect_firstReturn_iff R.rot (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h3).2).2 hc
      exact (eq_of_fconnect_of_fixed ha' hc').symm
  omega

end Bound

end RotSystem

end SsspFlow
