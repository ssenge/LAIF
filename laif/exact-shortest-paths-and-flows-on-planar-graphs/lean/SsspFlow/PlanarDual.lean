import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import SsspFlow.PlanarMap

/-!
# Circulations on planar maps are differences of face potentials

For a connected planar rotation system, every integer function on the darts that is odd under `rev`
and sums to zero around every vertex is the difference of an integer potential on the faces
(`RotSystem.exists_face_potential`). This is the fact behind the duality of flows and shortest paths
in the dual.

The proof counts dimensions. The potentials on vertices and on faces map to the odd functions on
darts. The images are orthogonal, the kernel consists of the constants, and Euler's formula makes the
map onto. An odd function orthogonal to the vertex potentials then comes from the faces alone.
-/

set_option autoImplicit false

namespace SsspFlow.RotSystem

open FourColor

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- A property of darts that passes along `rev`, `rot` and the face step holds everywhere on a
connected rotation system, once it holds somewhere. -/
theorem forall_of_closed (hc : R.Connected) (P : D → Prop) (hrev : ∀ x, P x → P (R.rev x))
    (hrot : ∀ x, P x → P (R.rot x)) (hface : ∀ x, P x → P (R.rot.symm (R.rev x))) {x₀ : D}
    (h0 : P x₀) (x : D) : P x := by
  have h : R.toHypermap.gcomp x₀ x :=
    connect_of_nComp_eq_one R.toHypermap.glinkC hc (Set.mem_univ x₀) (Set.mem_univ x)
  induction h with
  | refl => exact h0
  | @tail b z _ hbz ih =>
    rcases hbz with h | h | h
    · rw [← h]
      exact hrev _ ih
    · rw [← h]
      exact hrot _ ih
    · rw [← h]
      exact hface _ ih

theorem faceOf_face (x : D) : R.faceOf (R.rot.symm (R.rev x)) = R.faceOf x :=
  Quotient.sound (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl R.facePerm x))

theorem faceOf_rev_rot (x : D) : R.faceOf (R.rev (R.rot x)) = R.faceOf x := by
  have h := R.faceOf_face (R.rev (R.rot x))
  rw [R.rev_rev, Equiv.symm_apply_apply] at h
  exact h.symm

theorem faceOf_rot_symm (y : D) : R.faceOf (R.rot.symm y) = R.faceOf (R.rev y) := by
  have h := R.faceOf_face (R.rev y)
  rwa [R.rev_rev] at h

theorem tail_face (x : D) : R.tail (R.rot.symm (R.rev x)) = R.tail (R.rev x) := R.tail_rot_symm _

section Hodge

variable (q : R.Vertex → ℚ) (ψ : R.Face → ℚ)

/-- The vertex part. -/
private def hV (y : D) : ℚ := q (R.tail y) - q (R.tail (R.rev y))

/-- The face part. -/
private def hF (y : D) : ℚ := ψ (R.faceOf (R.rev y)) - ψ (R.faceOf y)

private theorem hV_rev (y : D) : hV R q (R.rev y) = - hV R q y := by
  simp only [hV, R.rev_rev]
  ring

private theorem hF_rev (y : D) : hF R ψ (R.rev y) = - hF R ψ y := by
  simp only [hF, R.rev_rev]
  ring

/-- The two parts are orthogonal. -/
private theorem orth : ∑ y, hV R q y * hF R ψ y = 0 := by
  have h1 : ∑ y, q (R.tail y) * ψ (R.faceOf (R.rev y)) = ∑ y, q (R.tail y) * ψ (R.faceOf y) := by
    rw [← Equiv.sum_comp R.rot fun y => q (R.tail y) * ψ (R.faceOf (R.rev y))]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [R.tail_rot, R.faceOf_rev_rot]
  have h2 : ∑ y, q (R.tail (R.rev y)) * ψ (R.faceOf (R.rev y)) =
      ∑ y, q (R.tail y) * ψ (R.faceOf y) :=
    Equiv.sum_comp R.revPerm fun y => q (R.tail y) * ψ (R.faceOf y)
  have h3 : ∑ y, q (R.tail (R.rev y)) * ψ (R.faceOf y) = ∑ y, q (R.tail y) * ψ (R.faceOf y) := by
    rw [← Equiv.sum_comp R.facePerm fun y => q (R.tail y) * ψ (R.faceOf y)]
    refine Finset.sum_congr rfl fun z _ => ?_
    show _ = q (R.tail (R.rot.symm (R.rev z))) * ψ (R.faceOf (R.rot.symm (R.rev z)))
    rw [R.tail_face, R.faceOf_face]
  have : ∀ y, hV R q y * hF R ψ y = q (R.tail y) * ψ (R.faceOf (R.rev y)) -
      q (R.tail y) * ψ (R.faceOf y) - q (R.tail (R.rev y)) * ψ (R.faceOf (R.rev y)) +
      q (R.tail (R.rev y)) * ψ (R.faceOf y) := fun y => by
    simp only [hV, hF]
    ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3]
  ring

variable {q ψ}

/-- A vertex potential with no differences is constant. -/
private theorem vertex_const (hc : R.Connected) (h : ∀ y, hV R q y = 0) (u v : R.Vertex) :
    q u = q v := by
  obtain ⟨a, rfl⟩ := R.exists_tail_eq u
  obtain ⟨b, rfl⟩ := R.exists_tail_eq v
  refine R.forall_of_closed hc (fun x => q (R.tail a) = q (R.tail x)) ?_ ?_ ?_ rfl b
  · intro x hx
    have := h x
    simp only [hV] at this
    show q (R.tail a) = _
    linarith
  · intro x hx
    show q (R.tail a) = _
    rwa [R.tail_rot]
  · intro x hx
    show q (R.tail a) = _
    rw [R.tail_face]
    have := h x
    simp only [hV] at this
    linarith

/-- A face potential with no differences is constant. -/
private theorem face_const (hc : R.Connected) (h : ∀ y, hF R ψ y = 0) (f g : R.Face) :
    ψ f = ψ g := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep f
  obtain ⟨b, rfl⟩ := Quotient.exists_rep g
  refine R.forall_of_closed hc (fun x => ψ (R.faceOf a) = ψ (R.faceOf x)) ?_ ?_ ?_ rfl b
  · intro x hx
    have := h x
    simp only [hF] at this
    show ψ (R.faceOf a) = _
    linarith
  · intro x hx
    have h1 := h (R.rot x)
    simp only [hF, R.faceOf_rev_rot] at h1
    show ψ (R.faceOf a) = _
    linarith
  · intro x hx
    show ψ (R.faceOf a) = _
    rwa [R.faceOf_face]

end Hodge

/-- A choice of one dart per edge holds half of the darts. -/
private theorem card_pick (pick : D → Prop) [DecidablePred pick]
    (h : ∀ d, pick (R.rev d) ↔ ¬ pick d) : Fintype.card D = 2 * Fintype.card {d // pick d} := by
  have e : {d // pick d} ≃ {d // ¬ pick d} :=
    Equiv.subtypeEquiv R.revPerm fun d => by simp [h d]
  rw [← Fintype.card_congr (Equiv.sumCompl pick), Fintype.card_sum, ← Fintype.card_congr e]
  omega

/-- **Hodge decomposition.** For a connected planar rotation system, every odd function on the
darts is the sum of a vertex part and a face part. -/
private theorem exists_hodge (hR : R.Planar) (hc : R.Connected) (g : D → ℚ)
    (hrev : ∀ y, g (R.rev y) = - g y) :
    ∃ (q : R.Vertex → ℚ) (ψ : R.Face → ℚ), ∀ y, g y = hV R q y + hF R ψ y := by
  classical
  have : Fintype R.Vertex := Fintype.ofFinite _
  have : Fintype R.Face := Fintype.ofFinite _
  let num : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  let pick : D → Prop := fun d => num d < num (R.rev d)
  have hpick : ∀ d, pick (R.rev d) ↔ ¬ pick d := by
    intro d
    show num (R.rev d) < num (R.rev (R.rev d)) ↔ ¬ num d < num (R.rev d)
    rw [R.rev_rev]
    have hne : num d ≠ num (R.rev d) := fun h => R.rev_ne d (num.injective h).symm
    constructor
    · intro h h'
      exact absurd h' (not_lt.2 h.le)
    · intro h
      exact lt_of_le_of_ne (not_lt.1 h) hne.symm
  let Ψ : ((R.Vertex → ℚ) × (R.Face → ℚ)) →ₗ[ℚ] ({d // pick d} → ℚ) :=
    { toFun := fun p e => hV R p.1 e.1 + hF R p.2 e.1
      map_add' := fun a b => by
        funext e
        simp only [hV, hF, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        ring
      map_smul' := fun c a => by
        funext e
        simp only [hV, hF, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  let cst : (ℚ × ℚ) →ₗ[ℚ] ((R.Vertex → ℚ) × (R.Face → ℚ)) :=
    { toFun := fun a => (fun _ => a.1, fun _ => a.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hext : ∀ p, Ψ p = 0 → ∀ y, hV R p.1 y + hF R p.2 y = 0 := by
    intro p hp y
    by_cases hy : pick y
    · exact congrFun hp ⟨y, hy⟩
    · have := congrFun hp ⟨R.rev y, (hpick y).2 hy⟩
      have h' : hV R p.1 (R.rev y) + hF R p.2 (R.rev y) = 0 := this
      rw [hV_rev, hF_rev] at h'
      linarith
  have hker : LinearMap.ker Ψ ≤ LinearMap.range cst := by
    intro p hp
    have hp0 := hext p (LinearMap.mem_ker.1 hp)
    have hsq : ∑ y, hV R p.1 y ^ 2 = 0 := by
      have : ∀ y, hV R p.1 y ^ 2 = - (hV R p.1 y * hF R p.2 y) := fun y => by
        have := hp0 y
        have h2 : hF R p.2 y = - hV R p.1 y := by linarith
        rw [h2]
        ring
      simp only [this, Finset.sum_neg_distrib, orth, neg_zero]
    have hV0 : ∀ y, hV R p.1 y = 0 := fun y => by
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg (hV R p.1 y)).1 hsq y
        (Finset.mem_univ y)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
    have hF0 : ∀ y, hF R p.2 y = 0 := fun y => by
      have := hp0 y
      rw [hV0 y] at this
      linarith
    obtain ⟨⟨x₀⟩, -⟩ := R.connected_iff.1 hc
    refine ⟨(p.1 (R.tail x₀), p.2 (R.faceOf x₀)), Prod.ext ?_ ?_⟩
    · funext v
      exact vertex_const R hc hV0 _ _
    · funext f
      exact face_const R hc hF0 _ _
  have hdom : Module.finrank ℚ ((R.Vertex → ℚ) × (R.Face → ℚ)) =
      Module.finrank ℚ ({d // pick d} → ℚ) + 2 := by
    have h := R.euler_card hR hc
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, R.card_pick pick hpick] at h
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card]
    omega
  have hkerdim : Module.finrank ℚ (LinearMap.ker Ψ) ≤ 2 := by
    refine (Submodule.finrank_mono hker).trans ((LinearMap.finrank_range_le cst).trans ?_)
    simp
  have hrange : LinearMap.range Ψ = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    have := LinearMap.finrank_range_add_finrank_ker Ψ
    omega
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.1 hrange (fun e => g e.1)
  refine ⟨p.1, p.2, fun y => ?_⟩
  by_cases hy : pick y
  · exact (congrFun hp ⟨y, hy⟩).symm
  · have h' : hV R p.1 (R.rev y) + hF R p.2 (R.rev y) = g (R.rev y) :=
      congrFun hp ⟨R.rev y, (hpick y).2 hy⟩
    rw [hV_rev, hF_rev, hrev] at h'
    linarith

/-- **Circulations on a planar map.** Let `g` be integer valued on the darts of a connected planar
rotation system, odd under `rev`, and orthogonal to all functions that are constant on the vertices.
Then `g` is the difference of an integer potential `π` that is constant on the faces:
`π (rot⁻¹ y) - π y = g y`. Here `rot⁻¹ y` lies in the face of `rev y`. -/
theorem exists_face_potential (hR : R.Planar) (hc : R.Connected) (g : D → ℤ)
    (hrev : ∀ y, g (R.rev y) = - g y)
    (hcons : ∀ q : D → ℚ, (∀ x, q (R.rot x) = q x) → ∑ y, q y * (g y : ℚ) = 0) :
    ∃ π : D → ℤ, (∀ x, π (R.rot.symm (R.rev x)) = π x) ∧ ∀ y, π (R.rot.symm y) - π y = g y := by
  classical
  obtain ⟨q, ψ, h⟩ := R.exists_hodge hR hc (fun y => (g y : ℚ)) (fun y => by
    show ((g (R.rev y) : ℤ) : ℚ) = _
    rw [hrev]
    push_cast
    rfl)
  have hgV : ∑ y, hV R q y * (g y : ℚ) = 0 := by
    have h1 : ∑ y, q (R.tail y) * (g y : ℚ) = 0 :=
      hcons (fun y => q (R.tail y)) fun x => by rw [R.tail_rot]
    have h2 : ∑ y, q (R.tail (R.rev y)) * (g y : ℚ) = - ∑ y, q (R.tail y) * (g y : ℚ) := by
      rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp R.revPerm fun y => - (q (R.tail y) * (g y : ℚ))]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [revPerm_apply, hrev]
      push_cast
      ring
    simp only [hV, sub_mul, Finset.sum_sub_distrib, h1, h2]
    simp
  have hsq : ∑ y, hV R q y ^ 2 = 0 := by
    have : ∀ y, hV R q y ^ 2 = hV R q y * (g y : ℚ) - hV R q y * hF R ψ y := fun y => by
      rw [h y]
      ring
    simp only [this, Finset.sum_sub_distrib, hgV, orth, sub_zero]
  have hV0 : ∀ y, hV R q y = 0 := fun y => by
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg (hV R q y)).1 hsq y
      (Finset.mem_univ y)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
  have hg : ∀ y, (g y : ℚ) = ψ (R.faceOf (R.rev y)) - ψ (R.faceOf y) := fun y => by
    rw [h y, hV0 y, zero_add]
    rfl
  obtain ⟨⟨x₀⟩, -⟩ := R.connected_iff.1 hc
  have hint : ∀ x, ∃ z : ℤ, (z : ℚ) = ψ (R.faceOf x) - ψ (R.faceOf x₀) := by
    refine fun x => R.forall_of_closed hc
      (fun x => ∃ z : ℤ, (z : ℚ) = ψ (R.faceOf x) - ψ (R.faceOf x₀)) ?_ ?_ ?_ (x₀ := x₀)
      ⟨0, by simp⟩ x
    · rintro x ⟨z, hz⟩
      refine ⟨z + g x, ?_⟩
      push_cast
      rw [hz, hg x]
      ring
    · rintro x ⟨z, hz⟩
      refine ⟨z - g (R.rot x), ?_⟩
      push_cast
      rw [hz, hg, R.faceOf_rev_rot]
      ring
    · rintro x ⟨z, hz⟩
      exact ⟨z, by rw [R.faceOf_face]; exact hz⟩
  choose π hπ using hint
  refine ⟨π, fun x => ?_, fun y => ?_⟩
  · have : (π (R.rot.symm (R.rev x)) : ℚ) = π x := by
      rw [hπ, hπ, R.faceOf_face]
    exact_mod_cast this
  · have : ((π (R.rot.symm y) - π y : ℤ) : ℚ) = g y := by
      push_cast
      rw [hπ, hπ, R.faceOf_rot_symm, hg]
      ring
    exact_mod_cast this

end SsspFlow.RotSystem
