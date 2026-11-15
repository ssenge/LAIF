import SsspFlow.GHatLevelBcast

/-!
# Values of the annuli of a level at all corners of their components

The copies at the corners of the component of an annulus of the list of a level are joined to its
source and its target by E_R and E_C edges, and a copy joined to the source or the target of an annulus
is the copy at a corner of its component. So one broadcast run gives the copy at every corner of the
component of an annulus the value of the annulus, and the copy at a corner holds a value below `M`
only when the corner lies in the component of an annulus of the list, as the value of that annulus.

* `RData.region_of_erc`: a corner whose copy is joined to the source or the target of an annulus of the
  list lies in its component.
* `RData.levelBcast_region`: the values of the annuli of a level at the corners of their components.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ)
include hΓ

/-- **A corner joined to the source or target of an annulus lies in its component.** -/
theorem region_of_erc (τ : Fin 2) {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ}
    (hq : q ∈ r.levelQ ℓ) {z : N.G.Dart × Bool}
    (h : Relation.ReflTransGen S.ERC (S.vcopy (S.endV (qEnd τ q))) (S.vcopy (S.endV z))) :
    (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z := by
  obtain ⟨hA, h1, h2, h3, h4⟩ := r.levelQ_range ℓ q hq
  obtain ⟨p, hp⟩ := (S.tg_comp_iff _ _).1
    ((S.erc_comp_iff ⟨_, S.endV_end (qEnd τ q)⟩ ⟨_, S.endV_end z⟩).1 h)
  rw [S.pieceOf_endV, S.pieceOf_endV, S.vertexEquiv_pieceAt, S.vertexEquiv_pieceAt] at hp
  have hzz : (N.toRot.dual.double.split S.Γ).toHypermap.gcomp (qEnd τ q) z := IsWalk.gcomp_tail hp
  rw [hΓ] at hzz
  exact connect_trans (gcomp_qEnd τ h1 h2 h3 h4)
    (RootedTree.gcomp_split_mono (r.subset_level ℓ hA) hzz)

/-- The conditions of `RData.bcast_eq` at the copy of a corner of the component of an annulus of the
list. -/
theorem bcast_region (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) {z : N.G.Dart × Bool}
    (hz : (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z) :
    Relation.ReflTransGen S.ERC (S.vcopy (S.endV (qEnd τ q))) (S.vcopy (S.endV z)) ∧
      (∀ u, S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl u)) ≠ ⊤ →
        Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy (S.endV z)) → u = S.endV (qEnd τ q)) ∧
      S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))) = pay q := by
  obtain ⟨hA, h1, h2, h3, h4⟩ := r.levelQ_range ℓ q hq
  have hv := S.region_erc r ℓ hΓ hA (gcomp_qEnd τ h1 h2 h3 h4) hz
  refine ⟨hv, fun u hu he => ?_, S.endVal_end hN r ℓ hΓ τ pay hq⟩
  obtain ⟨q', hq', hu'⟩ := S.endVal_ne_top hN r ℓ τ pay hu
  have hu'' := Sum.inl_injective ((S.levelPad hN).ι_injective hu')
  subst hu''
  have e := S.levelQ_end_eq r ℓ hΓ τ τ hq' hq (he.trans (S.erc_symm hv))
  rw [e]

omit hΓ in
/-- **Values of the annuli of a level at the corners of their components.** One algorithm of the
message model on `N`, fixed before the network, starts from the inputs of a level with token lengths
`0` and, at each node, offsets that agree with `endVal τ` at the identifiers it hosts. After
`1 + C log^c n' · (12 D + 16)` rounds, for every annulus `q` of the list of a level with a value at most
`M`, the copy at every corner of the component of `q` holds the value of `q`, and the copy at a corner
holds a value below `M` only when the corner lies in the component of an annulus `q` of the list, and
then it holds the value of `q`. -/
theorem levelBcast_region (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σT : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) σT
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σT → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (M : ℕ)
      (u₀ : S.hRot.Vertex) (off : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K →
      ∀ {Cp : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
        {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
        {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live g Γ₀} {j k : ℕ}
        (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ), S.Γ = Γ₀ ∪ r.steps ℓ →
      ∀ (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ),
      (∀ q ∈ r.levelQ ℓ, pay q ≤ M) →
      (∀ a, off (hostOf a) a = S.endVal hN r ℓ τ pay a) →
      (∀ q ∈ r.levelQ ℓ, ∀ z,
        (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
        out ((S.levelPad hN).ι (.inl (S.endV z)))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
            (hostOf ((S.levelPad hN).ι (.inl (S.endV z))))) = pay q) ∧
      ∀ z, out ((S.levelPad hN).ι (.inl (S.endV z)))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
            (hostOf ((S.levelPad hN).ι (.inl (S.endV z))))) < M →
        ∃ q ∈ r.levelQ ℓ, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z ∧
          out ((S.levelPad hN).ι (.inl (S.endV z)))
            (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
              (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
              (hostOf ((S.levelPad hN).ι (.inl (S.endV z))))) = pay q := by
  obtain ⟨Cc, c, hB⟩ := levelSsspOff_local hE K
  refine ⟨Cc, c, fun n D => ?_⟩
  obtain ⟨σT, A, out, hA⟩ := hB n D
  refine ⟨σT, A, out, ?_⟩
  intro N S hN M u₀ off hP hc hS hcut hD hM1 hM Cp g hR hC hg Γ₀ L₀ j k r ℓ hΓ τ pay hpay hoff
  have hW : ∀ z, S.endVal hN r ℓ τ pay z = ⊤ ∨ S.endVal hN r ℓ τ pay z ≤ (n * (n * 21) + 2) ^ K := by
    intro z
    by_cases hz : S.endVal hN r ℓ τ pay z = ⊤
    · exact .inl hz
    · obtain ⟨q', hq', rfl⟩ := S.endVal_ne_top hN r ℓ τ pay hz
      rw [S.endVal_end hN r ℓ hΓ τ pay hq']
      exact .inr (by exact_mod_cast (hpay q' hq').trans hM)
  have key := fun v => hA N S hN (fun _ => 0) M u₀ (S.endVal hN r ℓ τ pay) off hP hc hS hcut hD
    (fun _ => Nat.zero_le _) hM (fun z hz => S.endVal_other hN r ℓ τ pay hz) hW hoff v
  refine ⟨fun q hq z hz => ?_, fun z hv => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := S.bcast_region hN r ℓ hΓ τ pay hq hz
    have hle : ((S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q))))) : ℝ≥0∞) ≤ M := by
      rw [h3]
      exact_mod_cast hpay q hq
    have e := key (S.endV z)
    rw [S.bcast_eq hN M hM1 _ h1 h2 hle, h3] at e
    exact_mod_cast e
  · have hlt : (out ((S.levelPad hN).ι (.inl (S.endV z)))
        (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
          (1 + Cc * logN (n * (n * 21)) ^ c * (12 * D + 16))
          (hostOf ((S.levelPad hN).ι (.inl (S.endV z))))) : ℝ≥0∞) < M := by
      exact_mod_cast hv
    rw [key (S.endV z)] at hlt
    obtain ⟨q, hq, hc', he⟩ := S.bcast_guard hN r ℓ hΓ τ pay M hM1 hpay (S.endV z) hlt
    refine ⟨q, hq, S.region_of_erc r ℓ hΓ τ hq hc', ?_⟩
    have e := key (S.endV z)
    rw [he] at e
    exact_mod_cast e

end RData

end RotSystem

end SsspFlow
