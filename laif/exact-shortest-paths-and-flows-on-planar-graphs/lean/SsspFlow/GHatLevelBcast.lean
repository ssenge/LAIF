import SsspFlow.GHatRegion
import SsspFlow.GHatBroadcast

/-!
# Values of the annuli of a level at the corners of the top annulus

Let each annulus of the list of a level carry a value at its target. The component of the E_R and E_C
edges of a copy at a corner `κ0(t)` or `κ1(t)` of the top annulus, with `t` strictly inside the ranges
of an annulus of the list, holds the target of that annulus and no other target. So one broadcast run
gives every such copy the value of its annulus.

* `RData.tgtVal`: the values at the targets of the list of a level, `⊤` elsewhere.
* `RData.tgtVal_tgt`: the value at the target of an annulus is its value.
* `RData.bcast_conds`: the conditions of `RData.levelBcast_local` at the copies of the corners of the
  top annulus inside an annulus of the list.
* `RData.levelBcast_annulus`: one run of the message model gives each of these copies the value of
  its annulus.
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
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- The values `pay q` at the targets of the annuli `q` of the list of a level, `⊤` elsewhere. -/
noncomputable def tgtVal (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    (z : Fin (n * (n * 21))) : ℕ∞ :=
  ⨅ q ∈ r.levelQ ℓ, ⨅ (_ : z = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))), (pay q : ℕ∞)

/-- A finite value of `tgtVal` sits at the target of an annulus of the list. -/
theorem tgtVal_ne_top (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {z : Fin (n * (n * 21))} (h : S.tgtVal hN r ℓ pay z ≠ ⊤) :
    ∃ q ∈ r.levelQ ℓ, z = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))) := by
  by_contra hn
  simp only [not_exists, not_and] at hn
  exact h (iInf_eq_top.2 fun q => iInf_eq_top.2 fun hq => iInf_eq_top.2 fun e => absurd e (hn q hq))

/-- `tgtVal` is `⊤` away from the copies of vertices. -/
theorem tgtVal_other (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {z : Fin (n * (n * 21))} (hz : ∀ u, z ≠ (S.levelPad hN).ι (.inl u)) : S.tgtVal hN r ℓ pay z = ⊤ :=
  iInf_eq_top.2 fun _ => iInf_eq_top.2 fun _ => iInf_eq_top.2 fun e => absurd e (hz _)

variable (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ)
include hΓ

/-- Two annuli of the list of a level whose targets are joined by E_R and E_C edges are equal. -/
theorem levelQ_tgt_eq {q q' : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ}
    (hq : q ∈ r.levelQ ℓ) (hq' : q' ∈ r.levelQ ℓ)
    (h : Relation.ReflTransGen S.ERC (S.vcopy (S.endV (q.1.2.κ1 q.2))) (S.vcopy (S.endV (q'.1.2.κ1 q'.2)))) :
    q = q' := by
  obtain ⟨hA, -, h2, -, h4⟩ := r.levelQ_range ℓ q hq
  obtain ⟨hB, -, h2', -, h4'⟩ := r.levelQ_range ℓ q' hq'
  have e := S.annulus_eq r ℓ hΓ hA hB ⟨_, S.endV_end _⟩ ⟨_, S.endV_end _⟩ (S.pieceOf_endV _)
    (S.pieceOf_endV _) (q.1.2.gcomp_κ1 h2 h4) (q'.1.2.gcomp_κ1 h2' h4') h
  exact Prod.ext e (r.levelQ_uniq ℓ q hq q' hq' e)

/-- **The value at a target.** -/
theorem tgtVal_tgt (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) :
    S.tgtVal hN r ℓ pay ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = pay q := by
  refine le_antisymm (iInf_le_of_le q (iInf_le_of_le hq (iInf_le_of_le rfl le_rfl)))
    (le_iInf fun q' => le_iInf fun hq' => le_iInf fun h => ?_)
  have hu := Sum.inl_injective ((S.levelPad hN).ι_injective h)
  have e := S.levelQ_tgt_eq r ℓ hΓ hq hq' (by rw [hu])
  rw [e]

/-- **The conditions of the broadcast.** For an annulus `q` of the list of a level and an index `t`
strictly inside its ranges, the copy at the corner `κ0(t)` (for `σ = 0`) or `κ1(t)` (for `σ = 1`) of
the top annulus is joined by E_R and E_C edges to the target of `q`, which is the only copy with a
finite value of `tgtVal` joined to it, and that value is `pay q`. -/
theorem bcast_conds (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) (σ : Fin 2) {t : ℕ}
    (ht : if σ = 0 then q.1.2.xa < t ∧ t < q.1.2.xb else q.1.2.ya < t ∧ t < q.1.2.yb) :
    Relation.ReflTransGen S.ERC (S.vcopy (S.endV (q.1.2.κ1 q.2)))
        (S.vcopy (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))) ∧
      (∀ u, S.tgtVal hN r ℓ pay ((S.levelPad hN).ι (.inl u)) ≠ ⊤ →
        Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))) →
        u = S.endV (q.1.2.κ1 q.2)) ∧
      S.tgtVal hN r ℓ pay ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = pay q := by
  obtain ⟨hA, -, h2, -, h4⟩ := r.levelQ_range ℓ q hq
  have hv := S.erc_symm (S.region_erc_mid r ℓ hΓ hA h2 h4 σ ht)
  refine ⟨hv, fun u hu he => ?_, S.tgtVal_tgt hN r ℓ hΓ pay hq⟩
  obtain ⟨q', hq', hu'⟩ := S.tgtVal_ne_top hN r ℓ pay hu
  have hu'' := Sum.inl_injective ((S.levelPad hN).ι_injective hu')
  subst hu''
  have e := S.levelQ_tgt_eq r ℓ hΓ hq' hq (he.trans (S.erc_symm hv))
  rw [e]

omit hΓ in
/-- **Values of the annuli of a level.** One algorithm of the message model on `N`, fixed before the
network, starts from the inputs of a level with token lengths `0` and, at each node, offsets that
agree with `tgtVal` at the identifiers it hosts. After `1 + C log^c n' · (12 D + 16)` rounds, for every
annulus `q` of the list of a level with a value at most `M` and every index `t` strictly inside its
ranges, the copy at the corner `κ0(t)` or `κ1(t)` of the top annulus holds the value of `q`. -/
theorem levelBcast_annulus (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
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
      ∀ pay : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ,
      (∀ q ∈ r.levelQ ℓ, pay q ≤ M) →
      (∀ a, off (hostOf a) a = S.tgtVal hN r ℓ pay a) →
      ∀ q ∈ r.levelQ ℓ, ∀ (σ : Fin 2) (t : ℕ),
        (if σ = 0 then q.1.2.xa < t ∧ t < q.1.2.xb else q.1.2.ya < t ∧ t < q.1.2.yb) →
        out ((S.levelPad hN).ι (.inl (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
            (hostOf ((S.levelPad hN).ι (.inl (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t)))))) =
          pay q := by
  obtain ⟨Cc, c, hB⟩ := levelBcast_local hE K
  refine ⟨Cc, c, fun n D => ?_⟩
  obtain ⟨σT, A, out, hA⟩ := hB n D
  refine ⟨σT, A, out, ?_⟩
  intro N S hN M u₀ off hP hc hS hcut hD hM1 hM Cp g hR hC hg Γ₀ L₀ j k r ℓ hΓ pay hpay hoff q hq σ t ht
  obtain ⟨h1, h2, h3⟩ := S.bcast_conds hN r ℓ hΓ pay hq σ ht
  have hW : ∀ z, S.tgtVal hN r ℓ pay z = ⊤ ∨ S.tgtVal hN r ℓ pay z ≤ (n * (n * 21) + 2) ^ K := by
    intro z
    by_cases hz : S.tgtVal hN r ℓ pay z = ⊤
    · exact .inl hz
    · obtain ⟨q', hq', rfl⟩ := S.tgtVal_ne_top hN r ℓ pay hz
      rw [S.tgtVal_tgt hN r ℓ hΓ pay hq']
      exact .inr (by exact_mod_cast (hpay q' hq').trans hM)
  have hle : ((S.tgtVal hN r ℓ pay ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))) : ℝ≥0∞) ≤ M := by
    rw [h3]
    exact_mod_cast hpay q hq
  rw [hA N S hN M u₀ _ off hP hc hS hcut hD hM1 hM (fun z hz => S.tgtVal_other hN r ℓ pay hz) hW hoff
    _ _ h1 h2 hle, h3]

end RData

end RotSystem

end SsspFlow
