import SsspFlow.GHatRegion
import SsspFlow.GHatBroadcast

/-!
# Values of the annuli of a level at the corners of the top annulus

Let each annulus of the list of a level carry a value at its source or at its target. The component
of the E_R and E_C edges of a copy at a corner `κ0(t)` or `κ1(t)` of the top annulus, with `t` strictly
inside the ranges of an annulus of the list, holds the source and the target of that annulus and no
other source or target. So one broadcast run gives every such copy the value of its annulus.

* `RData.qEnd`: the source corner (`τ = 0`) or the target corner (`τ = 1`) of an annulus with an index.
* `RData.endVal`: the values at the sources or at the targets of the list of a level, `⊤` elsewhere.
* `RData.endVal_end`: the value at the source or target of an annulus is its value.
* `RData.bcast_conds`: the conditions of `RData.levelBcast_local` at the copies of the corners of the
  top annulus inside an annulus of the list.
* `RData.bcast_guard`: a least value below `M` is the value of the annulus of the component.
* `RData.levelBcast_annulus`: one run of the message model gives each of these copies the value of
  its annulus, and a copy holds a value below `M` only as the value of the annulus of its component.
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

/-- The source corner `κ0(t)` (for `τ = 0`) or the target corner `κ1(t)` (for `τ = 1`) of an annulus
with an index `t`. -/
def qEnd (τ : Fin 2) (q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ) : N.G.Dart × Bool :=
  if τ = 0 then q.1.2.κ0 q.2 else q.1.2.κ1 q.2

theorem gcomp_qEnd (τ : Fin 2) {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ}
    (h1 : q.1.2.xa ≤ q.2) (h2 : q.1.2.ya ≤ q.2) (h3 : q.2 ≤ q.1.2.xb) (h4 : q.2 ≤ q.1.2.yb) :
    (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) (qEnd τ q) := by
  unfold qEnd
  split_ifs
  · exact q.1.2.gcomp_κ0 h1 h3
  · exact q.1.2.gcomp_κ1 h2 h4

/-- The values `pay q` at the sources (`τ = 0`) or targets (`τ = 1`) of the annuli `q` of the list of
a level, `⊤` elsewhere. -/
noncomputable def endVal (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    (z : Fin (n * (n * 21))) : ℕ∞ :=
  ⨅ q ∈ r.levelQ ℓ, ⨅ (_ : z = (S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))), (pay q : ℕ∞)

/-- A finite value of `endVal` sits at the source or target of an annulus of the list. -/
theorem endVal_ne_top (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {z : Fin (n * (n * 21))} (h : S.endVal hN r ℓ τ pay z ≠ ⊤) :
    ∃ q ∈ r.levelQ ℓ, z = (S.levelPad hN).ι (.inl (S.endV (qEnd τ q))) := by
  by_contra hn
  simp only [not_exists, not_and] at hn
  exact h (iInf_eq_top.2 fun q => iInf_eq_top.2 fun hq => iInf_eq_top.2 fun e => absurd e (hn q hq))

/-- `endVal` is `⊤` away from the copies of vertices. -/
theorem endVal_other (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {z : Fin (n * (n * 21))} (hz : ∀ u, z ≠ (S.levelPad hN).ι (.inl u)) :
    S.endVal hN r ℓ τ pay z = ⊤ :=
  iInf_eq_top.2 fun _ => iInf_eq_top.2 fun _ => iInf_eq_top.2 fun e => absurd e (hz _)

variable (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ)
include hΓ

/-- Two annuli of the list of a level whose sources or targets are joined by E_R and E_C edges are
equal. -/
theorem levelQ_end_eq (τ τ' : Fin 2) {q q' : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ}
    (hq : q ∈ r.levelQ ℓ) (hq' : q' ∈ r.levelQ ℓ)
    (h : Relation.ReflTransGen S.ERC (S.vcopy (S.endV (qEnd τ q))) (S.vcopy (S.endV (qEnd τ' q')))) :
    q = q' := by
  obtain ⟨hA, h1, h2, h3, h4⟩ := r.levelQ_range ℓ q hq
  obtain ⟨hB, h1', h2', h3', h4'⟩ := r.levelQ_range ℓ q' hq'
  have e := S.annulus_eq r ℓ hΓ hA hB ⟨_, S.endV_end _⟩ ⟨_, S.endV_end _⟩ (S.pieceOf_endV _)
    (S.pieceOf_endV _) (gcomp_qEnd τ h1 h2 h3 h4) (gcomp_qEnd τ' h1' h2' h3' h4') h
  exact Prod.ext e (r.levelQ_uniq ℓ q hq q' hq' e)

/-- **The value at a source or target.** -/
theorem endVal_end (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) :
    S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))) = pay q := by
  refine le_antisymm (iInf_le_of_le q (iInf_le_of_le hq (iInf_le_of_le rfl le_rfl)))
    (le_iInf fun q' => le_iInf fun hq' => le_iInf fun h => ?_)
  have hu := Sum.inl_injective ((S.levelPad hN).ι_injective h)
  have e := S.levelQ_end_eq r ℓ hΓ τ τ hq hq' (by rw [hu])
  rw [e]

/-- **The conditions of the broadcast.** For an annulus `q` of the list of a level and an index `t`
strictly inside its ranges, the copy at the corner `κ0(t)` (for `σ = 0`) or `κ1(t)` (for `σ = 1`) of
the top annulus is joined by E_R and E_C edges to the source and the target of `q`, which for each `τ`
is the only copy with a finite value of `endVal τ` joined to it, and that value is `pay q`. -/
theorem bcast_conds (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) (σ : Fin 2) {t : ℕ}
    (ht : if σ = 0 then q.1.2.xa < t ∧ t < q.1.2.xb else q.1.2.ya < t ∧ t < q.1.2.yb) :
    Relation.ReflTransGen S.ERC (S.vcopy (S.endV (qEnd τ q)))
        (S.vcopy (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))) ∧
      (∀ u, S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl u)) ≠ ⊤ →
        Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))) →
        u = S.endV (qEnd τ q)) ∧
      S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))) = pay q := by
  obtain ⟨hA, h1, h2, h3, h4⟩ := r.levelQ_range ℓ q hq
  obtain ⟨-, -, -, -, e0, e1⟩ := r.below_nodes ℓ q.1 hA
  have hin : (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa)
      (if σ = 0 then L₀.κ0 t else L₀.κ1 t) := by
    split_ifs at ht ⊢ with hσ
    · rw [← e0 t ht.1 ht.2]
      exact q.1.2.gcomp_κ0 ht.1.le ht.2.le
    · rw [← e1 t ht.1 ht.2]
      exact q.1.2.gcomp_κ1 ht.1.le ht.2.le
  have hv := S.region_erc r ℓ hΓ hA (gcomp_qEnd τ h1 h2 h3 h4) hin
  refine ⟨hv, fun u hu he => ?_, S.endVal_end hN r ℓ hΓ τ pay hq⟩
  obtain ⟨q', hq', hu'⟩ := S.endVal_ne_top hN r ℓ τ pay hu
  have hu'' := Sum.inl_injective ((S.levelPad hN).ι_injective hu')
  subst hu''
  have e := S.levelQ_end_eq r ℓ hΓ τ τ hq' hq (he.trans (S.erc_symm hv))
  rw [e]

/-- **A value below `M` is the value of an annulus.** With token lengths `0`, if the least offset plus
distance at the copy of `v` from the values `endVal τ` is below `M`, the component of the E_R and E_C
edges of `v` holds the source or target of an annulus `q` of the list, and that least value is
`pay q`. -/
theorem bcast_guard (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ) (M : ℕ)
    (hM : 1 ≤ M) (hpay : ∀ q ∈ r.levelQ ℓ, pay q ≤ M) (v : S.hRot.Vertex)
    (h : ⨅ u, (S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞) +
      S.arcDist (fun _ => 0) M (S.vcopy u) (S.vcopy v) < M) :
    ∃ q ∈ r.levelQ ℓ, Relation.ReflTransGen S.ERC (S.vcopy (S.endV (qEnd τ q))) (S.vcopy v) ∧
      ⨅ u, (S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞) +
        S.arcDist (fun _ => 0) M (S.vcopy u) (S.vcopy v) = pay q := by
  obtain ⟨u, hu⟩ := iInf_lt_iff.1 h
  have hfin : S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl u)) ≠ ⊤ := fun e => by
    rw [e, ENat.toENNReal_top, top_add] at hu
    exact absurd hu (not_lt.2 le_top)
  have hc : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v) := by
    by_contra hc
    have := S.le_arcDist (fun _ => 0) M (fun _ => .inl rfl) (by rwa [zr_zero])
    exact absurd (lt_of_le_of_lt (this.trans le_add_self) hu) (lt_irrefl _)
  obtain ⟨q, hq, hu'⟩ := S.endVal_ne_top hN r ℓ τ pay hfin
  have e := Sum.inl_injective ((S.levelPad hN).ι_injective hu')
  subst e
  refine ⟨q, hq, hc, ?_⟩
  have huniq : ∀ u', S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl u')) ≠ ⊤ →
      Relation.ReflTransGen S.ERC (S.vcopy u') (S.vcopy v) → u' = S.endV (qEnd τ q) := by
    intro u' hu₁ hc'
    obtain ⟨q', hq', hu₂⟩ := S.endVal_ne_top hN r ℓ τ pay hu₁
    have e := Sum.inl_injective ((S.levelPad hN).ι_injective hu₂)
    subst e
    rw [S.levelQ_end_eq r ℓ hΓ τ τ hq' hq (hc'.trans (S.erc_symm hc))]
  have hle : ((S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q))))) : ℝ≥0∞) ≤ M := by
    rw [S.endVal_end hN r ℓ hΓ τ pay hq]
    exact_mod_cast hpay q hq
  rw [S.bcast_eq hN M hM _ hc huniq hle, S.endVal_end hN r ℓ hΓ τ pay hq]
  simp

omit hΓ in
/-- **Values of the annuli of a level.** One algorithm of the message model on `N`, fixed before the
network, starts from the inputs of a level with token lengths `0` and, at each node, offsets that
agree with `endVal τ` at the identifiers it hosts. After `1 + C log^c n' · (12 D + 16)` rounds, for every
annulus `q` of the list of a level with a value at most `M` and every index `t` strictly inside its
ranges, the copy at the corner `κ0(t)` or `κ1(t)` of the top annulus holds the value of `q`, and every
copy that holds a value below `M` lies in the component of the source or target of an annulus `q` of
the list and holds the value of `q`. -/
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
      ∀ (τ : Fin 2) (pay : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ),
      (∀ q ∈ r.levelQ ℓ, pay q ≤ M) →
      (∀ a, off (hostOf a) a = S.endVal hN r ℓ τ pay a) →
      (∀ q ∈ r.levelQ ℓ, ∀ (σ : Fin 2) (t : ℕ),
        (if σ = 0 then q.1.2.xa < t ∧ t < q.1.2.xb else q.1.2.ya < t ∧ t < q.1.2.yb) →
        out ((S.levelPad hN).ι (.inl (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
            (hostOf ((S.levelPad hN).ι (.inl (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t)))))) =
          pay q) ∧
      ∀ v : S.hRot.Vertex,
        out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) < M →
        ∃ q ∈ r.levelQ ℓ, Relation.ReflTransGen S.ERC (S.vcopy (S.endV (qEnd τ q))) (S.vcopy v) ∧
          out ((S.levelPad hN).ι (.inl v))
            (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
              (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) =
            pay q := by
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
  refine ⟨fun q hq σ t ht => ?_, fun v hv => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := S.bcast_conds hN r ℓ hΓ τ pay hq σ ht
    have hle : ((S.endVal hN r ℓ τ pay ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q))))) : ℝ≥0∞) ≤ M := by
      rw [h3]
      exact_mod_cast hpay q hq
    have e := key (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))
    rw [S.bcast_eq hN M hM1 _ h1 h2 hle, h3] at e
    exact_mod_cast e
  · have hlt : (out ((S.levelPad hN).ι (.inl v)) (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
        (1 + Cc * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) < M := by
      exact_mod_cast hv
    rw [key v] at hlt
    obtain ⟨q, hq, hc', he⟩ := S.bcast_guard hN r ℓ hΓ τ pay M hM1 hpay v hlt
    refine ⟨q, hq, hc', ?_⟩
    have e := key v
    rw [he] at e
    exact_mod_cast e

end RData

end RotSystem

end SsspFlow
