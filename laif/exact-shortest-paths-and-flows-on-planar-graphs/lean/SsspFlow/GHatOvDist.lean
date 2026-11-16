import SsspFlow.GHatRegion

/-!
# Distances inside the region of an annulus

For two copies on E_R edges whose pieces lie at corners `y` and `z` of the component of an annulus of
a level in the cut along its own corners, the distance in `Ĝ_ℓ`, capped at `M`, is the distance from
`y` to `z` in that cut, capped at `M`.

* `RData.arcDist_region`: the capped distance of two copies of the region of an annulus.
* `RData.markDist_region`: for sources at copies that each lie at a corner of the region of an
  annulus of the level, with one source in the region of the annulus, the least distance from the
  sources at a corner of that region, capped at `M`, is the distance from the corner of the source.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- **Distances inside the region of an annulus.** For copies `a` and `b` on E_R edges of the pieces
at corners `y` and `z`, where `y` lies in the component of `κ0(x_a)` of an annulus of a level, the
distance in `Ĝ_ℓ` capped at `M` is the distance from `y` to `z` in the cut along the corners of the
annulus, capped at `M`. -/
theorem arcDist_region (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}
    (hA : A ∈ r.nodes ℓ) {y z : N.G.Dart × Bool}
    (hy : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) y)
    (a b : S.EndCopy) (ha : S.pieceOf a = S.pieceAt y) (hb : S.pieceOf b = S.pieceAt z) :
    min (S.arcDist lam M a.1 b.1) M =
      min ((N.toRot.dual.double.split A.1).walkDist (g ∘ Prod.fst)
        ((N.toRot.dual.double.split A.1).tail y) ((N.toRot.dual.double.split A.1).tail z)) M := by
  set W := (N.toRot.dual.double.split A.1).walkDist (g ∘ Prod.fst)
    ((N.toRot.dual.double.split A.1).tail y) ((N.toRot.dual.double.split A.1).tail z) with hW
  have hsub : A.1 ⊆ S.Γ := hΓ ▸ r.subset_level ℓ hA
  obtain ⟨p₀, hp₀⟩ := exists_walk_of_gcomp hy
  have hun : ∀ w ∈ S.Γ, w ∉ A.1 → ∀ q, ¬ (N.toRot.dual.double.split A.1).IsWalk
      ((N.toRot.dual.double.split A.1).tail y) q ((N.toRot.dual.double.split A.1).tail w) :=
    fun w hw hwA q hq => r.unreach_level ℓ hA (hΓ ▸ hw) hwA le_rfl A.2.le_x _ (hp₀.append hq)
  have hgf : (fun z : N.G.Dart × Bool => ENNReal.ofReal ((c z.1 : ℕ) : ℝ)) = g ∘ Prod.fst :=
    funext fun z => by simp [hgc]
  have hdd : S.ddist (fun x => ((c x.1.1 : ℕ) : ℝ)) (S.pieceOf a) (S.pieceOf b) = (W : EReal) := by
    rw [S.ddist_eq (fun d => ((c d : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _) (fun d => by simp only [hcr]),
      ha, hb, S.vertexEquiv_pieceAt, S.vertexEquiv_pieceAt]
    show (((N.toRot.dual.double.split S.Γ).walkDist _ ((N.toRot.dual.double.split S.Γ).tail y)
      ((N.toRot.dual.double.split S.Γ).tail z) : ℝ≥0∞) : EReal) = _
    rw [N.toRot.dual.double.walkDist_split_split hsub hun, hgf]
  have hlamR : (fun x => (lam x : ℝ)) = fun x => ((c x.1.1 : ℕ) : ℝ) := funext fun x => by rw [hlam]
  have hge := S.gdist_eq (lam := fun x => ((c x.1.1 : ℕ) : ℝ)) (M := (M : ℝ)) (fun _ => Nat.cast_nonneg _)
    (Nat.cast_nonneg _) a b
  rw [hdd, ← hlamR] at hge
  have hq : ∀ q : FaceDisjoint.Walk S.Arc a.1 b.1, S.gdist (fun x => (lam x : ℝ)) M a.1 b.1 ≤
      (((S.awt lam M q : ℕ) : ℝ≥0∞) : EReal) := fun q => by
    have h : S.gdist (fun x => (lam x : ℝ)) M a.1 b.1 ≤ (((S.awt lam M q : ℕ) : ℝ) : EReal) := by
      rw [S.awt_eq_wt]
      exact iInf_le (fun p : FaceDisjoint.Walk S.Arc _ _ =>
        ((p.wt (S.w (fun x => (lam x : ℝ)) M) : ℝ) : EReal)) q
    have e : (((S.awt lam M q : ℕ) : ℝ) : EReal) = (((S.awt lam M q : ℕ) : ℝ≥0∞) : EReal) := by simp
    rwa [e] at h
  have hMe : ((M : ℝ) : EReal) = ((M : ℝ≥0∞) : EReal) := by simp
  by_cases hWM : W < M
  · have hWe : (W : EReal) < ((M : ℝ) : EReal) := by
      rw [hMe]; exact EReal.coe_ennreal_lt_coe_ennreal_iff.2 hWM
    have h1 := hge.1 hWe
    have hle : S.arcDist lam M a.1 b.1 ≤ W := S.arcDist_le_of_gdist lam M (ne_top_of_lt hWM) h1
    have hge' : W ≤ S.arcDist lam M a.1 b.1 :=
      le_iInf fun q => EReal.coe_ennreal_le_coe_ennreal_iff.1 (h1 ▸ hq q)
    rw [le_antisymm hle hge']
  · push_neg at hWM
    have hWe : ((M : ℝ) : EReal) ≤ (W : EReal) := by
      rw [hMe]; exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hWM
    have h2 := hge.2 hWe
    have hMa : (M : ℝ≥0∞) ≤ S.arcDist lam M a.1 b.1 :=
      le_iInf fun q => EReal.coe_ennreal_le_coe_ennreal_iff.1 (hMe ▸ h2.trans (hq q))
    rw [min_eq_right hMa, min_eq_right hWM]

/-- **Distances from one source per region.** Let every copy `u` with `mk u` be a copy on an E_R edge
whose piece lies at a corner of the region of an annulus of `Q`, and let `u₁` be the only such copy of
the region of the annulus `A`, at the corner `c₁`. Then at every corner `z` of the region of `A` the
least distance from these copies, capped at `M`, is the distance from `c₁` to `z` in the cut along the
corners of `A`, capped at `M`. -/
theorem markDist_region (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ) (mk : S.hRot.Vertex → Prop)
    (hmk : ∀ u, mk u → ∃ q ∈ Q, ∃ y, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp
      (q.1.2.κ0 q.1.2.xa) y ∧ ∃ he : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)), S.pieceOf ⟨_, he⟩ = S.pieceAt y)
    {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {u₁ : S.hRot.Vertex}
    (hu₁ : mk u₁) {c₁ : N.G.Dart × Bool}
    (hc₁ : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) c₁)
    (he₁ : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u₁)) (hp₁ : S.pieceOf ⟨_, he₁⟩ = S.pieceAt c₁)
    (huniq : ∀ u, mk u → ∀ y, (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) y →
      ∀ he : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)), S.pieceOf ⟨_, he⟩ = S.pieceAt y → u = u₁)
    {z : N.G.Dart × Bool} (hz : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) z) :
    min (⨅ u, ⨅ (_ : mk u), S.arcDist lam M (S.vcopy u) (S.vcopy (S.endV z))) M =
      min ((N.toRot.dual.double.split A.1).walkDist (g ∘ Prod.fst)
        ((N.toRot.dual.double.split A.1).tail c₁) ((N.toRot.dual.double.split A.1).tail z)) M := by
  have key := S.arcDist_region r ℓ lam M c hcr hlam hgc hΓ hA hc₁ ⟨_, he₁⟩ ⟨_, S.endV_end z⟩ hp₁
    (S.pieceOf_endV z)
  rw [← key]
  apply le_antisymm
  · exact min_le_min_right _ (iInf₂_le u₁ hu₁)
  · refine le_min ?_ (min_le_right _ _)
    refine le_iInf₂ fun u hu => ?_
    obtain ⟨q, hq, y, hy, he, hp⟩ := hmk u hu
    by_cases h : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy (S.endV z))
    · have e := S.annulus_eq r ℓ hΓ (hQ q hq) hA ⟨_, he⟩ ⟨_, S.endV_end z⟩ hp (S.pieceOf_endV z) hy hz h
      subst e
      obtain rfl := huniq u hu y hy he hp
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (S.le_arcDist_of_not_erc lam M h)

end RData

end RotSystem

end SsspFlow
