import SsspFlow.GHatCornerId
import SsspFlow.GHatLevelBcast

/-!
# The values of the annuli of a level at their sources and targets, from local values

A value of each annulus of the list of a level, put at the corners `κ0(t)` or `κ1(t)` of its source or
target, becomes the value `endVal` at the identifier of that copy, read at its host from the values at
the corners of the darts into the host. A local map of these values that keeps `⊤` is again of this
form.

* `RData.onCopies_endPay`: the least value at the corners whose token starts at a copy is `endVal`.
* `RData.endVal_map`: a local map of `endVal` that keeps `⊤` is `endVal` of the mapped values.
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

/-- **Values of the annuli at their ends, from the corners.** If `f` is `p q` at the source corner
(`τ = 0`) or target corner (`τ = 1`) of each annulus `q` of the list of the level, the least such
value, and `⊤` at other corners, then at every identifier the least value of `f` over the corners
whose token starts at its copy is `endVal`. -/
theorem onCopies_endPay (τ : Fin 2) (p : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    (f : N.G.Dart × Bool → ℕ∞) (hf : ∀ z, f z = ⨅ q ∈ r.levelQ ℓ, ⨅ (_ : z = qEnd τ q), (p q : ℕ∞))
    (a : Fin (n * (n * 21))) :
    S.onCopies hN (fun u => S.copyVal0 f (S.vcopy u)) a = S.endVal hN r ℓ τ p a := by
  unfold onCopies endVal copyVal0
  apply le_antisymm
  · refine le_iInf fun q => le_iInf fun hq => le_iInf fun ha => ?_
    subst ha
    refine iInf_le_of_le (S.endV (qEnd τ q)) (iInf_le_of_le rfl ?_)
    refine iInf_le_of_le ⟨S.tokOf (qEnd τ q), S.isTok_tokOf _⟩ (iInf_le_of_le (S.vcopy_endV _).symm
      (iInf_le_of_le (qEnd τ q) (iInf_le_of_le rfl ?_)))
    rw [hf]
    exact iInf_le_of_le q (iInf_le_of_le hq (iInf_le_of_le rfl le_rfl))
  · refine le_iInf fun u => le_iInf fun hu => le_iInf fun y => le_iInf fun hy => le_iInf fun z =>
      le_iInf fun hz => ?_
    rw [hf]
    refine le_iInf fun q => le_iInf fun hq => le_iInf fun hzq => ?_
    have e : S.endV z = u := S.vcopy_injective (by rw [S.vcopy_endV, hz, hy])
    refine iInf_le_of_le q (iInf_le_of_le hq (iInf_le_of_le ?_ le_rfl))
    rw [← hu, ← e, hzq]

variable (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ)
include hΓ

/-- **A local map of the values at the ends.** Let `F` keep `⊤` and give a finite value at the end of
each annulus of the list from its value there. Then `F` applied to `endVal` at each identifier is
`endVal` of the mapped values. -/
theorem endVal_map (τ : Fin 2) (p : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ → ℕ)
    (F : Fin (n * (n * 21)) → ℕ∞ → ℕ∞) (hF : ∀ a, F a ⊤ = ⊤)
    (hfin : ∀ q ∈ r.levelQ ℓ, F ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))) (p q) ≠ ⊤)
    (a : Fin (n * (n * 21))) :
    F a (S.endVal hN r ℓ τ p a) =
      S.endVal hN r ℓ τ (fun q => (F ((S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))) (p q)).toNat) a := by
  by_cases ha : ∃ q ∈ r.levelQ ℓ, a = (S.levelPad hN).ι (.inl (S.endV (qEnd τ q)))
  · obtain ⟨q, hq, rfl⟩ := ha
    rw [S.endVal_end hN r ℓ hΓ τ _ hq, S.endVal_end hN r ℓ hΓ τ _ hq]
    exact (ENat.natCast_toNat (hfin q hq)).symm
  · have h1 : ∀ p', S.endVal hN r ℓ τ p' a = ⊤ := fun p' => by
      by_contra h
      exact ha (S.endVal_ne_top hN r ℓ τ p' h)
    rw [h1, h1, hF]

end RData

end RotSystem

end SsspFlow
