import SsspFlow.GHatLevelX0
import SsspFlow.CutPathKap

/-!
# The base values of the corners as least values over pieces

The base values `0` to `3` of a corner, the least index and the least distance to the end of the cut
path at its vertex of the cut map and the flags of its two sides, are least values, over the corners at
that vertex, of a value that each corner knows from the indices of its own corner: `locIdx`. On data
whose corners are those of the cut path, the pieces are the vertices of the cut map, so these are least
values over pieces.

* `RData.gsBase_eq_cut`: the base values as least values over the vertex of the cut map.
* `RData.locOf_eq`: the value of a corner from its indices.
* `RData.gsBase_eq_piece`: on data with the corners of the cut path, the base values as least values over
  pieces.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)}

/-- The sides that the base value `k` looks at. -/
def sdOf (k : ℕ) (σ : Fin 2) : Prop := if k = 2 then σ = 0 else if k = 3 then σ = 1 else True

/-- The value of an index for the base value `k`. -/
def φOf (m k r : ℕ) : ℕ∞ := if k = 0 then (r : ℕ∞) else if k = 1 then ((m - r : ℕ) : ℕ∞) else 0

/-- The value of a corner for the base value `k`, from the indices of the corner itself. -/
noncomputable def locIdx (C : N.toRot.dual.CutPath) (k : ℕ) (z : N.G.Dart × Bool) : ℕ∞ :=
  ⨅ r, ⨅ (_ : r ≤ C.m ∧ ∃ σ, sdOf k σ ∧ z = C.k σ r), φOf C.m k r

/-- The value of a corner from the flags of its indices. -/
noncomputable def locOf (m : ℕ) (kap : (ℕ → Bool) × (ℕ → Bool)) (k : ℕ) : ℕ∞ :=
  ⨅ r, ⨅ (_ : r ≤ m ∧ ((sdOf k 0 ∧ kap.1 r = true) ∨ (sdOf k 1 ∧ kap.2 r = true))), φOf m k r

theorem locOf_eq (C : N.toRot.dual.CutPath) {z : N.G.Dart × Bool} {kap : (ℕ → Bool) × (ℕ → Bool)}
    (hkap : ∀ r, (kap.1 r = true ↔ z = C.k 0 r) ∧ (kap.2 r = true ↔ z = C.k 1 r)) (k : ℕ) :
    locOf C.m kap k = locIdx C k z := by
  unfold locOf locIdx
  refine iInf_congr fun r => iInf_congr_Prop (and_congr_right fun _ => ?_) fun _ => rfl
  rw [Fin.exists_fin_two, (hkap r).1, (hkap r).2]

/-- **The base values over the vertex of the cut map.** -/
theorem gsBase_eq_cut (C : N.toRot.dual.CutPath) {k : ℕ} (hk : k ≤ 3) (z : N.G.Dart × Bool) :
    gsBase C k z = ⨅ z', ⨅ (_ : C.cut.tail z' = C.cut.tail z), locIdx C k z' := by
  have hR : (⨅ z', ⨅ (_ : C.cut.tail z' = C.cut.tail z), locIdx C k z') =
      ⨅ r, ⨅ (_ : r ≤ C.m ∧ ∃ σ, sdOf k σ ∧ C.cut.tail z = C.cut.tail (C.k σ r)), φOf C.m k r := by
    apply le_antisymm
    · refine le_iInf fun r => le_iInf fun ⟨hr, σ, hs, hz⟩ => ?_
      exact iInf_le_of_le (C.k σ r) (iInf_le_of_le hz.symm (iInf_le_of_le r (iInf_le_of_le ⟨hr, σ, hs, rfl⟩ le_rfl)))
    · refine le_iInf fun z' => le_iInf fun hz' => le_iInf fun r => le_iInf fun ⟨hr, σ, hs, he⟩ => ?_
      subst he
      exact iInf_le_of_le r (iInf_le_of_le ⟨hr, σ, hs, hz'.symm⟩ le_rfl)
  rw [hR]
  interval_cases k
  · simp [gsBase, cornerIdx, sdOf, φOf]
  · simp [gsBase, cornerIdx, sdOf, φOf]
  · have e1 : gsBase C 2 z = flagVal C 0 z := by simp [gsBase]
    have e2 : ∀ r, φOf C.m 2 r = 0 := fun r => by simp [φOf]
    have e3 : ∀ σ, sdOf 2 σ ↔ σ = 0 := fun σ => by simp [sdOf]
    simp only [e1, e2, e3]
    unfold flagVal
    split_ifs with h
    · obtain ⟨t, ht, hz⟩ := h
      exact (le_antisymm (iInf_le_of_le t (iInf_le_of_le ⟨ht, 0, rfl, hz⟩ le_rfl)) bot_le).symm
    · refine (top_le_iff.1 (le_iInf fun r => le_iInf fun hr => ?_)).symm
      obtain ⟨hr, σ, hs, hz⟩ := hr
      subst hs
      exact absurd ⟨r, hr, hz⟩ h
  · have e1 : gsBase C 3 z = flagVal C 1 z := by simp [gsBase]
    have e2 : ∀ r, φOf C.m 3 r = 0 := fun r => by simp [φOf]
    have e3 : ∀ σ, sdOf 3 σ ↔ σ = 1 := fun σ => by simp [sdOf]
    simp only [e1, e2, e3]
    unfold flagVal
    split_ifs with h
    · obtain ⟨t, ht, hz⟩ := h
      exact (le_antisymm (iInf_le_of_le t (iInf_le_of_le ⟨ht, 1, rfl, hz⟩ le_rfl)) bot_le).symm
    · refine (top_le_iff.1 (le_iInf fun r => le_iInf fun hr => ?_)).symm
      obtain ⟨hr, σ, hs, hz⟩ := hr
      subst hs
      exact absurd ⟨r, hr, hz⟩ h

/-- On data whose corners are those of the cut path, the pieces are the vertices of the cut map. -/
theorem pieceAt_eq_iff (S : N.toRot.RData) (C : N.toRot.dual.CutPath) (hΓ : S.Γ = C.Γ)
    (z z' : N.G.Dart × Bool) : S.pieceAt z' = S.pieceAt z ↔ C.cut.tail z' = C.cut.tail z := by
  rw [← S.vertexEquiv.injective.eq_iff, vertexEquiv_pieceAt, vertexEquiv_pieceAt]
  show (N.toRot.dual.double.split S.Γ).tail z' = (N.toRot.dual.double.split S.Γ).tail z ↔ _
  rw [hΓ]

/-- **The base values over pieces.** -/
theorem gsBase_eq_piece (S : N.toRot.RData) (C : N.toRot.dual.CutPath) (hΓ : S.Γ = C.Γ) {k : ℕ}
    (hk : k ≤ 3) (z : N.G.Dart × Bool) :
    (⨅ z', ⨅ (_ : S.pieceAt z' = S.pieceAt z), locIdx C k z') = gsBase C k z := by
  rw [gsBase_eq_cut C hk z]
  exact iInf_congr fun z' => iInf_congr_Prop (S.pieceAt_eq_iff C hΓ z z') fun _ => rfl

end RData

end RotSystem

end SsspFlow
