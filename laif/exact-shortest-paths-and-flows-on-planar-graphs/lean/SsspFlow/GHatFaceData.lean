import SsspFlow.GHatSplit
import SsspFlow.GHatPlanar

/-!
# Data without incisions: the pieces are the faces

The data of Definition R with no incised dart and no cut corner keep every face walk in one piece.
So the pieces of these data are the vertices of the doubled dual, that is the faces of `G`.

* `RData.faceData`: the data with no incision and no cut corner, for given modes and hosts.
* `RData.faceData_Γ`, `RData.faceData_noConflict`, `RData.faceData_cut`: they have no corners of the
  cut, no conflict and no cut corner.
* `RData.faceData_pieceAt_iff`: two corners of the doubled dual lie at one piece exactly when their
  darts lie at one vertex of the dual.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

universe u

section Double

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- The split at no corner has the vertices of the map. -/
theorem split_empty_tail_eq_iff (x y : D) :
    (R.split ∅).tail x = (R.split ∅).tail y ↔ R.tail x = R.tail y := by
  rw [tail_eq_iff, tail_eq_iff]
  have e : ((R.split ∅).rot : D → D) = R.rot := funext fun z => R.split_rot_of_not_mem (Finset.notMem_empty z)
  show fconnect ((R.split ∅).rot : D → D) x y ↔ fconnect (R.rot : D → D) x y
  rw [e]

/-- Two copies lie at one vertex of the doubled map exactly when their darts lie at one vertex. -/
theorem double_tail_eq_iff (z z' : D × Bool) :
    R.double.tail z = R.double.tail z' ↔ R.tail z.1 = R.tail z'.1 := by
  rw [tail_eq_iff, tail_eq_iff]
  exact ⟨fun h => R.fconnect_of_double h, fun h => R.fconnect_double h _ _⟩

end Double

namespace RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E}

/-- **The data with no incision and no cut corner**, for given modes and hosts. -/
def faceData (modeL hostT : E → Bool) (hh : ∀ d, hostT (G.rev d) = !hostT d) : G.RData where
  inc := ∅
  inc_rev _ := by simp
  cut := ∅
  modeL := modeL
  hostT := hostT
  hostT_rev d _ := hh d

variable (modeL hostT : E → Bool) (hh : ∀ d, hostT (G.rev d) = !hostT d)

@[simp] theorem faceData_inc : (faceData modeL hostT hh).inc = ∅ := rfl

@[simp] theorem faceData_cut : (faceData modeL hostT hh).cut = ∅ := rfl

theorem faceData_Γ : (faceData modeL hostT hh).Γ = ∅ := by
  simp [Γ]

theorem faceData_noConflict : (faceData modeL hostT hh).NoConflict := by
  intro d hd
  simp at hd

theorem faceData_cut_card : (faceData modeL hostT hh).cut.card ≤ 3 := by
  simp

/-- **The pieces of the data with no incision are the faces.** Two corners of the doubled dual lie at
one piece exactly when their darts lie at one vertex of the dual. -/
theorem faceData_pieceAt_iff (z z' : E × Bool) :
    (faceData modeL hostT hh).pieceAt z = (faceData modeL hostT hh).pieceAt z' ↔
      G.dual.tail z.1 = G.dual.tail z'.1 := by
  rw [← (faceData modeL hostT hh).vertexEquiv.apply_eq_iff_eq, vertexEquiv_pieceAt, vertexEquiv_pieceAt]
  show (G.dual.double.split (faceData modeL hostT hh).Γ).tail z =
    (G.dual.double.split (faceData modeL hostT hh).Γ).tail z' ↔ _
  rw [faceData_Γ, split_empty_tail_eq_iff, double_tail_eq_iff]

end RData

end RotSystem

end SsspFlow
