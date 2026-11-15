import SsspFlow.GHatCornerLocal

/-!
# The identifier of the copy of a corner, from local data

The copy `endV z` of a corner `z` is the first end of its token, a copy at the head of the dart of `z`.
Its identifier is a function of the rotation list of the head and the records of the darts out of it:
the copy is `R(c)` for the last token of an incised dart, and otherwise `X(c)` or `D(c)` for the tail
corner `c` of the reverse dart.

* `cornerName`: the name computed at the head.
* `RData.cornerName_eq`: it names the copy `endV z`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace RotSystem

/-- The name of the copy of the first end of the token of the corner `((u, w), b)`, from the rotation
list `R` of `w` and the records `f` of the darts out of `w`. -/
def cornerName {n : ℕ} (R : List (Fin n)) (f : Fin n → DInfo) (w u : Fin n) (b : Bool) :
    Fin n × Fin n × Fin 21 :=
  if b && (f u).inc then (w, R.formPerm.symm u, 3)
  else if (f (R.formPerm.symm u)).movB then (w, R.formPerm.symm u, 4) else (w, R.formPerm.symm u, 1)

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **The identifier of the copy of a corner from the data at its head.** -/
theorem cornerName_eq (d : N.G.Dart) (b : Bool) :
    idEquiv (cornerName (N.rotList d.snd) (S.dinfoAt d.snd) d.snd d.fst b) =
      (S.levelPad hN).ι (.inl (S.endV (d, b))) := by
  show _ = idEquiv (N.nameC (S.alpha (S.tokOf (d, b))))
  set c : N.G.Dart := N.toRot.tailCorner (N.toRot.rev d) with hc
  have hcd : S.dinfoAt d.snd ((N.rotList d.snd).formPerm.symm d.fst) = S.dinfo c := S.dinfoAt_dart c
  have hid : S.dinfoAt d.snd d.fst = S.dinfo (N.toRot.rev d) := S.dinfoAt_dart (N.toRot.rev d)
  have hmov : (S.dinfo c).movB = decide (S.MovB c) := S.movB_dinfo c
  have hinc : (S.dinfo (N.toRot.rev d)).inc = decide (N.toRot.rev d ∈ S.inc) := rfl
  unfold cornerName
  rw [hcd, hid, hmov, hinc]
  cases b
  · show _ = idEquiv (N.nameC (S.alpha (N.toRot.rev d, S.firstLab (N.toRot.rev d))))
    rw [S.alpha_first]
    unfold alphaD
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    unfold MovB
    split_ifs <;> rfl
  · show _ = idEquiv (N.nameC (S.alpha (N.toRot.rev d, S.lastLab (N.toRot.rev d))))
    unfold lastLab
    by_cases hi : N.toRot.rev d ∈ S.inc
    · simp only [hi, decide_true, Bool.and_self, ↓reduceIte]
      rfl
    · simp only [hi, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
      show _ = idEquiv (N.nameC (S.alphaD (N.toRot.tailCorner (N.toRot.rev d))))
      unfold alphaD MovB
      split_ifs <;> rfl

end RData

end RotSystem

end SsspFlow
