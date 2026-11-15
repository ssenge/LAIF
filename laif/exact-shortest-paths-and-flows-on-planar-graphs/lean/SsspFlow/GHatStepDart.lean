import SsspFlow.GHatLevelDarts
import SsspFlow.GHatLevelLocal

/-!
# The dart of the token of an arc, decided at its head

An arc of the network of a level carries a token exactly when it joins the two rim darts of a primal
dart `d`. The head of the arc, a rim dart of `d` at the tail of `d`, decides this from its own
identifier, the identifier of the tail of the arc and its rotation list, and reads the corner of the
dart of the token from the record of `d`.

* `stepCornerL`: the corner, as its tail, head and bit, decided at the host of the head of an arc.
* `RData.stepCornerL_eq`: it is the corner of the dart of the token of the arc, if there is one.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace RotSystem

namespace RData

/-- The corner of the dart of the token of the arc from `par` to `y`, as its tail, head and bit,
decided from the rotation list `R` and the records `f` at the host of `y`. -/
def stepCornerL {n : ℕ} (R : List (Fin n)) (f : Fin n → DInfo) (y par : Fin (n * (n * 21))) :
    Option (Fin n × Fin n × Bool) :=
  if (idEquiv.symm y).2.1 ∈ R ∧ ((idEquiv.symm y).2.2 = 13 ∨ (idEquiv.symm y).2.2 = 14) ∧
      par = idEquiv ((idEquiv.symm y).1, (idEquiv.symm y).2.1, if (idEquiv.symm y).2.2 = 13 then 14 else 13) then
    some (if (idEquiv.symm y).2.2 = 14 then ((idEquiv.symm y).2.1, (idEquiv.symm y).1, false)
      else ((idEquiv.symm y).1, (idEquiv.symm y).2.1, (f (idEquiv.symm y).2.1).inc))
  else none


variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **The corner of the token of an arc, from local data.** -/
theorem stepCornerL_eq (y par : Fin (n * (n * 21))) :
    stepCornerL (N.rotList (hostOf y)) (S.dinfoAt (hostOf y)) y par =
      (S.edgeTok hN par y).map fun x => ((N.toRot.tokDart x.1).1.fst, (N.toRot.tokDart x.1).1.snd,
        (N.toRot.tokDart x.1).2) := by
  classical
  have hι : ∀ x : S.HD, (S.levelPad hN).ι (.inr x) = idEquiv (S.nameD x) := fun _ => rfl
  have hhost : hostOf y = (idEquiv.symm y).1 := rfl
  unfold edgeTok stepCornerL
  rw [hhost]
  by_cases h : ∃ d : S.HD, par = (S.levelPad hN).ι (.inr d) ∧ y = (S.levelPad hN).ι (.inr (S.hrev d))
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    obtain ⟨hp, hy⟩ := h.choose_spec
    generalize h.choose = d at hp hy
    subst hp hy
    rw [hι, hι, Equiv.symm_apply_apply]
    obtain ⟨e, b⟩ := d
    rcases e with c | d0 | x | a | a | c
    · cases b <;> simp [hrev, nameD, hdTok]
    · have hm : d0.snd ∈ N.rotList d0.fst := (N.mem_rotList _ _).2 d0.adj
      have hf : (S.dinfoAt d0.fst d0.snd).inc = decide (d0 ∈ S.inc) := by
        rw [S.dinfoAt_dart d0]; rfl
      cases b <;> by_cases hi : d0 ∈ S.inc <;>
        simp [hrev, nameD, hdTok, rimTok, hi, hm, hf, partnerTok, RotSystem.partner, RotSystem.tokDart, Lab.swap]
    · obtain ⟨⟨d, l⟩, hx⟩ := x
      cases l <;> cases b <;> simp [hrev, nameD, hdTok]
    · cases b <;> simp [hrev, nameD, hdTok]
    · cases b <;> simp [hrev, nameD, hdTok]
    · cases b <;> simp [hrev, nameD, hdTok]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    simp only [Option.map_none]
    refine ite_eq_right_iff.2 fun hc => absurd hc ?_
    rintro ⟨hm, hk, hp⟩
    have hadj : N.G.Adj (idEquiv.symm y).1 (idEquiv.symm y).2.1 := (N.mem_rotList _ _).1 hm
    set d0 : N.G.Dart := ⟨((idEquiv.symm y).1, (idEquiv.symm y).2.1), hadj⟩
    have hy : y = (S.levelPad hN).ι (.inr (.rim d0, decide ((idEquiv.symm y).2.2 = 14))) := by
      rw [hι]
      conv_lhs => rw [← Equiv.apply_symm_apply idEquiv y]
      congr 1
      rcases hk with hk | hk
      · simp only [nameD, hk, d0]
        exact Prod.ext rfl (Prod.ext rfl hk)
      · simp only [nameD, hk, d0, decide_true, ite_true]
        exact Prod.ext rfl (Prod.ext rfl hk)
    refine h ⟨(.rim d0, !decide ((idEquiv.symm y).2.2 = 14)), ?_, ?_⟩
    · rw [hp, hι]
      congr 1
      rcases hk with hk | hk <;> simp [nameD, hk, d0]
    · simp only [hrev, Bool.not_not]
      exact hy

end RData

end RotSystem

end SsspFlow
