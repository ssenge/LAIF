import SsspFlow.GHatLevelConn

/-!
# The lists of the network of a level, by names

The rotation list of the network of a level at an identifier, in terms of the names
(`RData.levelPad`):

* `RData.levelNet_rotList_dart`: at the name of a dart `x`, the name of the copy at which `x` starts and
  the name of the reverse dart.
* `RData.levelNet_rotList_copy`: at the name of a copy, the names of its darts in the order of
  Table R, then the identifiers that hang at it in increasing order.
* `RData.levelNet_rotList_pend`: at an identifier that names nothing, the star centre `(u, u, 0)` of its
  node `u`.

The adjacency of the network of a level is membership in these lists, so a node that knows the lists
at its own identifiers knows the edges at them.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace Congest

/-- **Views from lists.** If every node knows its own name and the rotation lists of `N'` at the
identifiers it hosts, the view "one end is mine and the other is in its list" is the adjacency of `N'`
at its identifiers. -/
theorem view_of_lists {V W I : Type} [Fintype W] [DecidableEq W] (N' : Net W) (h : W → V)
    (me : I → V) (L : I → W → List W) (inp : V → I) (hme : ∀ w, me (inp w) = w)
    (hL : ∀ w a, h a = w → L (inp w) a = N'.rotList a) (w : V) (b a : W) (hba : h b = w ∨ h a = w) :
    ((h b = me (inp w) ∧ a ∈ L (inp w) b) ∨ (h a = me (inp w) ∧ b ∈ L (inp w) a)) ↔
      N'.G.Adj b a := by
  rw [hme]
  constructor
  · rintro (⟨hb, ha⟩ | ⟨ha, hb⟩)
    · rw [hL w b hb] at ha
      exact (N'.mem_rotList b a).1 ha
    · rw [hL w a ha] at hb
      exact (N'.G.adj_symm) ((N'.mem_rotList a b).1 hb)
  · intro hadj
    rcases hba with hb | ha
    · exact .inl ⟨hb, by rw [hL w b hb]; exact (N'.mem_rotList b a).2 hadj⟩
    · exact .inr ⟨ha, by rw [hL w a ha]; exact (N'.mem_rotList a b).2 (N'.G.adj_symm hadj)⟩

end Congest

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

theorem levelPad_ι (x : S.hRot.Vertex ⊕ S.HD) : (S.levelPad hN).ι x = idEquiv (S.name x) := rfl

/-- The star centre of a node `u` is named `(u, u, 0)`. -/
theorem starV_name (u : Fin n) :
    (S.levelPad hN).ι (.inl (S.starV hN u)) = idEquiv (u, u, 0) := rfl

/-- An identifier that names nothing hangs at the star centre of its node. -/
theorem back_of_not_real {z : Fin (n * (n * 21))} (h : ¬ (S.levelPad hN).IsReal z) :
    (S.levelPad hN).back z = .inl (S.starV hN (hostOf z)) := by
  classical
  have hz : ¬ ∃ x, idEquiv (S.name x) = z := by
    rintro ⟨x, rfl⟩
    exact h ((S.levelPad hN).isReal_ι x)
  show (if h : ∃ x, idEquiv (S.name x) = z then h.choose
    else .inl (S.starV hN (idEquiv.symm z).1)) = _
  rw [dite_eq_right_of_eq_false (eq_false hz)]
  rfl

/-- No identifier hangs at a dart. -/
theorem extras_inr (x : S.HD) : (S.levelPad hN).extras (.inr x) = ∅ := by
  classical
  ext z
  simp only [PadMap.mem_extras, Finset.notMem_empty, iff_false, not_and]
  intro h
  rw [S.back_of_not_real hN h]
  exact Sum.inl_ne_inr

/-- **The list at the name of a dart.** -/
theorem levelNet_rotList_dart (x : S.HD) :
    (S.levelNet hN).rotList ((S.levelPad hN).ι (.inr x)) =
      [(S.levelPad hN).ι (.inl (S.hRot.tail x)), (S.levelPad hN).ι (.inr (S.hrev x))] := by
  show padList (S.levelPad hN) S.hatNet _ = _
  rw [padList_ι, show S.hatNet.rotList (.inr x) = _ from S.hRot.subNet_rotList_inr x, S.extras_inr hN, PadMap.order_empty, List.append_nil]
  rfl

/-- **The list at the name of a copy.** -/
theorem levelNet_rotList_copy (v : S.hRot.Vertex) :
    (S.levelNet hN).rotList ((S.levelPad hN).ι (.inl v)) =
      (S.lstR (S.vcopy v)).map (fun x => (S.levelPad hN).ι (.inr x)) ++
        (S.levelPad hN).order ((S.levelPad hN).extras (.inl v)) := by
  show padList (S.levelPad hN) S.hatNet _ = _
  rw [padList_ι, show S.hatNet.rotList (.inl v) = (S.lstR (S.vcopy v)).map Sum.inr from rfl,
    List.map_map]
  rfl

/-- **The list at an identifier that names nothing.** -/
theorem levelNet_rotList_pend {z : Fin (n * (n * 21))} (h : ¬ (S.levelPad hN).IsReal z) :
    (S.levelNet hN).rotList z = [idEquiv (hostOf z, hostOf z, 0)] := by
  show padList (S.levelPad hN) S.hatNet _ = _
  rw [padList_of_not h, S.back_of_not_real hN h]
  rfl

end RData

end RotSystem

end SsspFlow
