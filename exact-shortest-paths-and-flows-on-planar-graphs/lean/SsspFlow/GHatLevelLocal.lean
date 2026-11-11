import SsspFlow.GHatLevelConn

/-!
# The lists of the network of a level, by names

The rotation list of the network of a level at an identifier, in terms of the names
(`RData.levelPad`):

* `RData.levelNet_rotList_dart`: at the name of a dart `x`, the name of the copy at which `x` starts and
  the name of the reverse dart.
* `RData.levelNet_rotList_copy`: at the name of a copy, the names of its darts in rotation order, then
  the identifiers that hang at it.
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

namespace Net

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

/-- The same network with lists that are rotations of its lists. -/
def relist (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) : Net V where
  G := N.G
  rotList := L
  nodup v := (hL v).nodup_iff.2 (N.nodup v)
  mem_rotList v w := (hL v).mem_iff.trans (N.mem_rotList v w)

theorem relist_rotPerm (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) :
    (N.relist L hL).rotPerm = N.rotPerm :=
  Equiv.ext fun d => SimpleGraph.Dart.ext _ _ (Prod.ext rfl (by
    show (L d.fst).formPerm d.snd = (N.rotList d.fst).formPerm d.snd
    rw [List.formPerm_eq_of_isRotated ((hL d.fst).nodup_iff.2 (N.nodup _)) (hL d.fst)]))

/-- Planarity does not depend on the instance of finiteness. -/
theorem _root_.SsspFlow.RotSystem.planar_of_inst {E : Type} [DecidableEq E] {i₁ i₂ : Fintype E}
    (R₁ : @RotSystem E i₁ _) (R₂ : @RotSystem E i₂ _)
    (hrev : @RotSystem.rev E i₁ _ R₁ = @RotSystem.rev E i₂ _ R₂)
    (hrot : @RotSystem.rot E i₁ _ R₁ = @RotSystem.rot E i₂ _ R₂)
    (h : @RotSystem.Planar E i₁ _ R₁) : @RotSystem.Planar E i₂ _ R₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  cases R₁
  cases R₂
  cases hrev
  cases hrot
  exact h

/-- **Rotated lists keep planarity.** The rotation is the same permutation of the same darts. -/
theorem relist_planar (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) (h : N.toRot.Planar) :
    (N.relist L hL).toRot.Planar :=
  RotSystem.planar_of_inst N.toRot (N.relist L hL).toRot rfl (N.relist_rotPerm L hL).symm h

theorem relist_diam (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) {D : ℕ} (h : N.DiamLE D) :
    (N.relist L hL).DiamLE D := h

end Net

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
  show padList (S.levelPad hN) S.hRot.subNet _ = _
  rw [padList_ι, S.hRot.subNet_rotList_inr, S.extras_inr hN, Finset.toList_empty, List.append_nil]
  rfl

/-- **The list at the name of a copy.** -/
theorem levelNet_rotList_copy (v : S.hRot.Vertex) :
    (S.levelNet hN).rotList ((S.levelPad hN).ι (.inl v)) =
      (S.hRot.vList v).map (fun x => (S.levelPad hN).ι (.inr x)) ++
        ((S.levelPad hN).extras (.inl v)).toList := by
  show padList (S.levelPad hN) S.hRot.subNet _ = _
  rw [padList_ι, S.hRot.subNet_rotList_inl, List.map_map]
  rfl

/-- **The list at an identifier that names nothing.** -/
theorem levelNet_rotList_pend {z : Fin (n * (n * 21))} (h : ¬ (S.levelPad hN).IsReal z) :
    (S.levelNet hN).rotList z = [idEquiv (hostOf z, hostOf z, 0)] := by
  show padList (S.levelPad hN) S.hRot.subNet _ = _
  rw [padList_of_not h, S.back_of_not_real hN h]
  rfl

end RData

end RotSystem

end SsspFlow
