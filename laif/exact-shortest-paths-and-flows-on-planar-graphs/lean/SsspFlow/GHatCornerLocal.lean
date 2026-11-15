import SsspFlow.GHatPieceLocal
import SsspFlow.GHatLevelBcast

/-!
# Values at the first ends of tokens, from local data

The copy at the first end of the token at a corner `(d, b)` is hosted at the head of `d`, at every
level. The first-end darts of the tokens at a copy are the token darts of kinds `5` to `7` in its
rotation list, so the host of a copy computes the least value of `f` over the corners whose tokens
start there from the values of `f` at the corners of the darts into it. For values `0` and `⊤` this
decides which corners have their token's first end at the copy; in particular the sources and the
targets of a list of annuli are local once each corner knows whether it is the source or target
corner of an annulus of the list.

* `RData.hostOf_endV`: the host of the copy of a corner `(d, b)` is the head of `d`.
* `RData.copyVal0`: the least value of `f` over the corners whose token has its first end at a copy.
* `RData.locCopy_eq0`: the value computed at the host of an identifier from its rotation list, with
  `⊤` on the darts out of it, is `copyVal0 f` at a copy of a vertex and `⊤` elsewhere.
* `RData.copyVal0_flag`: for values `0` and `⊤`, `copyVal0 f` at a copy is `0` exactly when the first
  end of the token at some corner of value `0` is that copy.
* `RData.onCopies_endFlag`: the offsets of the sources (`τ = 0`), or the targets (`τ = 1`), of a list of
  annuli, from the corners that are their source or target corners.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (f : N.G.Dart × Bool → ℕ∞)

/-- **The host of the copy of a corner** `(d, b)` is the head of `d`. -/
theorem hostOf_endV (z : N.G.Dart × Bool) :
    hostOf ((S.levelPad hN).ι (.inl (S.endV z))) = z.1.snd := by
  rw [S.hostOf_inl, S.vcopy_endV]
  obtain ⟨w, b⟩ := z
  cases b
  · show (N.nameC (S.alpha (N.toRot.rev w, S.firstLab (N.toRot.rev w)))).1 = w.snd
    generalize S.firstLab (N.toRot.rev w) = l
    cases l <;> simp only [alpha, alphaD] <;> (try split_ifs) <;> rfl
  · show (N.nameC (S.alpha (N.toRot.rev w, S.lastLab (N.toRot.rev w)))).1 = w.snd
    generalize S.lastLab (N.toRot.rev w) = l
    cases l <;> simp only [alpha, alphaD] <;> (try split_ifs) <;> rfl

/-- The least value of `f` over the corners whose token has its first end at the copy `c`. -/
noncomputable def copyVal0 (c : Copy N.toRot.Vertex N.G.Dart) : ℕ∞ :=
  ⨅ y : S.Tok, ⨅ (_ : S.alpha y.1 = c), ⨅ z, ⨅ (_ : S.tokOf z = y.1), f z

/-- The value of a dart of `Ĝ_ℓ` at its first end: the least value of `f` at the corners of its
token for the first-end dart of a token, `⊤` otherwise. -/
noncomputable def tv0 : S.HD → ℕ∞
  | (.tok y, false) => ⨅ z, ⨅ (_ : S.tokOf z = y.1), f z
  | _ => ⊤

theorem copyVal0_lstR (c : Copy N.toRot.Vertex N.G.Dart) :
    S.copyVal0 f c = ⨅ x ∈ S.lstR c, S.tv0 f x := by
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => ?_
    rw [S.mem_lstR_iff] at hx
    obtain ⟨e, b⟩ := x
    rcases e with c' | c' | y | c' | c' | c'
    case tok =>
      cases b
      · exact iInf_le_of_le y (iInf_le_of_le hx le_rfl)
      · exact le_top
    all_goals exact le_top
  · exact le_iInf fun y => le_iInf fun hy =>
      iInf_le_of_le (HE.tok y, false) (iInf_le_of_le ((S.mem_lstR_iff _ _).2 hy) le_rfl)

theorem copyVal0_star (v : N.toRot.Vertex) : S.copyVal0 f (.star v) = ⊤ := by
  refine le_antisymm le_top (le_iInf fun y => le_iInf fun hy => ?_)
  exfalso
  obtain ⟨⟨d, l⟩, hd⟩ := y
  cases l <;> simp [alpha, alphaD] at hy <;> split_ifs at hy

variable (vi : Fin n → Fin n → Bool → ℕ∞) (hvi : ∀ (d : N.G.Dart) b, vi d.snd d.fst b = f (d, b))
include hvi

/-- **The value at the name of a dart, at its first end.** -/
theorem tokVal_nameD0 (x : S.HD) :
    tokVal (S.dinfoAt (S.nameD x).1) (fun u => S.dinfoAt u (S.nameD x).1) (fun _ _ => ⊤)
      (vi (S.nameD x).1) (S.nameD x) = S.tv0 f x := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | ⟨⟨d, l⟩, hd⟩ | c | c | c
  case tok =>
    cases b
    · show _ = ⨅ z, ⨅ (_ : S.tokOf z = (d, l)), f z
      rw [S.tokSet f d l]
      cases l <;>
        simp only [nameD, tokVal, kLab, S.dinfoAt_dart, S.dinfoAt_symm, Net.toRot_rev] <;> norm_num <;>
        exact iInf_congr fun b' => iInf_congr fun _ => hvi d.symm b'
    · cases l <;> simp [nameD, tokVal, tv0]
  all_goals cases b <;> simp [nameD, tokVal, tv0]

/-- **The value at the first ends, from local data.** The value computed at the host of an identifier
from the rotation list of the network of a level there, the records of the darts at the host and into
it, the values of `f` at the corners of the darts into it, and `⊤` for the darts out of it, is
`copyVal0 f` at the copy of a vertex and `⊤` at every other identifier. -/
theorem locCopy_eq0 (a : Fin (n * (n * 21))) :
    locCopy (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (fun _ _ => ⊤) (vi (hostOf a))
      (idEquiv.symm a).2.2 ((S.levelNet hN).rotList a) =
      S.onCopies hN (fun u => S.copyVal0 f (S.vcopy u)) a := by
  classical
  by_cases hz : (S.levelPad hN).IsReal a
  · obtain ⟨y, rfl⟩ : ∃ y, a = (S.levelPad hN).ι y := ⟨_, hz⟩
    have hname : idEquiv.symm ((S.levelPad hN).ι y) = S.name y := idEquiv.symm_apply_apply _
    have hhost : hostOf ((S.levelPad hN).ι y) = (S.name y).1 := by
      unfold hostOf; rw [hname]
    rcases y with v | x
    · rw [S.onCopies_copy, S.levelNet_rotList_copy, hhost, hname]
      show locCopy _ _ _ _ (N.nameC (S.vcopy v)).2.2 _ = _
      by_cases h0 : (N.nameC (S.vcopy v)).2.2 = 0
      · have hst : ∃ w, S.vcopy v = .star w := by
          revert h0
          cases S.vcopy v <;> simp [Net.nameC]
        obtain ⟨w, hw⟩ := hst
        rw [hw, S.copyVal0_star]
        unfold locCopy
        rw [hw] at h0
        rw [h0]
        simp
      · unfold locCopy
        have hk : 1 ≤ (N.nameC (S.vcopy v)).2.2.val ∧ (N.nameC (S.vcopy v)).2.2.val < 5 :=
          ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (Fin.ext h), N.nameC_kind _⟩
        rw [S.extras_inl hN v]
        simp only [hk, h0, and_self, ↓reduceIte]
        rw [(S.levelPad hN).order_empty, List.append_nil, S.copyVal0_lstR]
        apply le_antisymm
        · refine le_iInf fun x => le_iInf fun hx => iInf_le_of_le ((S.levelPad hN).ι (.inr x))
            (iInf_le_of_le (List.mem_map.2 ⟨x, hx, rfl⟩) (le_of_eq ?_))
          have hw : (S.name (.inl v)).1 = (S.nameD x).1 := by
            show (N.nameC (S.vcopy v)).1 = _
            rw [← S.tl_of_mem_lstR hx]; exact S.nameC_tl x
          rw [show idEquiv.symm ((S.levelPad hN).ι (.inr x)) = S.nameD x from idEquiv.symm_apply_apply _, hw]
          exact S.tokVal_nameD0 f vi hvi x
        · refine le_iInf fun b => le_iInf fun hb => ?_
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
          refine iInf_le_of_le x (iInf_le_of_le hx (le_of_eq ?_))
          have hw : (S.name (.inl v)).1 = (S.nameD x).1 := by
            show (N.nameC (S.vcopy v)).1 = _
            rw [← S.tl_of_mem_lstR hx]; exact S.nameC_tl x
          rw [show idEquiv.symm ((S.levelPad hN).ι (.inr x)) = S.nameD x from idEquiv.symm_apply_apply _, hw]
          exact (S.tokVal_nameD0 f vi hvi x).symm
    · rw [S.onCopies_other hN _ _ fun u h => Sum.inr_ne_inl ((S.levelPad hN).ι_injective h), hname]
      unfold locCopy
      have hk := S.nameD_kind x
      rw [show (S.name (.inr x)).2.2 = (S.nameD x).2.2 from rfl]
      have : ¬ (1 ≤ (S.nameD x).2.2.val ∧ (S.nameD x).2.2.val < 5) := by omega
      simp only [this, ↓reduceIte]
  · rw [S.onCopies_other hN _ _ fun u h => hz (by rw [h]; exact (S.levelPad hN).isReal_ι _),
      S.levelNet_rotList_pend hN hz]
    unfold locCopy
    split_ifs
    · simp [tokVal]
    · rfl

omit hvi

open Classical in
/-- **Flags at the first ends.** For values `0` and `⊤`, `copyVal0 f` at the copy of `u` is `0` exactly
when the first end of the token at some corner of value `0` is `u`, and `⊤` otherwise. -/
theorem copyVal0_flag (hf : ∀ z, f z = 0 ∨ f z = ⊤) (u : S.hRot.Vertex) :
    S.copyVal0 f (S.vcopy u) = if ∃ z, S.endV z = u ∧ f z = 0 then 0 else ⊤ := by
  split_ifs with h
  · obtain ⟨z, rfl, hz⟩ := h
    exact le_antisymm (iInf_le_of_le ⟨S.tokOf z, S.isTok_tokOf z⟩ (iInf_le_of_le (S.vcopy_endV z).symm
      (iInf_le_of_le z (iInf_le_of_le rfl (le_of_eq hz))))) zero_le
  · refine iInf_eq_top.2 fun y => iInf_eq_top.2 fun hy => iInf_eq_top.2 fun z => iInf_eq_top.2 fun hz => ?_
    rcases hf z with h0 | h0
    · refine absurd ⟨z, S.vcopy_injective ?_, h0⟩ h
      rw [S.vcopy_endV, hz, hy]
    · exact h0

open Classical in
/-- **Sources and targets from their corners.** If `f` is `0` exactly at the source corners (`τ = 0`), or
the target corners (`τ = 1`), of the annuli of a list `Q`, and `⊤` elsewhere, then at every identifier
the least value of `f` over the corners whose token starts at its copy is `0` at the sources, or the
targets, of `Q` and `⊤` elsewhere. -/
theorem onCopies_endFlag {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} (τ : Fin 2)
    (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hf : ∀ z, f z = if ∃ q ∈ Q, z = qEnd τ q then 0 else ⊤) (a : Fin (n * (n * 21))) :
    S.onCopies hN (fun u => S.copyVal0 f (S.vcopy u)) a =
      if ∃ q ∈ Q, a = (S.levelPad hN).ι (.inl (S.endV (qEnd τ q))) then 0 else ⊤ := by
  have hf' : ∀ z, f z = 0 ∨ f z = ⊤ := fun z => by rw [hf z]; split_ifs <;> simp
  have h0 : ∀ z, f z = 0 ↔ ∃ q ∈ Q, z = qEnd τ q := fun z => by
    rw [hf z]; split_ifs with h <;> simp [h]
  split_ifs with h
  · obtain ⟨q, hq, rfl⟩ := h
    rw [S.onCopies_copy, S.copyVal0_flag f hf']
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨qEnd τ q, rfl, (h0 _).2 ⟨q, hq, rfl⟩⟩)
  · by_cases ha : ∃ u, a = (S.levelPad hN).ι (.inl u)
    · obtain ⟨u, rfl⟩ := ha
      rw [S.onCopies_copy, S.copyVal0_flag f hf']
      refine ite_eq_right_of_eq_false _ _ (eq_false fun ⟨z, hz, hz0⟩ => h ?_)
      obtain ⟨q, hq, rfl⟩ := (h0 z).1 hz0
      exact ⟨q, hq, by rw [hz]⟩
    · exact S.onCopies_other hN _ _ fun u e => ha ⟨u, e⟩

end RData

end RotSystem

end SsspFlow
