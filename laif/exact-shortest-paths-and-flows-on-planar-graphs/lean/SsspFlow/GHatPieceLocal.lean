import SsspFlow.GHatPieceMin
import SsspFlow.GHatLevelRaw

/-!
# The value of a copy from local data

The value `copyVal f` of a copy, the least value of `f` over the corners of the tokens that end there,
is known to the host of the copy: the tokens that end at a copy are the E_R darts in its rotation list,
their names give the dart and the label, the record of the dart gives the corners at which the token
lies, and these corners are the two corners of the reverse dart. So a node that knows the rotation
lists of the network of a level at its identifiers, the records of its darts and of the darts into it,
and the values of `f` at the corners of both darts of each of its edges computes `copyVal f` at each
copy it hosts, and `⊤` at its other identifiers.

* `RData.tokSet`: the corners whose token is `(d, l)` are the corners `(rev d, b)` with the label `l`
  for `b` in the record of `d`.
* `RData.copyVal_lstR`: `copyVal f` as a least value over the darts in the list of the copy.
* `RData.tokVal_nameD`: the value at the name of a dart, from the data of its host.
* `RData.locCopy_eq`: the value computed at the host of an identifier from its rotation list is
  `copyVal f` at a copy of a vertex and `⊤` elsewhere.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

section Loc

variable {n : ℕ}

/-- The label of the token of a dart at the first (`false`) or the last (`true`) side, from its
record. -/
def labOf (i : DInfo) : Bool → Lab
  | false => if i.inc then .one else .zero
  | true => if i.inc then .two else .zero

/-- The label in the kind of the name of a token dart. -/
def kLab (k : ℕ) : Lab := if k % 3 = 2 then .zero else if k % 3 = 0 then .one else .two

/-- The value at the name `p` of a dart at a node `w`, with the records `fo u`, `fi u` of the darts
`(w, u)`, `(u, w)` and the values `vo u b`, `vi u b` at their corners: for a token dart, the least value
at the corners of the reverse dart whose token it is; `⊤` for other darts. -/
noncomputable def tokVal (fo fi : Fin n → DInfo) (vo vi : Fin n → Bool → ℕ∞) (p : Fin n × Fin n × Fin 21) :
    ℕ∞ :=
  if 5 ≤ p.2.2.val ∧ p.2.2.val ≤ 7 then ⨅ b, ⨅ (_ : labOf (fo p.2.1) b = kLab p.2.2.val), vi p.2.1 b
  else if 8 ≤ p.2.2.val ∧ p.2.2.val ≤ 10 then ⨅ b, ⨅ (_ : labOf (fi p.2.1) b = kLab p.2.2.val), vo p.2.1 b
  else ⊤

/-- The value computed at an identifier of kind `k` with rotation list `L`. -/
noncomputable def locCopy (fo fi : Fin n → DInfo) (vo vi : Fin n → Bool → ℕ∞) (k : Fin 21)
    (L : List (Fin (n * (n * 21)))) : ℕ∞ :=
  if 1 ≤ k.val ∧ k.val < 5 then ⨅ b ∈ L, tokVal fo fi vo vi (RData.idEquiv.symm b) else ⊤

end Loc

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (f : N.G.Dart × Bool → ℕ∞)

theorem labOf_dinfo (d : N.G.Dart) :
    labOf (S.dinfo d) false = S.firstLab d ∧ labOf (S.dinfo d) true = S.lastLab d := by
  unfold labOf dinfo firstLab lastLab
  by_cases h : d ∈ S.inc <;> simp [h]

/-- **The corners of a token.** -/
theorem tokSet (d : N.G.Dart) (l : Lab) :
    ⨅ z, ⨅ (_ : S.tokOf z = (d, l)), f z = ⨅ b, ⨅ (_ : labOf (S.dinfo d) b = l), f (N.toRot.rev d, b) := by
  obtain ⟨h0, h1⟩ := S.labOf_dinfo d
  apply le_antisymm
  · refine le_iInf fun b => le_iInf fun h => iInf_le_of_le (N.toRot.rev d, b) (iInf_le_of_le ?_ le_rfl)
    cases b
    · show (N.toRot.rev (N.toRot.rev d), S.firstLab (N.toRot.rev (N.toRot.rev d))) = (d, l)
      rw [N.toRot.rev_rev, ← h0, h]
    · show (N.toRot.rev (N.toRot.rev d), S.lastLab (N.toRot.rev (N.toRot.rev d))) = (d, l)
      rw [N.toRot.rev_rev, ← h1, h]
  · refine le_iInf fun z => le_iInf fun hz => ?_
    obtain ⟨w, b⟩ := z
    cases b
    · have e : (N.toRot.rev w, S.firstLab (N.toRot.rev w)) = (d, l) := hz
      obtain ⟨rfl, h2⟩ := Prod.mk.inj e
      refine iInf_le_of_le false (iInf_le_of_le ?_ (by rw [N.toRot.rev_rev]))
      rw [(S.labOf_dinfo _).1, h2]
    · have e : (N.toRot.rev w, S.lastLab (N.toRot.rev w)) = (d, l) := hz
      obtain ⟨rfl, h2⟩ := Prod.mk.inj e
      refine iInf_le_of_le true (iInf_le_of_le ?_ (by rw [N.toRot.rev_rev]))
      rw [(S.labOf_dinfo _).2, h2]

/-- The value of a dart of `Ĝ_ℓ`: the least value of `f` at the corners of its token for a token dart,
`⊤` otherwise. -/
noncomputable def tv : S.HD → ℕ∞
  | (.tok y, _) => ⨅ z, ⨅ (_ : S.tokOf z = y.1), f z
  | _ => ⊤

theorem mem_lstR_iff (c : Copy N.toRot.Vertex N.G.Dart) (x : S.HD) : x ∈ S.lstR c ↔ S.tl x = c :=
  ⟨S.tl_of_mem_lstR, fun h => (S.lstR_rot c).mem_iff.2 (h ▸ S.mem_lst_tl x)⟩

/-- **The value of a copy from its list.** -/
theorem copyVal_lstR (c : Copy N.toRot.Vertex N.G.Dart) :
    S.copyVal f c = ⨅ x ∈ S.lstR c, S.tv f x := by
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => ?_
    rw [S.mem_lstR_iff] at hx
    obtain ⟨e, b⟩ := x
    rcases e with c' | c' | y | c' | c' | c'
    case tok =>
      have hend : S.IsEnd y.1 c := by
        cases b
        · exact .inl hx
        · exact .inr hx
      exact iInf_le_of_le y (iInf_le_of_le hend le_rfl)
    all_goals exact le_top
  · refine le_iInf fun y => le_iInf fun hy => ?_
    rcases hy with hy | hy
    · exact iInf_le_of_le (HE.tok y, false) (iInf_le_of_le ((S.mem_lstR_iff _ _).2 hy) le_rfl)
    · exact iInf_le_of_le (HE.tok y, true) (iInf_le_of_le ((S.mem_lstR_iff _ _).2 hy) le_rfl)

variable (vo vi : Fin n → Fin n → Bool → ℕ∞) (hvo : ∀ (d : N.G.Dart) b, vo d.fst d.snd b = f (d, b))
  (hvi : ∀ (d : N.G.Dart) b, vi d.snd d.fst b = f (d, b))
include hvo hvi

/-- **The value at the name of a dart, from the data of its host.** -/
theorem tokVal_nameD (x : S.HD) :
    tokVal (S.dinfoAt (S.nameD x).1) (fun u => S.dinfoAt u (S.nameD x).1) (vo (S.nameD x).1)
      (vi (S.nameD x).1) (S.nameD x) = S.tv f x := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | ⟨⟨d, l⟩, hd⟩ | c | c | c
  case tok =>
    show _ = ⨅ z, ⨅ (_ : S.tokOf z = (d, l)), f z
    rw [S.tokSet f d l]
    cases b <;> cases l <;>
      simp only [nameD, tokVal, kLab, S.dinfoAt_dart, S.dinfoAt_symm, Net.toRot_rev] <;> norm_num <;>
      first
        | exact iInf_congr fun b' => iInf_congr fun _ => hvi d.symm b'
        | exact iInf_congr fun b' => iInf_congr fun _ => hvo d.symm b'
  all_goals cases b <;> simp [nameD, tokVal, tv]

omit hvo hvi in
theorem copyVal_star (v : N.toRot.Vertex) : S.copyVal f (.star v) = ⊤ := by
  refine le_antisymm le_top (le_iInf fun y => le_iInf fun hy => ?_)
  exfalso
  obtain ⟨⟨d, l⟩, hd⟩ := y
  rcases hy with hy | hy <;> cases l <;> simp [alpha, beta, alphaD, betaD] at hy <;> split_ifs at hy

/-- **The value of a copy from local data.** The value computed at the host of an identifier from the
rotation list of the network of a level there, the records of the darts at the host and into it and
the values of `f` at the corners of both darts of its edges is `copyVal f` at the copy of a vertex
and `⊤` at every other identifier. -/
theorem locCopy_eq (a : Fin (n * (n * 21))) :
    locCopy (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (vo (hostOf a)) (vi (hostOf a))
      (idEquiv.symm a).2.2 ((S.levelNet hN).rotList a) =
      S.onCopies hN (fun u => S.copyVal f (S.vcopy u)) a := by
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
        rw [hw, S.copyVal_star]
        unfold locCopy
        rw [hw] at h0
        rw [h0]
        simp
      · unfold locCopy
        have hk : 1 ≤ (N.nameC (S.vcopy v)).2.2.val ∧ (N.nameC (S.vcopy v)).2.2.val < 5 :=
          ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (Fin.ext h), N.nameC_kind _⟩
        rw [S.extras_inl hN v]
        simp only [hk, h0, and_self, ↓reduceIte]
        rw [(S.levelPad hN).order_empty, List.append_nil, S.copyVal_lstR]
        apply le_antisymm
        · refine le_iInf fun x => le_iInf fun hx => iInf_le_of_le ((S.levelPad hN).ι (.inr x))
            (iInf_le_of_le (List.mem_map.2 ⟨x, hx, rfl⟩) (le_of_eq ?_))
          have hw : (S.name (.inl v)).1 = (S.nameD x).1 := by
            show (N.nameC (S.vcopy v)).1 = _
            rw [← S.tl_of_mem_lstR hx]; exact S.nameC_tl x
          rw [show idEquiv.symm ((S.levelPad hN).ι (.inr x)) = S.nameD x from idEquiv.symm_apply_apply _, hw]
          exact S.tokVal_nameD f vo vi hvo hvi x
        · refine le_iInf fun b => le_iInf fun hb => ?_
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
          refine iInf_le_of_le x (iInf_le_of_le hx (le_of_eq ?_))
          have hw : (S.name (.inl v)).1 = (S.nameD x).1 := by
            show (N.nameC (S.vcopy v)).1 = _
            rw [← S.tl_of_mem_lstR hx]; exact S.nameC_tl x
          rw [show idEquiv.symm ((S.levelPad hN).ι (.inr x)) = S.nameD x from idEquiv.symm_apply_apply _, hw]
          exact (S.tokVal_nameD f vo vi hvo hvi x).symm
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

end RData

end RotSystem

end SsspFlow
