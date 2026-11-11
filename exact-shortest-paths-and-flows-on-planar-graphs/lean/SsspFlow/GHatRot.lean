import SsspFlow.GHat
import SsspFlow.ListRot
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# The rotation of the copies (Table R)

The full repaired graph `H⁺` of `notes/GHAT_REPAIR.md`, property (3): Definition R with a rim edge
at both ends of every edge of `G`, with the copies `X(c)` of the cut corners and the rim edges at
them rerouted. Its edges (`HE`) are the spokes `σ(v)D(c)`, the rims, the tokens (E_R edges) and the
short edges `D(c)L(c)`, `D(c)R(c)`, `D(c)X(c)`. The rim across a dart `d` at its tail joins the ends
`α_D(τ d)` and `β_D(d)`, so a rim that meets a cut corner on the side of its moved token ends at
`X(c)`. The repaired graph of a level keeps those rims that are E_C edges.

The lists of Table R at the copies (`lst`): the spokes at `σ(v)` in the rotation of `G`; at `D(c)`
the spoke, the rim across `in(c)`, the tokens of `in(c)` with `L(c)`, the tokens of `out(c)` with
`R(c)`, and the rim across `out(c)`, where the entry of a moved token is the edge to `X(c)`; and the
two or three edges at `L(c)`, `R(c)` and `X(c)`. Option (ii) is used exactly for an incised dart
whose tail corner is a cut corner in mode R.

* `HD`: the darts, an edge with a direction.
* `tl`: the copy at which a dart starts.
* `listData`: every dart lies in the list of its tail, and the lists have no repetitions, so the
  lists define a rotation system `hRot` (`ListData.toRot`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

universe u

instance : Fintype Lab where
  elems := {.zero, .one, .two}
  complete x := by cases x <;> simp

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E}

/-- The darts at a vertex of `G` in rotation order, starting at a representative. -/
noncomputable def starList (G : RotSystem E) (v : G.Vertex) : List E :=
  if G.rot.toList (Quotient.out v) = [] then [Quotient.out v] else G.rot.toList (Quotient.out v)

theorem tail_out (v : G.Vertex) : G.tail (Quotient.out v) = v := Quotient.out_eq v

theorem mem_starList {v : G.Vertex} {c : E} : c ∈ G.starList v ↔ G.tail c = v := by
  have hsc : G.tail c = v ↔ G.rot.SameCycle (Quotient.out v) c := by
    conv_lhs => rw [← tail_out v]
    show Quotient.mk _ c = Quotient.mk _ _ ↔ _
    rw [Quotient.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hsc]
  unfold starList
  split_ifs with h
  · rw [Equiv.Perm.toList_eq_nil_iff, Equiv.Perm.mem_support, not_not] at h
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact Equiv.Perm.SameCycle.refl _ _
    · intro hs
      obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
      rw [← hn, Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h]
  · rw [Equiv.Perm.mem_toList_iff]
    have hs : Quotient.out v ∈ G.rot.support := by
      by_contra hn
      exact h (Equiv.Perm.toList_eq_nil_iff.2 hn)
    exact ⟨fun h' => h'.1, fun h' => ⟨h', hs⟩⟩

theorem starList_nodup (v : G.Vertex) : (G.starList v).Nodup := by
  unfold starList
  split_ifs
  · exact List.nodup_singleton _
  · exact Equiv.Perm.nodup_toList _ _

/-- The next dart in the list of a vertex is the next dart in the rotation. -/
theorem formPerm_starList {v : G.Vertex} {c : E} (hc : c ∈ G.starList v) :
    (G.starList v).formPerm c = G.rot c := by
  by_cases h : G.rot.toList (Quotient.out v) = []
  · simp only [starList, h, if_true, List.mem_singleton] at hc ⊢
    subst hc
    rw [Equiv.Perm.toList_eq_nil_iff, Equiv.Perm.mem_support, not_not] at h
    simp [h]
  · simp only [starList, h, if_false] at hc ⊢
    rw [List.formPerm_apply_mem_eq_next (Equiv.Perm.nodup_toList _ _) _ hc,
      Equiv.Perm.next_toList_eq_apply _ _ _ hc]

namespace RData

variable (S : G.RData)

/-- The edges of the full repaired graph: spokes `σ(v)D(c)`, the rim across each dart at its tail,
the tokens, and the edges `D(c)L(c)` (named by the incised dart `in(c)`), `D(c)R(c)` (named by the
incised dart `out(c)`) and `D(c)X(c)`. -/
inductive HE : Type u
  | sp (c : E)
  | rim (d : E)
  | tok (x : S.Tok)
  | lsp (a : {a : E // a ∈ S.inc})
  | rsp (b : {b : E // b ∈ S.inc})
  | xsp (c : {c : E // c ∈ S.cut})

/-- The edges as a sum type. -/
def heEquiv : S.HE ≃ E ⊕ E ⊕ S.Tok ⊕ {a : E // a ∈ S.inc} ⊕ {b : E // b ∈ S.inc} ⊕
    {c : E // c ∈ S.cut} where
  toFun
    | .sp c => .inl c
    | .rim d => .inr (.inl d)
    | .tok x => .inr (.inr (.inl x))
    | .lsp a => .inr (.inr (.inr (.inl a)))
    | .rsp b => .inr (.inr (.inr (.inr (.inl b))))
    | .xsp c => .inr (.inr (.inr (.inr (.inr c))))
  invFun
    | .inl c => .sp c
    | .inr (.inl d) => .rim d
    | .inr (.inr (.inl x)) => .tok x
    | .inr (.inr (.inr (.inl a))) => .lsp a
    | .inr (.inr (.inr (.inr (.inl b)))) => .rsp b
    | .inr (.inr (.inr (.inr (.inr c)))) => .xsp c
  left_inv e := by cases e <;> rfl
  right_inv s := by rcases s with c | d | x | a | b | c <;> rfl

noncomputable instance : DecidableEq S.HE := Classical.decEq _

noncomputable instance : Fintype S.HE := by classical exact Fintype.ofEquiv _ S.heEquiv.symm

/-- The darts: an edge, read from its first end (`false`) or from its second end (`true`). -/
abbrev HD : Type u := S.HE × Bool

/-- The two ends of an edge. -/
def ends : S.HE → Copy G.Vertex E × Copy G.Vertex E
  | .sp c => (.star (G.tail c), .dc c)
  | .rim d => (S.alphaD (G.tailCorner d), S.betaD d)
  | .tok x => (S.alpha x.1, S.beta x.1)
  | .lsp a => (.dc (G.headCorner a.1), .lc (G.headCorner a.1))
  | .rsp b => (.dc (G.tailCorner b.1), .rc (G.tailCorner b.1))
  | .xsp c => (.dc c.1, .xc c.1)

/-- The copy at which a dart starts. -/
def tl (x : S.HD) : Copy G.Vertex E := if x.2 then (S.ends x.1).2 else (S.ends x.1).1

/-- The reverse dart. -/
def hrev (x : S.HD) : S.HD := (x.1, !x.2)

variable {S} in
/-- A dart from the first end. -/
abbrev fw (e : S.HE) : S.HD := (e, false)

variable {S} in
/-- A dart from the second end. -/
abbrev bw (e : S.HE) : S.HD := (e, true)

/-- The corner `c` is a cut corner in mode L: its in-token moves to `X(c)`. -/
def MovA (c : E) : Prop := c ∈ S.cut ∧ S.modeL c = true

/-- The corner `c` is a cut corner in mode R: its out-token moves to `X(c)`. -/
def MovB (c : E) : Prop := c ∈ S.cut ∧ S.modeL c = false

instance (c : E) : Decidable (S.MovA c) := by unfold MovA; infer_instance
instance (c : E) : Decidable (S.MovB c) := by unfold MovB; infer_instance

/-- Option (ii): the tail corner of the dart is a cut corner in mode R. -/
def Opt (d : E) : Prop := S.MovB (G.tailCorner d)

instance (d : E) : Decidable (S.Opt d) := by unfold Opt; infer_instance

theorem isTok_zero {d : E} (h : d ∉ S.inc) : S.IsTok (d, .zero) := by simp [IsTok, h]
theorem isTok_one {d : E} (h : d ∈ S.inc) : S.IsTok (d, .one) := by simp [IsTok, h]
theorem isTok_two {d : E} (h : d ∈ S.inc) : S.IsTok (d, .two) := by simp [IsTok, h]

theorem cut_of_movA {c : E} (h : S.MovA c) : c ∈ S.cut := h.1
theorem cut_of_movB {c : E} (h : S.MovB c) : c ∈ S.cut := h.1

/-- The entry of the in-token at `D(c)`: the edge to `X(c)` if it moves, else the token ending
there. -/
def entA (c : E) (l : Lab) (hl : S.IsTok (G.rev c, l)) : S.HD :=
  if h : S.MovA c then fw (HE.xsp ⟨c, S.cut_of_movA h⟩) else bw (HE.tok ⟨(G.rev c, l), hl⟩)

/-- The entry of the out-token at `D(c)`. -/
def entB (c : E) (l : Lab) (hl : S.IsTok (G.rot c, l)) : S.HD :=
  if h : S.MovB c then fw (HE.xsp ⟨c, S.cut_of_movB h⟩) else fw (HE.tok ⟨(G.rot c, l), hl⟩)

/-- The entries for the in-dart `a = in(c)` at `D(c)`. -/
def segA (c : E) : List S.HD :=
  if ha : G.rev c ∈ S.inc then
    if S.Opt (G.rev c) then [fw (HE.lsp ⟨G.rev c, ha⟩), S.entA c .two (S.isTok_two ha)]
    else [S.entA c .two (S.isTok_two ha), fw (HE.lsp ⟨G.rev c, ha⟩)]
  else [S.entA c .zero (S.isTok_zero ha)]

/-- The entries for the out-dart `b = out(c)` at `D(c)`. -/
def segB (c : E) : List S.HD :=
  if hb : G.rot c ∈ S.inc then
    if S.MovB c then [fw (HE.rsp ⟨G.rot c, hb⟩), S.entB c .one (S.isTok_one hb)]
    else [S.entB c .one (S.isTok_one hb), fw (HE.rsp ⟨G.rot c, hb⟩)]
  else [S.entB c .zero (S.isTok_zero hb)]

/-- The list of Table R at `D(c)`. -/
def dList (c : E) : List S.HD :=
  [bw (HE.sp c)] ++ (if S.MovA c then [] else [bw (HE.rim c)]) ++ S.segA c ++ S.segB c ++
    (if S.MovB c then [] else [fw (HE.rim (G.rot c))])

/-- The list at `L(c)`. -/
def lList (c : E) : List S.HD :=
  if ha : G.rev c ∈ S.inc then [bw (HE.lsp ⟨G.rev c, ha⟩), bw (HE.tok ⟨(G.rev c, .one), S.isTok_one ha⟩)]
  else []

/-- The list at `R(c)`. -/
def rList (c : E) : List S.HD :=
  if hb : G.rot c ∈ S.inc then [bw (HE.rsp ⟨G.rot c, hb⟩), fw (HE.tok ⟨(G.rot c, .two), S.isTok_two hb⟩)]
  else []

/-- The list at `X(c)`: in mode L the edge to `D(c)`, the rerouted rim and the moved in-token; in
mode R the edge to `D(c)`, the moved out-token and the rerouted rim. -/
def xList (c : E) : List S.HD :=
  if hc : c ∈ S.cut then
    if S.modeL c then
      [bw (HE.xsp ⟨c, hc⟩), bw (HE.rim c), bw (HE.tok ⟨(G.rev c, S.lastLab (G.rev c)), S.isTok_last _⟩)]
    else
      [bw (HE.xsp ⟨c, hc⟩), fw (HE.tok ⟨(G.rot c, S.firstLab (G.rot c)), S.isTok_first _⟩),
        fw (HE.rim (G.rot c))]
  else []

/-- The lists of Table R. -/
noncomputable def lst : Copy G.Vertex E → List S.HD
  | .star v => (G.starList v).map fun c => fw (HE.sp c)
  | .dc c => S.dList c
  | .lc c => S.lList c
  | .rc c => S.rList c
  | .xc c => S.xList c

/-! ### Every dart lies in the list of its tail -/

@[simp] theorem tl_fw (e : S.HE) : S.tl (fw e) = (S.ends e).1 := rfl
@[simp] theorem tl_bw (e : S.HE) : S.tl (bw e) = (S.ends e).2 := rfl

theorem not_movB_of_movA {c : E} (h : S.MovA c) : ¬ S.MovB c := by
  unfold MovA at h; unfold MovB; simp [h.2]

theorem alphaD_movB {c : E} (h : S.MovB c) : S.alphaD c = .xc c := if_pos h
theorem alphaD_not {c : E} (h : ¬ S.MovB c) : S.alphaD c = .dc c := if_neg h
theorem betaD_movA {c : E} (h : S.MovA c) : S.betaD c = .xc c := if_pos h
theorem betaD_not {c : E} (h : ¬ S.MovA c) : S.betaD c = .dc c := if_neg h

@[simp] theorem tailCorner_rot' (c : E) : G.tailCorner (G.rot c) = c := G.rot.symm_apply_apply c
@[simp] theorem headCorner_rev' (c : E) : G.headCorner (G.rev c) = c := G.rev_rev c

theorem alpha_first (d : E) : S.alpha (d, S.firstLab d) = S.alphaD (G.tailCorner d) := by
  unfold firstLab; split_ifs <;> rfl

theorem beta_last (d : E) : S.beta (d, S.lastLab d) = S.betaD (G.headCorner d) := by
  unfold lastLab; split_ifs <;> rfl

/-- Each dart in a list starts at that copy. -/
theorem tl_of_mem (v : Copy G.Vertex E) : ∀ x ∈ S.lst v, S.tl x = v := by
  cases v with
  | star v => simp [lst, ends, mem_starList]
  | dc c =>
    simp only [lst, dList, segA, segB, entA, entB]
    split_ifs <;> first
      | exact absurd ‹S.MovB c› (S.not_movB_of_movA ‹S.MovA c›)
      | simp_all [ends, alpha, beta, alphaD_not, betaD_not, alphaD_movB, betaD_movA]
  | lc c =>
    simp only [lst, lList]
    split_ifs <;> simp_all [ends, beta]
  | rc c =>
    simp only [lst, rList]
    split_ifs <;> simp_all [ends, alpha]
  | xc c =>
    simp only [lst, xList]
    split_ifs with h1 h2 <;> simp_all [ends, alpha_first, beta_last, alphaD, betaD]

/-- Each list has no repetitions. -/
theorem lst_nodup (v : Copy G.Vertex E) : (S.lst v).Nodup := by
  cases v with
  | star v =>
    simp only [lst]
    exact (G.starList_nodup v).map fun a b h => by simpa using h
  | dc c =>
    simp only [lst, dList, segA, segB, entA, entB]
    split_ifs <;> first
      | exact absurd ‹S.MovB c› (S.not_movB_of_movA ‹S.MovA c›)
      | simp_all
  | lc c =>
    simp only [lst, lList]
    split_ifs <;> simp
  | rc c =>
    simp only [lst, rList]
    split_ifs <;> simp
  | xc c =>
    simp only [lst, xList]
    split_ifs <;> simp

theorem rot_ex (d : E) : ∃ c, d = G.rot c := ⟨G.rot.symm d, (G.rot.apply_symm_apply d).symm⟩

theorem rev_ex (d : E) : ∃ c, d = G.rev c := ⟨G.rev d, (G.rev_rev d).symm⟩

/-- Each dart lies in the list of its tail. -/
theorem mem_lst_tl (x : S.HD) : x ∈ S.lst (S.tl x) := by
  obtain ⟨e, b⟩ := x
  cases e with
  | sp c => cases b <;> simp [ends, lst, dList, mem_starList]
  | rim d =>
    cases b
    · obtain ⟨c, rfl⟩ := rot_ex (G := G) d
      by_cases h : S.MovB c
      · simp [ends, S.alphaD_movB h, lst, xList, h.1, show S.modeL c = false from h.2]
      · simp [ends, S.alphaD_not h, lst, dList, h]
    · by_cases h : S.MovA d
      · simp [ends, S.betaD_movA h, lst, xList, h.1, show S.modeL d = true from h.2]
      · simp [ends, S.betaD_not h, lst, dList, h]
  | tok x =>
    obtain ⟨⟨d, l⟩, hx⟩ := x
    cases b
    · obtain ⟨c, rfl⟩ := rot_ex (G := G) d
      cases l with
      | two =>
        have hm : G.rot c ∈ S.inc := by simpa [IsTok] using hx
        simp [ends, alpha, lst, rList, hm]
      | _ =>
        have hm := hx
        simp [IsTok] at hm
        by_cases h : S.MovB c
        · simp [ends, alpha, S.alphaD_movB h, lst, xList, h.1, show S.modeL c = false from h.2,
            firstLab, hm]
        · simp [ends, alpha, S.alphaD_not h, lst, dList, segB, entB, hm, h]
    · obtain ⟨c, rfl⟩ := rev_ex (G := G) d
      cases l with
      | one =>
        have hm : G.rev c ∈ S.inc := by simpa [IsTok] using hx
        simp [ends, beta, lst, lList, hm]
      | _ =>
        have hm := hx
        simp [IsTok] at hm
        by_cases h : S.MovA c
        · simp [ends, beta, S.betaD_movA h, lst, xList, h.1, show S.modeL c = true from h.2,
            lastLab, hm]
        · simp [ends, beta, S.betaD_not h, lst, dList, segA, entA, hm, h]
          try split_ifs <;> simp
  | lsp a =>
    obtain ⟨a, ha⟩ := a
    obtain ⟨c, rfl⟩ := rev_ex (G := G) a
    cases b
    · simp [ends, lst, dList, segA, ha]
      split_ifs <;> simp
    · simp [ends, lst, lList, ha]
  | rsp b' =>
    obtain ⟨b', hb⟩ := b'
    obtain ⟨c, rfl⟩ := rot_ex (G := G) b'
    cases b
    · simp [ends, lst, dList, segB, hb]
      split_ifs <;> simp
    · simp [ends, lst, rList, hb]
  | xsp c =>
    obtain ⟨c, hc⟩ := c
    cases b
    · simp only [tl_fw, ends, lst, dList, segA, segB, entA, entB]
      by_cases hA : S.MovA c
      · have hB := S.not_movB_of_movA hA
        split_ifs <;> simp_all
      · have hB : S.MovB c := ⟨hc, by simpa [MovA, hc] using hA⟩
        split_ifs <;> simp_all
    · simp [ends, lst, xList, hc]
      cases S.modeL c <;> simp

/-- The lists of Table R as list data. -/
noncomputable def listData : ListData S.HD (Copy G.Vertex E) where
  rev := S.hrev
  rev_rev x := by simp [hrev]
  rev_ne x := by simp [hrev, Prod.ext_iff]
  tl := S.tl
  lst := S.lst
  nodup := S.lst_nodup
  mem_iff v x := ⟨fun h => S.tl_of_mem v x h, fun h => h ▸ S.mem_lst_tl x⟩

/-- The rotation system of the full repaired graph. -/
noncomputable def hRot : RotSystem S.HD := S.listData.toRot

end RData

end RotSystem

end SsspFlow
