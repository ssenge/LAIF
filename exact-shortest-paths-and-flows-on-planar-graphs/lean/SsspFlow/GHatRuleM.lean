import SsspFlow.GHatLevelConn

/-!
# Rule M as a local rule

`notes/GHAT_REPAIR.md`, (6), local phase, item 2. A node `v` holds the token `x` of level `ℓ` at the end of its
pair on the side of `v` (tail or head of the dart). Rule M matches it with the parent token `x̄` of the level before
(`RData.parent`: `x` if the dart of `x` was incised before, `(δ, 0)` otherwise), at the end of `x̄` on the same side
of the same dart (`RData.ruleEnd`). This end is a copy of `v` itself (`RData.owner_ruleEnd`), so `v` reads the label
of the level before at one of its own copies, and needs only the incision flag of the dart.

* `RData.ruleM_comp`: tokens of one component of `Ĝ_ℓ[E_R ∪ E_C]` are matched with copies of one component of
  `Ĝ_{ℓ-1}[E_R ∪ E_C]`.
* `RData.ruleM_lab`: hence they read the same label of the level before, for the labels of `RData.zlab` with
  token lengths `0`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section General

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S S' : G.RData)

/-- The end of the E_R edge of `x` at the tail (`true`) or at the head (`false`) of its dart. -/
def endAt (x : E × Lab) (b : Bool) : Copy G.Vertex E := if b then S.alpha x else S.beta x

theorem att_eq_endAt (x : E × Lab) : S.att x = S.endAt x (S.atTail x) := rfl

theorem owner_endAt (x : E × Lab) (b : Bool) :
    G.owner (S.endAt x b) = if b then G.tail x.1 else G.head x.1 := by
  cases b
  · exact S.owner_beta x
  · exact S.owner_alpha x

theorem isEnd_endAt (x : E × Lab) (b : Bool) : S.IsEnd x (S.endAt x b) := by
  cases b
  · exact .inr rfl
  · exact .inl rfl

theorem parent_fst (x : E × Lab) : (S'.parent x).1 = x.1 := by
  unfold parent
  split_ifs <;> rfl

/-- The copy that Rule M reads for the token `x`: the end of its parent on the side of the host of `x`. -/
def ruleEnd (x : E × Lab) : Copy G.Vertex E := S'.endAt (S'.parent x) (S.atTail x)

/-- **Rule M is local.** The copy that Rule M reads is a copy of the node that holds `x`. -/
theorem owner_ruleEnd (x : E × Lab) : G.owner (S.ruleEnd S' x) = G.owner (S.att x) := by
  rw [ruleEnd, owner_endAt, att_eq_endAt, owner_endAt, parent_fst]

/-- **Rule M on components.** Tokens of one component of the token graph of a level are matched with copies of one
component of `Ĝ[E_R ∪ E_C]` of the level before. -/
theorem ruleM_comp (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) {x y : S.Tok}
    (h : Relation.ReflTransGen S.TG (S.piece x) (S.piece y)) :
    Relation.ReflTransGen S'.ERC (S.ruleEnd S' x.1) (S.ruleEnd S' y.1) := by
  let a : S'.EndCopy := ⟨S.ruleEnd S' x.1, S.parentTok S' hinc x, S'.isEnd_endAt _ _⟩
  let b : S'.EndCopy := ⟨S.ruleEnd S' y.1, S.parentTok S' hinc y, S'.isEnd_endAt _ _⟩
  have ha : S'.pieceOf a = S.parentPiece S' hinc hcut (S.piece x) := S'.pieceOf_eq _ (S'.isEnd_endAt _ _)
  have hb : S'.pieceOf b = S.parentPiece S' hinc hcut (S.piece y) := S'.pieceOf_eq _ (S'.isEnd_endAt _ _)
  refine (S'.erc_comp_iff a b).2 ?_
  rw [ha, hb]
  exact S.parent_comp S' hinc hcut h

end General

variable {n : ℕ} {N : Net (Fin n)} (S S' : N.toRot.RData) (M : ℕ) (φ : S'.hRot.Vertex → ℕ)

/-- **Rule M with labels.** With the labels of the level before for token lengths `0`, tokens of one component of
the token graph of a level read the same label at the copies that Rule M names. -/
theorem ruleM_lab (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) (hφ : ∀ u, φ u < M)
    (hinj : Function.Injective φ) {x y : S.Tok} (h : Relation.ReflTransGen S.TG (S.piece x) (S.piece y))
    {u w : S'.hRot.Vertex} (hu : S'.vcopy u = S.ruleEnd S' x.1) (hw : S'.vcopy w = S.ruleEnd S' y.1) :
    S'.zlab (fun _ => 0) M φ u = S'.zlab (fun _ => 0) M φ w := by
  rw [S'.zlab_eq_iff (fun _ => 0) M φ (fun _ => Or.inl rfl) (fun _ => rfl) hφ hinj, S'.zr_zero, hu, hw]
  exact S.ruleM_comp S' hinc hcut h

end RData

end RotSystem

end SsspFlow
