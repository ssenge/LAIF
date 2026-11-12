import SsspFlow.GHatRun

/-!
# The phases of the local computation (property (6))

The global phase runs connectivity on `Ĝ_ℓ[E_R]` and on `Ĝ_ℓ[E_R ∪ E_C]`.

* `RData.er_comp_iff`: two copies on E_R edges are joined by E_R edges exactly when they lie on the
  path of one piece. So the components of `Ĝ_ℓ[E_R]`, apart from the star centres, are the paths of
  the pieces.
* `RData.erc_comp_iff`: two such copies are joined by E_R and E_C edges exactly when their pieces
  are joined in the token graph. So the components of `Ĝ_ℓ[E_R ∪ E_C]` are those of the token graph,
  which are those of the split (`RData.tg_comp_iff`), and by Lemma N those are the annuli.
* `RData.owner_end`: every copy on the path of a piece is a copy of an end of a dart of a token of
  that piece, so the leader copy of a piece is a copy of a vertex of the piece.

Claim 3, second part. The parent of the other token of a pair is the other token of the parent pair
(`RData.parent_partner`), so an arc of the token graph maps to an arc of the token graph of the
level before (`RData.parent_tg`), and pieces joined at one level have parents joined at the level
before (`RData.parent_comp`): a component of a level lies in one component of the level before. On a
run, the incisions grow with the level and the cut corners stay the same (`CutPath.Run.inc_mono`,
`CutPath.Run.cut_eq`), so this holds for every two consecutive levels of a run
(`CutPath.Run.parent_comp`).
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

noncomputable section

namespace RotSystem

namespace RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- An E_C edge between two copies: the ends at the host of the two tokens of a pair. -/
def EC (a b : Copy G.Vertex E) : Prop := ∃ x : S.Tok, S.att x.1 = a ∧ S.att (G.partner x.1) = b

/-- An E_R or E_C edge. -/
def ERC (a b : Copy G.Vertex E) : Prop := S.ER a b ∨ S.EC a b

/-- An arc of the token graph between two pieces. -/
def TG (f g : S.Piece) : Prop := Nonempty (S.DArc f g)

theorem endCopy_of_er {a b : Copy G.Vertex E} (h : S.ER a b) :
    ∃ x : S.Tok, S.IsEnd x.1 a ∧ S.IsEnd x.1 b := by
  obtain ⟨x, hx | hx⟩ := h
  · exact ⟨x, .inl hx.1, .inr hx.2⟩
  · exact ⟨x, .inr hx.1, .inl hx.2⟩

/-- **The components of `Ĝ_ℓ[E_R]` are the paths of the pieces.** -/
theorem er_comp_iff (a b : S.EndCopy) :
    Relation.ReflTransGen S.ER a.1 b.1 ↔ S.pieceOf a = S.pieceOf b := by
  refine ⟨fun h => ?_, S.ring_conn a b⟩
  have key : ∀ c, Relation.ReflTransGen S.ER a.1 c →
      ∃ hc : ∃ x : S.Tok, S.IsEnd x.1 c, S.pieceOf ⟨c, hc⟩ = S.pieceOf a := by
    intro c hc
    induction hc with
    | refl => exact ⟨a.2, rfl⟩
    | tail _ hcd ih =>
      obtain ⟨hc, ih⟩ := ih
      obtain ⟨x, h1, h2⟩ := S.endCopy_of_er hcd
      exact ⟨⟨x, h2⟩, by rw [S.pieceOf_eq ⟨_, ⟨x, h2⟩⟩ h2, ← S.pieceOf_eq ⟨_, hc⟩ h1, ih]⟩
  obtain ⟨hb, e⟩ := key b.1 h
  exact e.symm.trans (congrArg S.pieceOf (Subtype.ext rfl))

/-- **The components of `Ĝ_ℓ[E_R ∪ E_C]` are those of the token graph.** -/
theorem erc_comp_iff (a b : S.EndCopy) :
    Relation.ReflTransGen S.ERC a.1 b.1 ↔ Relation.ReflTransGen S.TG (S.pieceOf a) (S.pieceOf b) := by
  constructor
  · intro h
    have key : ∀ c, Relation.ReflTransGen S.ERC a.1 c →
        ∃ hc : ∃ x : S.Tok, S.IsEnd x.1 c,
          Relation.ReflTransGen S.TG (S.pieceOf a) (S.pieceOf ⟨c, hc⟩) := by
      intro c hc
      induction hc with
      | refl => exact ⟨a.2, .refl⟩
      | tail _ hcd ih =>
        obtain ⟨hc, ih⟩ := ih
        rcases hcd with hcd | ⟨x, rfl, rfl⟩
        · obtain ⟨x, h1, h2⟩ := S.endCopy_of_er hcd
          exact ⟨⟨x, h2⟩, by rwa [S.pieceOf_eq ⟨_, ⟨x, h2⟩⟩ h2, ← S.pieceOf_eq ⟨_, hc⟩ h1]⟩
        · refine ⟨⟨S.partnerTok x, S.isEnd_att _⟩, ih.tail ?_⟩
          have e2 : S.pieceOf ⟨S.att (G.partner x.1), S.partnerTok x, S.isEnd_att _⟩ =
              S.piece (S.partnerTok x) := S.pieceOf_eq _ (S.isEnd_att (S.partnerTok x).1)
          rw [S.pieceOf_eq ⟨_, hc⟩ (S.isEnd_att x.1), e2]
          exact ⟨⟨x, rfl, rfl⟩⟩
    obtain ⟨hb, e⟩ := key b.1 h
    exact (congrArg S.pieceOf (Subtype.ext rfl : (⟨b.1, hb⟩ : S.EndCopy) = b)) ▸ e
  · intro h
    have lift : ∀ {c d : Copy G.Vertex E}, Relation.ReflTransGen S.ER c d →
        Relation.ReflTransGen S.ERC c d := by
      intro c d h'
      induction h' with
      | refl => exact .refl
      | tail _ h'' ih => exact ih.tail (Or.inl h'')
    have key : ∀ g, Relation.ReflTransGen S.TG (S.pieceOf a) g →
        ∀ b : S.EndCopy, S.pieceOf b = g → Relation.ReflTransGen S.ERC a.1 b.1 := by
      intro g hg
      induction hg with
      | refl => exact fun b hb => lift (S.ring_conn a b hb.symm)
      | tail _ hfg ih =>
        obtain ⟨x, hx1, hx2⟩ := hfg
        intro b hb
        have h1 := ih ⟨S.att x.1, x, S.isEnd_att _⟩ (by rw [S.pieceOf_att, hx1])
        have h2 : S.ERC (S.att x.1) (S.att (G.partner x.1)) := .inr ⟨x, rfl, rfl⟩
        have h3 := S.ring_conn ⟨S.att (S.partnerTok x).1, S.partnerTok x, S.isEnd_att _⟩ b
          (by rw [S.pieceOf_att, hx2, hb])
        exact (h1.tail h2).trans (lift h3)
    exact key _ h b rfl

/-- **The leader copy of a piece is a copy of a vertex of the piece.** -/
theorem owner_end (a : S.EndCopy) :
    ∃ x : S.Tok, S.piece x = S.pieceOf a ∧
      (G.owner a.1 = G.tail x.1.1 ∨ G.owner a.1 = G.head x.1.1) := by
  obtain ⟨x, hx⟩ := a.2
  refine ⟨x, (S.pieceOf_eq a hx).symm, ?_⟩
  rcases hx with h | h
  · exact .inl (h ▸ S.owner_alpha x.1)
  · exact .inr (h ▸ S.owner_beta x.1)

/-- **The components of the token graph are those of the split.** Two pieces are joined in the
token graph exactly when a walk of the split joins their vertices. -/
theorem tg_comp_iff (f h : S.Piece) :
    Relation.ReflTransGen S.TG f h ↔
      ∃ p : List (E × Bool), S.dualSplit.IsWalk (S.vertexEquiv f) p (S.vertexEquiv h) := by
  constructor
  · intro hfh
    have hw : ∀ {f h : S.Piece}, Relation.ReflTransGen S.TG f h →
        Nonempty (FaceDisjoint.Walk S.DArc f h) := by
      intro f h hfh
      induction hfh using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨.nil _⟩
      | head hab _ ih =>
        obtain ⟨x⟩ := hab
        obtain ⟨P⟩ := ih
        exact ⟨.cons x P⟩
    obtain ⟨P⟩ := hw hfh
    obtain ⟨p, hp, -⟩ := S.split_walk (fun _ => 0) (fun _ => rfl) P
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    obtain ⟨P, -⟩ := S.dwalk_of_split (fun _ => 0) (fun _ => rfl) p hp
    have hr : ∀ {f h : S.Piece}, FaceDisjoint.Walk S.DArc f h → Relation.ReflTransGen S.TG f h := by
      intro f h P
      induction P with
      | nil => exact .refl
      | cons x _ ih => exact .head ⟨x⟩ ih
    exact hr P

variable (S' : G.RData)

/-- The parent of the other token of a pair is the other token of the parent pair. -/
theorem parent_partner (x : E × Lab) : S'.parent (G.partner x) = G.partner (S'.parent x) := by
  obtain ⟨d, l⟩ := x
  unfold parent partner
  by_cases h : d ∈ S'.inc
  · simp [h, S'.inc_rev]
  · simp [h, S'.inc_rev, Lab.swap]

theorem parentTok_partnerTok (hinc : S'.inc ⊆ S.inc) (x : S.Tok) :
    S.parentTok S' hinc (S.partnerTok x) = S'.partnerTok (S.parentTok S' hinc x) :=
  Subtype.ext (S'.parent_partner x.1)

/-- An arc of the token graph maps to an arc of the token graph of the level before. -/
theorem parent_tg (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) {f g : S.Piece}
    (h : S.TG f g) : S'.TG (S.parentPiece S' hinc hcut f) (S.parentPiece S' hinc hcut g) := by
  obtain ⟨x, rfl, rfl⟩ := h
  refine ⟨⟨S.parentTok S' hinc x, rfl, ?_⟩⟩
  rw [← S.parentTok_partnerTok S' hinc]
  rfl

/-- **Claim 3, second part.** Pieces joined in the token graph have parents joined in the token
graph of the level before: a component of a level lies in one component of the level before. -/
theorem parent_comp (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) {f g : S.Piece}
    (h : Relation.ReflTransGen S.TG f g) :
    Relation.ReflTransGen S'.TG (S.parentPiece S' hinc hcut f) (S.parentPiece S' hinc hcut g) := by
  induction h with
  | refl => exact .refl
  | tail _ hfg ih => exact ih.tail (S.parent_tg S' hinc hcut hfg)

end RData

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}
variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- The incisions of a run grow with the level. -/
theorem Run.steps_mono : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), r.steps ℓ ⊆ r.steps (ℓ + 1)
  | _, _, _, _, .leaf .., _ => by simp [Run.steps]
  | _, _, _, _, .node .., 0 => by simp [Run.steps]
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1 => by
    simp only [Run.steps]
    exact Finset.union_subset_union (Finset.union_subset_union le_rfl (SideA.steps_mono left ℓ))
      (SideB.steps_mono right ℓ)
theorem SideA.steps_mono : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      s.steps ℓ ⊆ s.steps (ℓ + 1)
  | _, _, _, _, _, _, _, .overlap .., _ => by simp [SideA.steps]
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => by
    simp only [SideA.steps]
    exact Run.steps_mono r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => by simp [SideA.steps]
theorem SideB.steps_mono : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      s.steps ℓ ⊆ s.steps (ℓ + 1)
  | _, _, _, _, _, _, _, .overlap .., _ => by simp [SideB.steps]
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => by
    simp only [SideB.steps]
    exact Run.steps_mono r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => by simp [SideB.steps]
end

end CutPath

section Tokens

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} {C : G.dual.CutPath}
  {g : E → ℝ≥0∞} {hR : G.dual.Planar} {hC : G.dual.Connected} {hg : ∀ x, g (G.dual.rev x) = g x}

namespace CutPath

variable {Γ : Finset (E × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k) (ℓ : ℕ)
  (modeL hostT modeL' hostT' : E → Bool)
  (hhost : ∀ d, (d, false) ∉ Γ ∪ r.steps ℓ → hostT (G.rev d) = !hostT d)
  (hhost' : ∀ d, (d, false) ∉ Γ ∪ r.steps (ℓ + 1) → hostT' (G.rev d) = !hostT' d)

/-- The incised darts grow from one level to the next. -/
theorem Run.inc_mono :
    (r.data ℓ modeL hostT hhost).inc ⊆ (r.data (ℓ + 1) modeL' hostT' hhost').inc := by
  intro d hd
  simp only [Run.data, RData.ofCorners, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union] at hd ⊢
  rcases hd with h | h
  · exact .inl h
  · exact .inr (r.steps_mono ℓ h)

/-- The cut corners are the same at every level. -/
theorem Run.cut_eq :
    (r.data ℓ modeL hostT hhost).cut = (r.data (ℓ + 1) modeL' hostT' hhost').cut := by
  ext c
  simp only [Run.data, RData.ofCorners, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, r.not_true_steps, or_false]

/-- **Claim 3 on a run.** Pieces of a level joined in its token graph have parents joined in the
token graph of the level before. -/
theorem Run.parent_comp {f f' : (r.data (ℓ + 1) modeL' hostT' hhost').Piece}
    (h : Relation.ReflTransGen (r.data (ℓ + 1) modeL' hostT' hhost').TG f f') :
    Relation.ReflTransGen (r.data ℓ modeL hostT hhost).TG
      ((r.data (ℓ + 1) modeL' hostT' hhost').parentPiece _
        (r.inc_mono ℓ modeL hostT modeL' hostT' hhost hhost')
        (r.cut_eq ℓ modeL hostT modeL' hostT' hhost hhost') f)
      ((r.data (ℓ + 1) modeL' hostT' hhost').parentPiece _
        (r.inc_mono ℓ modeL hostT modeL' hostT' hhost hhost')
        (r.cut_eq ℓ modeL hostT modeL' hostT' hhost hhost') f') :=
  RData.parent_comp _ _ _ _ h

end CutPath

end Tokens

end RotSystem

end

end SsspFlow
