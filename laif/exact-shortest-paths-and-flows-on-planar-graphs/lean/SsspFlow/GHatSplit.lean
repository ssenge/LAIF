import SsspFlow.GHatProps
import SsspFlow.Live

/-!
# The pieces as the vertices of a split

The split model of the incisions (`Incision.lean` to `Run.lean`) cuts a doubled map at a set of
corners. Here the map is the dual `G.dual`, whose rotation at a face runs along the reversed
darts of its walk: `(rev δ, false)` and `(rev δ, true)` are the two copies of the dart `δ` in
`G.dual.double`, the digon corner `(rev δ, false)` lies between them, and the corner
`(rev δ, true)` is the corner `η δ` between `δ` and the next dart of its face. For the data `S`
of Definition R, the corners of the cut are the digon corners `(d, false)` of the incised darts
and the corners `(c, true)` of the cut corners (`RData.Γ`, `RData.dualSplit`).

* `RotSystem.tokDart` is the dart at which a token starts, and `RData.tokOf` the token at a dart.
* `RData.piece_eq_iff`: two tokens lie in one piece exactly when their darts lie at one vertex of
  the split. So the pieces are the vertices of the split (`RData.vertexEquiv`).
* `RData.tokOf_rev`: the reverse of a dart belongs to the partner token, so the dart of a token
  runs from the vertex of its piece to the vertex of the piece of its partner
  (`RData.head_tokDart`). The pairs are the edges of the split, the pair of an unincised edge as
  the two copies of the edge.
* `RData.ddist_eq`: for weights that agree on the two darts of an edge, the distances of the
  token graph are the distances of the split.
* `RData.ofCorners`: every set of corners of the doubled dual that holds both digon corners of
  each of its edges is the set `Γ` of some data.
* `RotSystem.walkDist_split_split`: more corners out of the reach of a vertex do not change the
  distances from it.
* `RData.ddist_live`, `RData.gdist_live`, `RData.ddist_live_ofCorners`: the distance `λ_t` of a
  live annulus is the distance in the token graph between the pieces at the corners `κ0(t)` and
  `κ1(t)`, and the distance in `Ĝ_ℓ` between copies on their paths when it is below `M`.

This is Lemma N of `notes/GHAT_REPAIR.md` in the split model: the node-parts are read as runs of
face walks, and a live annulus of the recursion is a component of the token graph.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

universe u

section Local

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D) {Γ Γ' : Finset D}

/-- If no corner of `Γ' \ Γ` lies at the vertex of `u` in the split at `Γ`, the two splits have
the same darts at the vertex of `u`. -/
theorem split_tail_eq_iff (h : Γ ⊆ Γ') {u : D}
    (hu : ∀ w ∈ Γ', w ∉ Γ → (R.split Γ).tail w ≠ (R.split Γ).tail u) (x : D) :
    (R.split Γ').tail u = (R.split Γ').tail x ↔ (R.split Γ).tail u = (R.split Γ).tail x := by
  rw [tail_eq_iff, tail_eq_iff]
  exact R.fconnect_split_split_iff h fun w hw hwΓ hc =>
    hu w hw hwΓ (((R.split Γ).tail_eq_iff u w).2 hc).symm

/-- If no walk of the split at `Γ` from the vertex of `z` reaches a corner of `Γ' \ Γ`, the walks
from every vertex that `z` reaches are the same in the splits at `Γ` and at `Γ'`. -/
theorem isWalk_split_split_iff (h : Γ ⊆ Γ') {z : D}
    (hz : ∀ w ∈ Γ', w ∉ Γ → ∀ p,
      ¬ (R.split Γ).IsWalk ((R.split Γ).tail z) p ((R.split Γ).tail w))
    (p : List D) {u : D} (hu : ∃ q, (R.split Γ).IsWalk ((R.split Γ).tail z) q ((R.split Γ).tail u))
    (y : D) :
    (R.split Γ').IsWalk ((R.split Γ').tail u) p ((R.split Γ').tail y) ↔
      (R.split Γ).IsWalk ((R.split Γ).tail u) p ((R.split Γ).tail y) := by
  have key : ∀ {u : D}, (∃ q, (R.split Γ).IsWalk ((R.split Γ).tail z) q ((R.split Γ).tail u)) →
      ∀ w ∈ Γ', w ∉ Γ → (R.split Γ).tail w ≠ (R.split Γ).tail u := by
    rintro u ⟨q, hq⟩ w hw hwΓ he
    exact hz w hw hwΓ q (by rw [he]; exact hq)
  induction p generalizing u with
  | nil =>
    rw [isWalk_nil, isWalk_nil]
    exact R.split_tail_eq_iff h (key hu) y
  | cons x p ih =>
    rw [isWalk_cons, isWalk_cons,
      eq_comm.trans ((R.split_tail_eq_iff h (key hu) x).trans eq_comm)]
    refine and_congr_right fun hx => ?_
    obtain ⟨q, hq⟩ := hu
    exact ih (u := (R.split Γ).rev x)
      ⟨q ++ [x], hq.append (((R.split Γ).isWalk_cons _ _ x []).2 ⟨hx, rfl⟩)⟩

/-- Under the same condition, the distances from `z` are the same in the two splits. -/
theorem walkDist_split_split (h : Γ ⊆ Γ') {z : D}
    (hz : ∀ w ∈ Γ', w ∉ Γ → ∀ p,
      ¬ (R.split Γ).IsWalk ((R.split Γ).tail z) p ((R.split Γ).tail w))
    (g : D → ℝ≥0∞) (y : D) :
    (R.split Γ').walkDist g ((R.split Γ').tail z) ((R.split Γ').tail y) =
      (R.split Γ).walkDist g ((R.split Γ).tail z) ((R.split Γ).tail y) :=
  le_antisymm
    (le_iInf₂ fun p hp => walkDist_le g ((R.isWalk_split_split_iff h hz p ⟨[], rfl⟩ y).2 hp))
    (le_iInf₂ fun p hp => walkDist_le g ((R.isWalk_split_split_iff h hz p ⟨[], rfl⟩ y).1 hp))

end Local

section Dart

variable {E : Type u} [Fintype E] [DecidableEq E] (G : RotSystem E)

/-- The dart of a token in the doubled dual: `(rev d, true)` for `(d, 2)` and `(rev d, false)`
otherwise. -/
def tokDart : E × Lab → E × Bool
  | (d, .zero) => (G.rev d, false)
  | (d, .one) => (G.rev d, false)
  | (d, .two) => (G.rev d, true)

theorem tokDart_fst (x : E × Lab) : (G.tokDart x).1 = G.rev x.1 := by
  obtain ⟨d, _ | _ | _⟩ := x <;> rfl

end Dart

namespace RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- The corners of the doubled dual at which `S` cuts: `(d, false)` for every incised dart `d`, and
`(c, true)` for every cut corner `c`. -/
def Γ : Finset (E × Bool) := S.inc.image (fun d => (d, false)) ∪ S.cut.image (fun c => (c, true))

@[simp] theorem mem_Γ_false (d : E) : (d, false) ∈ S.Γ ↔ d ∈ S.inc := by
  simp [Γ]

@[simp] theorem mem_Γ_true (c : E) : (c, true) ∈ S.Γ ↔ c ∈ S.cut := by
  simp [Γ]

/-- The doubled dual cut at the corners of `S`. -/
noncomputable def dualSplit : RotSystem (E × Bool) := G.dual.double.split S.Γ

theorem dualSplit_rot_of_not_mem {z : E × Bool} (hz : z ∉ S.Γ) :
    S.dualSplit.rot z = G.dual.double.rot z :=
  G.dual.double.split_rot_of_not_mem hz

theorem dualSplit_rev (z : E × Bool) : S.dualSplit.rev z = (G.rev z.1, !z.2) := rfl

/-- The token at a dart of the doubled dual: the first token of `rev w` at `(w, false)` and its
last token at `(w, true)`. -/
def tokOf : E × Bool → E × Lab
  | (w, false) => (G.rev w, S.firstLab (G.rev w))
  | (w, true) => (G.rev w, S.lastLab (G.rev w))

theorem isTok_tokOf (z : E × Bool) : S.IsTok (S.tokOf z) := by
  obtain ⟨w, _ | _⟩ := z
  · exact S.isTok_first _
  · exact S.isTok_last _

theorem tokOf_tokDart {x : E × Lab} (hx : S.IsTok x) : S.tokOf (G.tokDart x) = x := by
  obtain ⟨d, l⟩ := x
  cases l
  · show (G.rev (G.rev d), S.firstLab (G.rev (G.rev d))) = (d, .zero)
    rw [G.rev_rev, ← S.eq_first hx (by decide)]
  · show (G.rev (G.rev d), S.firstLab (G.rev (G.rev d))) = (d, .one)
    rw [G.rev_rev, ← S.eq_first hx (by decide)]
  · show (G.rev (G.rev d), S.lastLab (G.rev (G.rev d))) = (d, .two)
    rw [G.rev_rev, ← S.eq_last hx (by decide)]

theorem tokDart_first (d : E) : G.tokDart (d, S.firstLab d) = (G.rev d, false) := by
  unfold firstLab
  split_ifs <;> rfl

theorem lastLab_ne_one (d : E) : S.lastLab d ≠ .one := by
  unfold lastLab
  split_ifs <;> decide

theorem succ_of_ne_one {x : E × Lab} (h : x.2 ≠ .one) :
    S.succ x = (G.noteFace x.1, S.firstLab (G.noteFace x.1)) := by
  obtain ⟨d, l⟩ := x
  cases l
  · rfl
  · exact absurd rfl h
  · rfl

/-- The darts of two linked tokens lie at one vertex of the split. -/
theorem fconnect_tokDart_of_link {x y : E × Lab} (hx : S.IsTok x) (h : S.Link x y) :
    fconnect S.dualSplit.rot (G.tokDart x) (G.tokDart y) := by
  obtain ⟨rfl, h1, h2⟩ := h
  obtain ⟨d, l⟩ := x
  have hc : (G.rev d, true) ∉ S.Γ := fun h => h2 ((S.mem_Γ_true _).1 h)
  have hstep : S.dualSplit.rot (G.rev d, true) = G.tokDart (S.succ (d, l)) := by
    rw [S.dualSplit_rot_of_not_mem hc, S.succ_of_ne_one h1, S.tokDart_first]
    rfl
  have h1' : fconnect S.dualSplit.rot (G.rev d, true) (G.tokDart (S.succ (d, l))) := by
    rw [← hstep]
    exact fconnect1 _ _
  cases l
  · have hd : d ∉ S.inc := by
      unfold IsTok at hx
      exact hx.1 rfl
    have h0 : (G.rev d, false) ∉ S.Γ := fun h => hd ((S.inc_rev d).1 ((S.mem_Γ_false _).1 h))
    have h0' : fconnect S.dualSplit.rot (G.rev d, false) (G.rev d, true) := by
      have := fconnect1 S.dualSplit.rot (G.rev d, false)
      rwa [S.dualSplit_rot_of_not_mem h0] at this
    exact connect_trans h0' h1'
  · exact absurd rfl h1
  · exact h1'

/-- The piece of the token at a dart of the doubled dual. -/
def pieceAt (z : E × Bool) : S.Piece := S.piece ⟨S.tokOf z, S.isTok_tokOf z⟩

theorem pieceAt_tokDart (x : S.Tok) : S.pieceAt (G.tokDart x.1) = S.piece x := by
  unfold pieceAt
  congr 1
  exact Subtype.ext (S.tokOf_tokDart x.2)

/-- A step of the doubled dual off the corners of `S` stays in one piece. -/
theorem pieceAt_rot {z : E × Bool} (hz : z ∉ S.Γ) :
    S.pieceAt (G.dual.double.rot z) = S.pieceAt z := by
  obtain ⟨w, _ | _⟩ := z
  · have hw : w ∉ S.inc := fun h => hz ((S.mem_Γ_false w).2 h)
    have hr : G.rev w ∉ S.inc := fun h => hw ((S.inc_rev w).1 h)
    unfold pieceAt
    congr 1
    apply Subtype.ext
    show (G.rev w, S.lastLab (G.rev w)) = (G.rev w, S.firstLab (G.rev w))
    rw [lastLab, firstLab, ite_eq_right hr, ite_eq_right hr]
  · have hw : w ∉ S.cut := fun h => hz ((S.mem_Γ_true w).2 h)
    unfold pieceAt
    symm
    apply S.piece_eq_of_link
    refine ⟨?_, S.lastLab_ne_one _, ?_⟩
    · show (G.rev (G.rev (G.rot w)), S.firstLab (G.rev (G.rev (G.rot w)))) =
        S.succ (G.rev w, S.lastLab (G.rev w))
      rw [S.succ_of_ne_one (x := (G.rev w, S.lastLab (G.rev w))) (S.lastLab_ne_one _)]
      simp only [noteFace_apply, G.rev_rev]
    · show G.rev (G.rev w) ∉ S.cut
      rwa [G.rev_rev]

/-- Along a trail of the doubled dual to a corner of `S`, the piece does not change. -/
theorem pieceAt_trail {y z : E × Bool} (h : Trail G.dual.double.rot S.Γ y z) :
    S.pieceAt y = S.pieceAt z := by
  induction h with
  | here _ => rfl
  | step hy _ ih => exact (S.pieceAt_rot hy).symm.trans ih

/-- A step of the split stays in one piece. -/
theorem pieceAt_split_rot (z : E × Bool) : S.pieceAt (S.dualSplit.rot z) = S.pieceAt z := by
  by_cases hz : z ∈ S.Γ
  · obtain ⟨p, rfl⟩ : ∃ p, G.dual.double.nodeReturn S.Γ p = z :=
      ⟨_, perm_apply_inv_self _ _⟩
    have hpΓ : p ∈ S.Γ := (firstReturn_mem_iff G.dual.double.rot S.Γ p).1 hz
    have e : S.dualSplit.rot (G.dual.double.nodeReturn S.Γ p) = G.dual.double.rot p := by
      show G.dual.double.rot ((G.dual.double.nodeReturn S.Γ)⁻¹ (G.dual.double.nodeReturn S.Γ p)) = _
      rw [perm_inv_apply_self]
    rw [e]
    exact S.pieceAt_trail (firstReturn_trail G.dual.double.rot hpΓ)
  · rw [S.dualSplit_rot_of_not_mem hz]
    exact S.pieceAt_rot hz

theorem pieceAt_iterate (k : ℕ) (z : E × Bool) :
    S.pieceAt ((⇑S.dualSplit.rot)^[k] z) = S.pieceAt z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', S.pieceAt_split_rot, ih]

theorem pieceAt_eq_of_fconnect {z w : E × Bool} (h : fconnect S.dualSplit.rot z w) :
    S.pieceAt z = S.pieceAt w := by
  obtain ⟨k, rfl⟩ := fconnect_iff_iterate.1 h
  exact (S.pieceAt_iterate k z).symm

/-- **Lemma N, the pieces.** Two tokens lie in one piece exactly when their darts lie at one vertex
of the split. -/
theorem piece_eq_iff (x y : S.Tok) :
    S.piece x = S.piece y ↔ fconnect S.dualSplit.rot (G.tokDart x.1) (G.tokDart y.1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have key : ∀ x y : S.Tok, Relation.EqvGen (fun x y : S.Tok => S.Link x.1 y.1) x y →
        fconnect S.dualSplit.rot (G.tokDart x.1) (G.tokDart y.1) := by
      intro x y hxy
      induction hxy with
      | rel x y hl => exact S.fconnect_tokDart_of_link x.2 hl
      | refl x => exact connect_refl _
      | symm x y _ ih => exact fconnect_symm ih
      | trans x y z _ _ ih₁ ih₂ => exact connect_trans ih₁ ih₂
    exact key x y (Quot.eqvGen_exact h)
  · rw [← S.pieceAt_tokDart x, ← S.pieceAt_tokDart y]
    exact S.pieceAt_eq_of_fconnect h

/-- The dart of the token at a dart lies at the vertex of that dart. -/
theorem fconnect_tokDart_tokOf (z : E × Bool) :
    fconnect S.dualSplit.rot (G.tokDart (S.tokOf z)) z := by
  obtain ⟨w, _ | _⟩ := z
  · show fconnect _ (G.tokDart (G.rev w, S.firstLab (G.rev w))) (w, false)
    rw [S.tokDart_first, G.rev_rev]
  · show fconnect _ (G.tokDart (G.rev w, S.lastLab (G.rev w))) (w, true)
    by_cases h : G.rev w ∈ S.inc
    · rw [show S.lastLab (G.rev w) = .two from ite_eq_left h]
      show fconnect _ (G.rev (G.rev w), true) (w, true)
      rw [G.rev_rev]
    · rw [show S.lastLab (G.rev w) = .zero from ite_eq_right h]
      show fconnect _ (G.rev (G.rev w), false) (w, true)
      rw [G.rev_rev]
      have hw : (w, false) ∉ S.Γ := fun h' => h ((S.inc_rev w).2 ((S.mem_Γ_false w).1 h'))
      have := fconnect1 S.dualSplit.rot (w, false)
      rwa [S.dualSplit_rot_of_not_mem hw] at this

/-- The vertex of the split at which a piece lies. -/
noncomputable def vertexOf : S.Piece → S.dualSplit.Vertex :=
  Quot.lift (fun x => S.dualSplit.tail (G.tokDart x.1)) fun x y h =>
    (S.dualSplit.tail_eq_iff _ _).2 ((S.piece_eq_iff x y).1 (S.piece_eq_of_link h))

/-- **Lemma N, the pieces.** The pieces are the vertices of the split. -/
noncomputable def vertexEquiv : S.Piece ≃ S.dualSplit.Vertex where
  toFun := S.vertexOf
  invFun := Quotient.lift S.pieceAt fun _ _ h =>
    S.pieceAt_eq_of_fconnect ((sameCycle_iff_fconnect S.dualSplit.rot).1 h)
  left_inv f := by
    induction f using Quot.ind with
    | mk x => exact S.pieceAt_tokDart x
  right_inv v := by
    obtain ⟨z, rfl⟩ := S.dualSplit.exists_tail_eq v
    show S.dualSplit.tail (G.tokDart (S.tokOf z)) = S.dualSplit.tail z
    exact (S.dualSplit.tail_eq_iff _ _).2 (S.fconnect_tokDart_tokOf z)

theorem vertexEquiv_pieceAt (z : E × Bool) : S.vertexEquiv (S.pieceAt z) = S.dualSplit.tail z :=
  S.vertexEquiv.apply_symm_apply (S.dualSplit.tail z)

theorem vertexEquiv_piece (x : S.Tok) :
    S.vertexEquiv (S.piece x) = S.dualSplit.tail (G.tokDart x.1) := rfl

/-- The token at the reverse of a dart is the partner of the token at the dart. -/
theorem tokOf_rev (z : E × Bool) : S.tokOf (S.dualSplit.rev z) = G.partner (S.tokOf z) := by
  obtain ⟨w, _ | _⟩ := z
  · show (G.rev (G.rev w), S.lastLab (G.rev (G.rev w))) =
      (G.rev (G.rev w), (S.firstLab (G.rev w)).swap)
    rw [G.rev_rev]
    unfold lastLab firstLab
    by_cases h : w ∈ S.inc
    · rw [ite_eq_left h, ite_eq_left ((S.inc_rev w).2 h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right fun h' => h ((S.inc_rev w).1 h')]
      rfl
  · show (G.rev (G.rev w), S.firstLab (G.rev (G.rev w))) =
      (G.rev (G.rev w), (S.lastLab (G.rev w)).swap)
    rw [G.rev_rev]
    unfold lastLab firstLab
    by_cases h : w ∈ S.inc
    · rw [ite_eq_left h, ite_eq_left ((S.inc_rev w).2 h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right fun h' => h ((S.inc_rev w).1 h')]
      rfl

/-- **Lemma N, the pairs.** The dart of a token runs from the vertex of its piece to the vertex of
the piece of its partner. -/
theorem head_tokDart (x : S.Tok) :
    S.dualSplit.head (G.tokDart x.1) = S.vertexEquiv (S.piece (S.partnerTok x)) := by
  show S.dualSplit.tail (S.dualSplit.rev (G.tokDart x.1)) =
    S.dualSplit.tail (G.tokDart (G.partner x.1))
  refine (S.dualSplit.tail_eq_iff _ _).2 ?_
  have h := S.fconnect_tokDart_tokOf (S.dualSplit.rev (G.tokDart x.1))
  rw [S.tokOf_rev, S.tokOf_tokDart x.2] at h
  exact fconnect_symm h

/-! ### Distances -/

theorem tokOf_fst (z : E × Bool) : (S.tokOf z).1 = G.rev z.1 := by
  obtain ⟨w, _ | _⟩ := z <;> rfl

section Dist

variable (c : E → ℝ)

theorem wt_dw_nonneg (hc0 : ∀ d, 0 ≤ c d) : ∀ {f h : S.Piece}
    (P : FaceDisjoint.Walk S.DArc f h), 0 ≤ P.wt (S.dw fun x => c x.1.1)
  | _, _, .nil _ => le_rfl
  | _, _, .cons _ P => by
    rw [FaceDisjoint.Walk.wt_cons]
    exact add_nonneg (hc0 _) (wt_dw_nonneg hc0 P)

/-- A walk of the token graph gives a walk of the split through the darts of its tokens, of the
same weight for weights that agree on the two darts of an edge. -/
theorem split_walk (hcr : ∀ d, c (G.rev d) = c d) : ∀ {f h : S.Piece}
    (P : FaceDisjoint.Walk S.DArc f h), ∃ p : List (E × Bool),
      S.dualSplit.IsWalk (S.vertexEquiv f) p (S.vertexEquiv h) ∧
      (p.map fun z => c z.1).sum = P.wt (S.dw fun x => c x.1.1)
  | _, _, .nil _ => ⟨[], rfl, by simp⟩
  | _, _, .cons x P => by
    obtain ⟨p, hp, hw⟩ := split_walk hcr P
    refine ⟨G.tokDart x.1.1 :: p, (S.dualSplit.isWalk_cons _ _ _ _).2 ⟨?_, ?_⟩, ?_⟩
    · exact (S.vertexEquiv_piece x.1).symm.trans (congrArg S.vertexEquiv x.2.1)
    · rw [S.head_tokDart, x.2.2]
      exact hp
    · simp only [List.map_cons, List.sum_cons, hw, FaceDisjoint.Walk.wt_cons, G.tokDart_fst, hcr,
        dw]

/-- A walk of the split gives a walk of the token graph through the tokens at its darts, of the
same weight for weights that agree on the two darts of an edge. -/
theorem dwalk_of_split (hcr : ∀ d, c (G.rev d) = c d) : ∀ (p : List (E × Bool)) {f h : S.Piece},
    S.dualSplit.IsWalk (S.vertexEquiv f) p (S.vertexEquiv h) →
      ∃ P : FaceDisjoint.Walk S.DArc f h,
        P.wt (S.dw fun x => c x.1.1) = (p.map fun z => c z.1).sum
  | [], f, h, hp => by
    obtain rfl : f = h := S.vertexEquiv.injective ((S.dualSplit.isWalk_nil _ _).1 hp)
    exact ⟨.nil _, by simp⟩
  | z :: p, f, h, hp => by
    obtain ⟨hz, hp⟩ := (S.dualSplit.isWalk_cons _ _ _ _).1 hp
    obtain ⟨P, hP⟩ := dwalk_of_split hcr p (f := S.vertexEquiv.symm (S.dualSplit.head z))
      (h := h) (by rwa [Equiv.apply_symm_apply])
    have h1 : S.piece ⟨S.tokOf z, S.isTok_tokOf z⟩ = f := by
      have e : S.piece ⟨S.tokOf z, S.isTok_tokOf z⟩ = S.vertexEquiv.symm (S.dualSplit.tail z) :=
        rfl
      rw [e, hz, Equiv.symm_apply_apply]
    have h2 : S.piece (S.partnerTok ⟨S.tokOf z, S.isTok_tokOf z⟩) =
        S.vertexEquiv.symm (S.dualSplit.head z) := by
      show _ = S.piece ⟨S.tokOf (S.dualSplit.rev z), S.isTok_tokOf _⟩
      congr 1
      exact Subtype.ext (S.tokOf_rev z).symm
    refine ⟨.cons ⟨⟨S.tokOf z, S.isTok_tokOf z⟩, h1, h2⟩ P, ?_⟩
    rw [FaceDisjoint.Walk.wt_cons, hP, List.map_cons, List.sum_cons]
    show c (S.tokOf z).1 + _ = _
    rw [S.tokOf_fst, hcr]

omit [Fintype E] [DecidableEq E] in
theorem sum_map_nonneg (hc0 : ∀ d, 0 ≤ c d) (p : List (E × Bool)) :
    0 ≤ (p.map fun z => c z.1).sum :=
  List.sum_nonneg fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact hc0 _

omit [Fintype E] [DecidableEq E] in
theorem sum_ofReal (hc0 : ∀ d, 0 ≤ c d) (p : List (E × Bool)) :
    (p.map fun z => ENNReal.ofReal (c z.1)).sum = ENNReal.ofReal (p.map fun z => c z.1).sum := by
  induction p with
  | nil => simp
  | cons z p ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ENNReal.ofReal_add (hc0 _) (sum_map_nonneg c hc0 p)]

/-- **Lemma N, the distances.** For weights `c ≥ 0` that agree on the two darts of an edge, the
distance of two pieces in the token graph is the distance of their vertices in the split. -/
theorem ddist_eq (hc0 : ∀ d, 0 ≤ c d) (hcr : ∀ d, c (G.rev d) = c d) (f h : S.Piece) :
    S.ddist (fun x => c x.1.1) f h =
      (S.dualSplit.walkDist (fun z => ENNReal.ofReal (c z.1)) (S.vertexEquiv f)
        (S.vertexEquiv h) : EReal) := by
  have key : ∀ p : List (E × Bool), S.dualSplit.IsWalk (S.vertexEquiv f) p (S.vertexEquiv h) →
      S.ddist (fun x => c x.1.1) f h ≤
        (((p.map fun z => ENNReal.ofReal (c z.1)).sum : ℝ≥0∞) : EReal) := by
    intro p hp
    obtain ⟨P, hP⟩ := S.dwalk_of_split c hcr p hp
    rw [sum_ofReal c hc0, EReal.coe_ennreal_ofReal, max_eq_left (sum_map_nonneg c hc0 p), ← hP]
    exact iInf_le (fun P : FaceDisjoint.Walk S.DArc f h =>
      ((P.wt (S.dw fun x => c x.1.1) : ℝ) : EReal)) P
  refine le_antisymm ?_ (le_iInf fun P => ?_)
  · by_cases hD : S.ddist (fun x => c x.1.1) f h ≤ 0
    · exact hD.trans (EReal.coe_ennreal_nonneg _)
    rw [← EReal.coe_toENNReal (not_le.1 hD).le, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun p hp => ?_
    have := EReal.toENNReal_le_toENNReal (key p hp)
    rwa [EReal.toENNReal_coe] at this
  · obtain ⟨p, hp, hw⟩ := S.split_walk c hcr P
    have h1 := walkDist_le (fun z => ENNReal.ofReal (c z.1)) hp
    rw [sum_ofReal c hc0, hw] at h1
    calc (S.dualSplit.walkDist (fun z => ENNReal.ofReal (c z.1)) (S.vertexEquiv f)
            (S.vertexEquiv h) : EReal)
        ≤ (ENNReal.ofReal (P.wt (S.dw fun x => c x.1.1)) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.2 h1
      _ = ((P.wt (S.dw fun x => c x.1.1) : ℝ) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (S.wt_dw_nonneg c hc0 P)]

/-! ### Live annuli -/

variable {C : G.dual.CutPath} {g : E → ℝ≥0∞} {Γ : Finset (E × Bool)}

/-- **Lemma N on a live annulus.** Let the weights `c ≥ 0` agree on the two darts of an edge and
give `g`, and let the corners of `S` hold those of a live annulus, the others out of its reach.
Then `λ_t` is the distance in the token graph of `S` between the pieces at the corners `κ0(t)`
and `κ1(t)`. -/
theorem ddist_live (hc0 : ∀ d, 0 ≤ c d) (hcr : ∀ d, c (G.rev d) = c d)
    (hgc : ∀ d, g d = ENNReal.ofReal (c d)) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (G.dual.double.split Γ).IsWalk
      ((G.dual.double.split Γ).tail (L.κ0 t)) p ((G.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb) :
    S.ddist (fun x => c x.1.1) (S.pieceAt (L.κ0 t)) (S.pieceAt (L.κ1 t)) =
      (C.lamD g t : EReal) := by
  have hg : (g ∘ Prod.fst : E × Bool → ℝ≥0∞) = fun z => ENNReal.ofReal (c z.1) :=
    funext fun z => hgc z.1
  have hd := L.dist t h1 h2 h3 h4
  rw [← G.dual.double.walkDist_split_split hS hz, hg] at hd
  rw [S.ddist_eq c hc0 hcr, S.vertexEquiv_pieceAt, S.vertexEquiv_pieceAt]
  exact congrArg (fun x : ℝ≥0∞ => (x : EReal)) hd

/-- **`λ_t` in the repaired graph.** Under the same conditions, for copies `a` and `b` on E_R
edges of the pieces at `κ0(t)` and `κ1(t)`, the distance in `Ĝ_ℓ` is `λ_t` if `λ_t < M`, and at
least `M` otherwise. -/
theorem gdist_live (hc0 : ∀ d, 0 ≤ c d) (hcr : ∀ d, c (G.rev d) = c d)
    (hgc : ∀ d, g d = ENNReal.ofReal (c d)) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (G.dual.double.split Γ).IsWalk
      ((G.dual.double.split Γ).tail (L.κ0 t)) p ((G.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb) {M : ℝ} (hM : 0 ≤ M)
    (a b : S.EndCopy) (ha : S.pieceOf a = S.pieceAt (L.κ0 t))
    (hb : S.pieceOf b = S.pieceAt (L.κ1 t)) :
    ((C.lamD g t : EReal) < M → S.gdist (fun x => c x.1.1) M a.1 b.1 = C.lamD g t) ∧
      ((M : EReal) ≤ C.lamD g t → (M : EReal) ≤ S.gdist (fun x => c x.1.1) M a.1 b.1) := by
  have hd := S.ddist_live c hc0 hcr hgc L hS hz h1 h2 h3 h4
  rw [← ha, ← hb] at hd
  rw [← hd]
  exact S.gdist_eq (fun _ => hc0 _) hM a b

end Dist

end RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E}

/-- The data with the incised darts and the cut corners of a set of corners of the doubled dual. -/
def RData.ofCorners (Γ : Finset (E × Bool)) (hΓ : ∀ d, (d, false) ∈ Γ → (G.rev d, false) ∈ Γ)
    (modeL hostT : E → Bool) (hhost : ∀ d, (d, false) ∉ Γ → hostT (G.rev d) = !hostT d) :
    G.RData where
  inc := Finset.univ.filter fun d => (d, false) ∈ Γ
  inc_rev d := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => by simpa [G.rev_rev] using hΓ _ h, hΓ d⟩
  cut := Finset.univ.filter fun c => (c, true) ∈ Γ
  modeL := modeL
  hostT := hostT
  hostT_rev d hd := hhost d (by simpa using hd)

/-- Every set of corners of the doubled dual that holds both digon corners of each of its edges is
the set of corners of some data. -/
theorem RData.Γ_ofCorners (Γ : Finset (E × Bool)) (hΓ : ∀ d, (d, false) ∈ Γ → (G.rev d, false) ∈ Γ)
    (modeL hostT : E → Bool) (hhost : ∀ d, (d, false) ∉ Γ → hostT (G.rev d) = !hostT d) :
    (RData.ofCorners Γ hΓ modeL hostT hhost).Γ = Γ := by
  ext ⟨d, _ | _⟩ <;> simp [RData.mem_Γ_false, RData.mem_Γ_true, RData.ofCorners]

variable {C : G.dual.CutPath} {g : E → ℝ≥0∞} {Γ : Finset (E × Bool)}

/-- **Lemma N on a live annulus, for its own corners.** For the data with the corners of a live
annulus, any modes and any hosts of the unincised pairs, `λ_t` is the distance in the token graph
between the pieces at the corners `κ0(t)` and `κ1(t)`. -/
theorem RData.ddist_live_ofCorners (c : E → ℝ) (hc0 : ∀ d, 0 ≤ c d)
    (hcr : ∀ d, c (G.rev d) = c d) (hgc : ∀ d, g d = ENNReal.ofReal (c d)) (L : C.Live g Γ)
    (modeL hostT : E → Bool) (hhost : ∀ d, (d, false) ∉ Γ → hostT (G.rev d) = !hostT d) {t : ℕ}
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb) :
    (RData.ofCorners (G := G) Γ L.pair modeL hostT hhost).ddist (fun x => c x.1.1)
        ((RData.ofCorners (G := G) Γ L.pair modeL hostT hhost).pieceAt (L.κ0 t))
        ((RData.ofCorners (G := G) Γ L.pair modeL hostT hhost).pieceAt (L.κ1 t)) =
      (C.lamD g t : EReal) := by
  have hΓ := RData.Γ_ofCorners (G := G) Γ L.pair modeL hostT hhost
  have hS : Γ ⊆ (RData.ofCorners (G := G) Γ L.pair modeL hostT hhost).Γ := by rw [hΓ]
  exact (RData.ofCorners (G := G) Γ L.pair modeL hostT hhost).ddist_live c hc0 hcr hgc L hS
    (fun w hw hwΓ => absurd (hΓ ▸ hw) hwΓ) h1 h2 h3 h4

end RotSystem

end SsspFlow
