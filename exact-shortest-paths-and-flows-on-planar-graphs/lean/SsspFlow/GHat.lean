import SsspFlow.PlanarMap

/-!
# The repaired graph of copies

Definition R of `notes/GHAT_REPAIR.md` for a graph `G` with a rotation system. The data of one level
(`RData`) are the incised darts `inc`, both darts of each edge of `I_ℓ`; the cut corners `cut`,
named by their first flanks, each with its mode (`modeL`, true for mode L); and, for each unincised
edge, the end that hosts its pair (`hostT`).

* Tokens and pairs (R1). A token is a dart with a label (`Lab`): `0` if the dart is not incised, `1`
  or `2` if it is (`IsTok`). The other token of the pair of `(δ, l)` is `(rev δ, l')`, with `0' = 0`,
  `1' = 2` and `2' = 1` (`partner`).
* Pieces (R2). Along the face walk of the note, `(δ, 1)` is followed by `(δ, 2)`, and the last token
  of `δ` by the first token of `rot (rev δ)` (`succ`). Two consecutive tokens are linked if no cut
  lies between them: neither the cut inside an incised dart nor the cut at a cut corner (`Link`). The
  pieces are the classes of linked tokens (`Piece`).
* Copies (R3). The star centre `σ(v)`, the copy `D(c)` of each corner, `L(c)` if `in(c)` is
  incised, `R(c)` if `out(c)` is incised, and `X(c)` for a cut corner (`Copy`, `Valid`).
* E_R edges (R4). The token `x` is an edge from `α(x)` to `β(x)` (`alpha`, `beta`), after repair (a):
  at a cut corner in mode L the in-token ends at `X(c)`, in mode R the out-token starts there.
* E_S edges (R5): `σ(v)D(c)`, `D(c)L(c)`, `D(c)R(c)` and `D(c)X(c)` (`ES`).
* E_C edges (R6). The edge of the pair of `x` joins `att(x)` and `att(x')`, the ends of its two
  tokens at the host (`att`); for an incised edge the host is the tail of the dart of the token
  labelled `1`. This is repair (b).

Claims 1 and 2 of the note. The ends of an E_R edge are valid copies and no star centres
(`valid_alpha`, `valid_beta`, `alpha_ne_star`, `beta_ne_star`), and they are distinct if `G` has no
loops (`alpha_ne_beta`). `α` and `β` are
injective on tokens (`alpha_inj`, `beta_inj`), and `β(y) = α(z)` exactly when `z` follows `y` in a
piece (`beta_eq_alpha_iff`). Every valid copy other than a star centre is an end of a token
(`exists_end`). So the E_R edges, directed from `α` to `β`, have in- and out-degree at most one, and
two of them meet only where a piece links their tokens.

Property (1) of Lemma R follows. Every copy on an E_R edge belongs to the piece of its tokens
(`pieceOf_eq`); an E_R edge joins two copies of one piece, and the copies of one piece are joined
by E_R edges (`ring_conn`). With the degrees, the E_R edges of each piece form a path, or a cycle if
the piece has no cut, and distinct pieces have disjoint paths. Property (2): the E_C edge of the pair
of `x` joins the path of the piece of `x` to the path of the piece of its other token
(`pieceOf_att`), at two copies of one vertex, the host (`owner_att_partner`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

universe u

/-- The label of a token. -/
inductive Lab
  | zero
  | one
  | two
  deriving DecidableEq

namespace Lab

/-- The label of the other token of a pair: `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 1`. -/
def swap : Lab → Lab
  | zero => zero
  | one => two
  | two => one

@[simp] theorem swap_swap (l : Lab) : l.swap.swap = l := by cases l <;> rfl

@[simp] theorem swap_eq_zero (l : Lab) : l.swap = zero ↔ l = zero := by cases l <;> decide

end Lab

/-- The copies of Definition R: a star centre `σ(v)` for each vertex, and the copies `D(c)`, `L(c)`,
`R(c)`, `X(c)` at a corner `c`. -/
inductive Copy (V : Type u) (E : Type u)
  | star (v : V)
  | dc (c : E)
  | lc (c : E)
  | rc (c : E)
  | xc (c : E)

variable {E : Type u} [Fintype E] [DecidableEq E] (G : RotSystem E)

/-- The other token of the pair of `x`. -/
def partner (x : E × Lab) : E × Lab := (G.rev x.1, x.2.swap)

@[simp] theorem partner_partner (x : E × Lab) : G.partner (G.partner x) = x := by
  obtain ⟨d, l⟩ := x
  simp [partner, G.rev_rev]

/-- The vertex of which a copy is a copy. -/
def owner : Copy G.Vertex E → G.Vertex
  | .star v => v
  | .dc c => G.tail c
  | .lc c => G.tail c
  | .rc c => G.tail c
  | .xc c => G.tail c

/-- The data of Definition R at one level: the incised darts, both darts of each edge of `I_ℓ`; the
cut corners, named by their first flanks, with their modes (`true` for mode L); and the host of the
pair of each unincised edge, the tail of `d` if `hostT d`. -/
structure RData where
  inc : Finset E
  inc_rev : ∀ d, G.rev d ∈ inc ↔ d ∈ inc
  cut : Finset E
  modeL : E → Bool
  hostT : E → Bool
  hostT_rev : ∀ d, d ∉ inc → hostT (G.rev d) = !hostT d

namespace RData

variable {G} (S : G.RData)

/-- A dart outside `inc` has the token `(δ, 0)`, a dart in `inc` the tokens `(δ, 1)` and `(δ, 2)`. -/
def IsTok (x : E × Lab) : Prop := x.2 = .zero ↔ x.1 ∉ S.inc

instance (x : E × Lab) : Decidable (S.IsTok x) := by unfold IsTok; infer_instance

/-- The tokens. -/
abbrev Tok : Type u := {x : E × Lab // S.IsTok x}

theorem isTok_partner {x : E × Lab} : S.IsTok (G.partner x) ↔ S.IsTok x := by
  obtain ⟨d, l⟩ := x
  simp only [IsTok, partner, Lab.swap_eq_zero, S.inc_rev]

/-- The other token of the pair, as a token. -/
def partnerTok (x : S.Tok) : S.Tok := ⟨G.partner x.1, S.isTok_partner.2 x.2⟩

@[simp] theorem partnerTok_partnerTok (x : S.Tok) : S.partnerTok (S.partnerTok x) = x :=
  Subtype.ext (G.partner_partner x.1)

/-- The label of the first token of a dart along the face walk. -/
def firstLab (d : E) : Lab := if d ∈ S.inc then .one else .zero

/-- The label of the last token of a dart along the face walk. -/
def lastLab (d : E) : Lab := if d ∈ S.inc then .two else .zero

theorem isTok_first (d : E) : S.IsTok (d, S.firstLab d) := by
  unfold IsTok firstLab
  split_ifs with h <;> simp [h]

theorem isTok_last (d : E) : S.IsTok (d, S.lastLab d) := by
  unfold IsTok lastLab
  split_ifs with h <;> simp [h]

/-- A token not labelled `2` is the first token of its dart. -/
theorem eq_first {d : E} {l : Lab} (h : S.IsTok (d, l)) (hl : l ≠ .two) : l = S.firstLab d := by
  unfold IsTok at h
  unfold firstLab
  cases l <;> split_ifs with hd <;> simp_all

/-- A token not labelled `1` is the last token of its dart. -/
theorem eq_last {d : E} {l : Lab} (h : S.IsTok (d, l)) (hl : l ≠ .one) : l = S.lastLab d := by
  unfold IsTok at h
  unfold lastLab
  cases l <;> split_ifs with hd <;> simp_all

/-- The token after `x` in the face walk of the note: `(δ, 1)` is followed by `(δ, 2)`, and the last
token of `δ` by the first token of `rot (rev δ)`. -/
def succ : E × Lab → E × Lab
  | (d, .zero) => (G.noteFace d, S.firstLab (G.noteFace d))
  | (d, .one) => (d, .two)
  | (d, .two) => (G.noteFace d, S.firstLab (G.noteFace d))

/-- `y` follows `x` in a piece: no cut lies between them, neither the cut inside an incised dart nor
the cut at a cut corner. -/
def Link (x y : E × Lab) : Prop := y = S.succ x ∧ x.2 ≠ .one ∧ G.headCorner x.1 ∉ S.cut

/-- The pieces: the classes of linked tokens. -/
def Piece : Type u := Quot fun x y : S.Tok => S.Link x.1 y.1

/-- The piece of a token. -/
def piece (x : S.Tok) : S.Piece := Quot.mk _ x

theorem piece_eq_of_link {x y : S.Tok} (h : S.Link x.1 y.1) : S.piece x = S.piece y :=
  Quot.sound h

/-- The copies that exist at this level. -/
def Valid : Copy G.Vertex E → Prop
  | .star _ => True
  | .dc _ => True
  | .lc c => G.inDart c ∈ S.inc
  | .rc c => G.outDart c ∈ S.inc
  | .xc c => c ∈ S.cut

/-- The tail end of the out-token of the corner `c`: `D(c)`, or `X(c)` at a cut corner in mode R. -/
def alphaD (c : E) : Copy G.Vertex E := if c ∈ S.cut ∧ S.modeL c = false then .xc c else .dc c

/-- The head end of the in-token of the corner `c`: `D(c)`, or `X(c)` at a cut corner in mode L. -/
def betaD (c : E) : Copy G.Vertex E := if c ∈ S.cut ∧ S.modeL c = true then .xc c else .dc c

/-- `α(x)`, the tail end of the E_R edge of `x`. -/
def alpha : E × Lab → Copy G.Vertex E
  | (d, .zero) => S.alphaD (G.tailCorner d)
  | (d, .one) => S.alphaD (G.tailCorner d)
  | (d, .two) => .rc (G.tailCorner d)

/-- `β(x)`, the head end of the E_R edge of `x`. -/
def beta : E × Lab → Copy G.Vertex E
  | (d, .zero) => S.betaD (G.headCorner d)
  | (d, .one) => .lc (G.headCorner d)
  | (d, .two) => S.betaD (G.headCorner d)

/-- The E_S edges, `σ(v)D(c)`, `D(c)L(c)`, `D(c)R(c)` and `D(c)X(c)`, each in one direction. -/
def ES : Copy G.Vertex E → Copy G.Vertex E → Prop
  | .star v, .dc c => G.tail c = v
  | .dc c, .lc c' => c = c' ∧ G.inDart c ∈ S.inc
  | .dc c, .rc c' => c = c' ∧ G.outDart c ∈ S.inc
  | .dc c, .xc c' => c = c' ∧ c ∈ S.cut
  | _, _ => False

/-- The pair of `x` is hosted at the tail of the dart of `x`. -/
def atTail : E × Lab → Bool
  | (d, .zero) => S.hostT d
  | (_, .one) => true
  | (_, .two) => false

/-- The end at the host of the E_R edge of `x`, an end of the E_C edge of its pair. -/
def att (x : E × Lab) : Copy G.Vertex E := if S.atTail x then S.alpha x else S.beta x

/-! ### The copies at a corner -/

theorem alphaD_inj {c c' : E} (h : S.alphaD c = S.alphaD c') : c = c' := by
  unfold alphaD at h
  split_ifs at h <;> simpa using h

theorem betaD_inj {c c' : E} (h : S.betaD c = S.betaD c') : c = c' := by
  unfold betaD at h
  split_ifs at h <;> simpa using h

theorem alphaD_ne_rc (c c' : E) : S.alphaD c ≠ .rc c' := by
  unfold alphaD
  split_ifs <;> simp

theorem betaD_ne_lc (c c' : E) : S.betaD c ≠ .lc c' := by
  unfold betaD
  split_ifs <;> simp

theorem betaD_ne_rc (c c' : E) : S.betaD c ≠ .rc c' := by
  unfold betaD
  split_ifs <;> simp

theorem alphaD_ne_lc (c c' : E) : S.alphaD c ≠ .lc c' := by
  unfold alphaD
  split_ifs <;> simp

/-- The copy at a corner that carries the in-token is the copy that carries the out-token exactly
when the corner is not cut. -/
theorem betaD_eq_alphaD {c c' : E} : S.betaD c = S.alphaD c' ↔ c = c' ∧ c ∉ S.cut := by
  unfold betaD alphaD
  by_cases hc : c ∈ S.cut <;> by_cases hc' : c' ∈ S.cut <;>
    cases hm : S.modeL c <;> cases hm' : S.modeL c' <;> simp [hc, hc'] <;>
    rintro rfl <;> simp_all

theorem owner_alphaD (c : E) : G.owner (S.alphaD c) = G.tail c := by
  unfold alphaD
  split_ifs <;> rfl

theorem owner_betaD (c : E) : G.owner (S.betaD c) = G.tail c := by
  unfold betaD
  split_ifs <;> rfl

theorem valid_alphaD (c : E) : S.Valid (S.alphaD c) := by
  unfold alphaD
  split_ifs with h
  · exact h.1
  · trivial

theorem valid_betaD (c : E) : S.Valid (S.betaD c) := by
  unfold betaD
  split_ifs with h
  · exact h.1
  · trivial

/-! ### Claims 1 and 2 -/

theorem owner_alpha (x : E × Lab) : G.owner (S.alpha x) = G.tail x.1 := by
  obtain ⟨d, l⟩ := x
  cases l
  · exact (S.owner_alphaD _).trans (G.tail_tailCorner d)
  · exact (S.owner_alphaD _).trans (G.tail_tailCorner d)
  · exact G.tail_tailCorner d

theorem owner_beta (x : E × Lab) : G.owner (S.beta x) = G.head x.1 := by
  obtain ⟨d, l⟩ := x
  cases l
  · exact (S.owner_betaD _).trans (G.tail_headCorner d)
  · exact G.tail_headCorner d
  · exact (S.owner_betaD _).trans (G.tail_headCorner d)

/-- The two ends of an E_R edge are distinct. -/
theorem alpha_ne_beta (hG : ∀ d, G.head d ≠ G.tail d) (x : E × Lab) : S.alpha x ≠ S.beta x :=
  fun h => hG x.1 (by rw [← S.owner_alpha, ← S.owner_beta, h])

theorem valid_alpha {x : E × Lab} (hx : S.IsTok x) : S.Valid (S.alpha x) := by
  obtain ⟨d, l⟩ := x
  cases l
  · exact S.valid_alphaD _
  · exact S.valid_alphaD _
  · show G.outDart (G.tailCorner d) ∈ S.inc
    rw [G.outDart_tailCorner]
    unfold IsTok at hx
    simpa using hx

theorem valid_beta {x : E × Lab} (hx : S.IsTok x) : S.Valid (S.beta x) := by
  obtain ⟨d, l⟩ := x
  cases l
  · exact S.valid_betaD _
  · show G.inDart (G.headCorner d) ∈ S.inc
    rw [G.inDart_headCorner]
    unfold IsTok at hx
    simpa using hx
  · exact S.valid_betaD _

theorem alpha_ne_star (x : E × Lab) (v : G.Vertex) : S.alpha x ≠ .star v := by
  obtain ⟨d, l⟩ := x
  cases l <;> simp only [alpha, alphaD] <;> (try split_ifs) <;> simp

theorem beta_ne_star (x : E × Lab) (v : G.Vertex) : S.beta x ≠ .star v := by
  obtain ⟨d, l⟩ := x
  cases l <;> simp only [beta, betaD] <;> (try split_ifs) <;> simp

/-- `α` is injective on tokens: a copy is the tail end of at most one E_R edge. -/
theorem alpha_inj {x y : E × Lab} (hx : S.IsTok x) (hy : S.IsTok y) (h : S.alpha x = S.alpha y) :
    x = y := by
  obtain ⟨d, l⟩ := x
  obtain ⟨d', l'⟩ := y
  have ht : ∀ {a b : E}, G.tailCorner a = G.tailCorner b → a = b := fun h => G.rot.symm.injective h
  cases l <;> cases l' <;> simp only [alpha] at h
  · rw [ht (S.alphaD_inj h)]
  · obtain rfl := ht (S.alphaD_inj h)
    unfold IsTok at hx hy
    simp_all
  · exact absurd h (S.alphaD_ne_rc _ _)
  · obtain rfl := ht (S.alphaD_inj h)
    unfold IsTok at hx hy
    simp_all
  · rw [ht (S.alphaD_inj h)]
  · exact absurd h (S.alphaD_ne_rc _ _)
  · exact absurd h.symm (S.alphaD_ne_rc _ _)
  · exact absurd h.symm (S.alphaD_ne_rc _ _)
  · simp only [Copy.rc.injEq] at h
    rw [ht h]

/-- `β` is injective on tokens: a copy is the head end of at most one E_R edge. -/
theorem beta_inj {x y : E × Lab} (hx : S.IsTok x) (hy : S.IsTok y) (h : S.beta x = S.beta y) :
    x = y := by
  obtain ⟨d, l⟩ := x
  obtain ⟨d', l'⟩ := y
  have ht : ∀ {a b : E}, G.headCorner a = G.headCorner b → a = b := fun h => by
    simpa [RotSystem.headCorner, G.rev_rev] using congrArg G.rev h
  cases l <;> cases l' <;> simp only [beta] at h
  · rw [ht (S.betaD_inj h)]
  · exact absurd h (S.betaD_ne_lc _ _)
  · obtain rfl := ht (S.betaD_inj h)
    unfold IsTok at hx hy
    simp_all
  · exact absurd h.symm (S.betaD_ne_lc _ _)
  · simp only [Copy.lc.injEq] at h
    rw [ht h]
  · exact absurd h.symm (S.betaD_ne_lc _ _)
  · obtain rfl := ht (S.betaD_inj h)
    unfold IsTok at hx hy
    simp_all
  · exact absurd h (S.betaD_ne_lc _ _)
  · rw [ht (S.betaD_inj h)]

/-- **Claim 2.** The head end of `y` is the tail end of `z` exactly when `z` follows `y` in a
piece. -/
theorem beta_eq_alpha_iff {y z : E × Lab} (hy : S.IsTok y) (hz : S.IsTok z) :
    S.beta y = S.alpha z ↔ S.Link y z := by
  obtain ⟨d, l⟩ := y
  obtain ⟨d', l'⟩ := z
  have key : ∀ {l l' : Lab}, l ≠ .one → l' ≠ .two → S.IsTok (d, l) → S.IsTok (d', l') →
      (S.betaD (G.headCorner d) = S.alphaD (G.tailCorner d') ↔
        (d', l') = (G.noteFace d, S.firstLab (G.noteFace d)) ∧ G.headCorner d ∉ S.cut) := by
    intro l l' _ hl' _ hz'
    rw [S.betaD_eq_alphaD]
    have e1 : G.headCorner d = G.tailCorner d' ↔ d' = G.noteFace d := by
      constructor
      · intro h
        rw [← G.outDart_tailCorner d', ← h]
        rfl
      · rintro rfl
        exact (G.tailCorner_noteFace d).symm
    rw [e1]
    constructor
    · rintro ⟨rfl, hc⟩
      exact ⟨by rw [S.eq_first hz' hl'], hc⟩
    · rintro ⟨h, hc⟩
      exact ⟨(Prod.mk.inj h).1, hc⟩
  have hf : ∀ e : E, S.firstLab e ≠ .two := fun e => by
    unfold firstLab
    split_ifs <;> simp
  unfold Link
  cases l <;> cases l' <;> simp only [alpha, beta, succ]
  · rw [key (by decide) (by decide) hy hz]
    simp
  · rw [key (by decide) (by decide) hy hz]
    simp
  · exact iff_of_false (S.betaD_ne_rc _ _) fun h => hf _ (Prod.mk.inj h.1).2.symm
  · exact iff_of_false (fun h => S.alphaD_ne_lc _ _ h.symm) fun h => h.2.1 rfl
  · exact iff_of_false (fun h => S.alphaD_ne_lc _ _ h.symm) fun h => h.2.1 rfl
  · exact iff_of_false (fun h => by cases h) fun h => h.2.1 rfl
  · rw [key (by decide) (by decide) hy hz]
    simp
  · rw [key (by decide) (by decide) hy hz]
    simp
  · exact iff_of_false (S.betaD_ne_rc _ _) fun h => hf _ (Prod.mk.inj h.1).2.symm

/-- **Claim 1.** Every valid copy other than a star centre is an end of the E_R edge of a token. -/
theorem exists_end {a : Copy G.Vertex E} (ha : S.Valid a) (hs : ∀ v, a ≠ .star v) :
    ∃ x : E × Lab, S.IsTok x ∧ (S.alpha x = a ∨ S.beta x = a) := by
  have hin : ∀ c, S.beta (G.rev c, S.lastLab (G.rev c)) = S.betaD c := fun c => by
    unfold lastLab
    split_ifs <;> simp only [beta, RotSystem.headCorner, G.rev_rev]
  have hout : ∀ c, S.alpha (G.rot c, S.firstLab (G.rot c)) = S.alphaD c := fun c => by
    unfold firstLab
    split_ifs <;> simp only [alpha, RotSystem.tailCorner, Equiv.symm_apply_apply]
  cases a with
  | star v => exact absurd rfl (hs v)
  | dc c =>
    by_cases h : c ∈ S.cut ∧ S.modeL c = false
    · refine ⟨(G.rev c, S.lastLab (G.rev c)), S.isTok_last _, .inr ?_⟩
      rw [hin]
      unfold betaD
      rw [ite_eq_right]
      rintro ⟨-, h'⟩
      rw [h.2] at h'
      exact absurd h' (by decide)
    · refine ⟨(G.rot c, S.firstLab (G.rot c)), S.isTok_first _, .inl ?_⟩
      rw [hout]
      unfold alphaD
      rw [ite_eq_right h]
  | lc c =>
    refine ⟨(G.rev c, .one), ?_, .inr ?_⟩
    · unfold IsTok
      have : G.rev c ∈ S.inc := ha
      simp [this]
    · simp only [beta, RotSystem.headCorner, G.rev_rev]
  | rc c =>
    refine ⟨(G.rot c, .two), ?_, .inl ?_⟩
    · unfold IsTok
      have : G.rot c ∈ S.inc := ha
      simp [this]
    · simp only [alpha, RotSystem.tailCorner, Equiv.symm_apply_apply]
  | xc c =>
    have hc : c ∈ S.cut := ha
    cases hm : S.modeL c
    · refine ⟨(G.rot c, S.firstLab (G.rot c)), S.isTok_first _, .inl ?_⟩
      rw [hout]
      unfold alphaD
      rw [ite_eq_left ⟨hc, hm⟩]
    · refine ⟨(G.rev c, S.lastLab (G.rev c)), S.isTok_last _, .inr ?_⟩
      rw [hin]
      unfold betaD
      rw [ite_eq_left ⟨hc, hm⟩]

/-! ### Property (1): pieces become paths -/

/-- The two ends of the E_R edge of `x`. -/
def IsEnd (x : E × Lab) (a : Copy G.Vertex E) : Prop := S.alpha x = a ∨ S.beta x = a

/-- An E_R edge between two copies, in either direction. -/
def ER (a b : Copy G.Vertex E) : Prop :=
  ∃ x : S.Tok, (S.alpha x.1 = a ∧ S.beta x.1 = b) ∨ (S.beta x.1 = a ∧ S.alpha x.1 = b)

theorem er_symm {a b : Copy G.Vertex E} (h : S.ER a b) : S.ER b a := by
  obtain ⟨x, hx | hx⟩ := h
  · exact ⟨x, .inr ⟨hx.2, hx.1⟩⟩
  · exact ⟨x, .inl ⟨hx.2, hx.1⟩⟩

/-- Two copies at the ends of the E_R edge of one token are joined by E_R edges. -/
theorem ends_conn (x : S.Tok) {a b : Copy G.Vertex E} (ha : S.IsEnd x.1 a) (hb : S.IsEnd x.1 b) :
    Relation.ReflTransGen S.ER a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact .refl
  · exact .single ⟨x, .inl ⟨rfl, rfl⟩⟩
  · exact .single ⟨x, .inr ⟨rfl, rfl⟩⟩
  · exact .refl

/-- Two tokens with a common end lie in one piece. -/
theorem piece_eq_of_end {x y : S.Tok} {a : Copy G.Vertex E}
    (hx : S.IsEnd x.1 a) (hy : S.IsEnd y.1 a) : S.piece x = S.piece y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [Subtype.ext (S.alpha_inj x.2 y.2 (hx.trans hy.symm))]
  · exact (S.piece_eq_of_link ((S.beta_eq_alpha_iff y.2 x.2).1 (hy.trans hx.symm))).symm
  · exact S.piece_eq_of_link ((S.beta_eq_alpha_iff x.2 y.2).1 (hx.trans hy.symm))
  · rw [Subtype.ext (S.beta_inj x.2 y.2 (hx.trans hy.symm))]

/-- The copies on E_R edges. -/
def EndCopy : Type u := {a : Copy G.Vertex E // ∃ x : S.Tok, S.IsEnd x.1 a}

/-- The piece of a copy on an E_R edge: the piece of its tokens. -/
noncomputable def pieceOf (a : S.EndCopy) : S.Piece := S.piece a.2.choose

/-- A copy on the E_R edge of `x` belongs to the piece of `x`. -/
theorem pieceOf_eq (a : S.EndCopy) {x : S.Tok}
    (hx : S.IsEnd x.1 a.1) : S.pieceOf a = S.piece x :=
  S.piece_eq_of_end a.2.choose_spec hx

/-- **Property (1) of Lemma R.** Two copies of one piece are joined by E_R edges. -/
theorem ring_conn (a b : S.EndCopy)
    (h : S.pieceOf a = S.pieceOf b) : Relation.ReflTransGen S.ER a.1 b.1 := by
  have hsymm : ∀ {a b : Copy G.Vertex E}, Relation.ReflTransGen S.ER a b →
      Relation.ReflTransGen S.ER b a := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact .head (S.er_symm hbc) ih
  have key : ∀ x y : S.Tok, Relation.EqvGen (fun x y : S.Tok => S.Link x.1 y.1) x y →
      ∀ a b, S.IsEnd x.1 a → S.IsEnd y.1 b → Relation.ReflTransGen S.ER a b := by
    intro x y hxy
    induction hxy with
    | rel x y hl =>
      intro a b ha hb
      have e : S.beta x.1 = S.alpha y.1 := (S.beta_eq_alpha_iff x.2 y.2).2 hl
      exact (S.ends_conn x ha (.inr rfl)).trans
        (e ▸ S.ends_conn y (.inl rfl) hb)
    | refl x => exact fun a b ha hb => S.ends_conn x ha hb
    | symm x y _ ih => exact fun a b ha hb => hsymm (ih b a hb ha)
    | trans x y z _ _ ih₁ ih₂ =>
      exact fun a b ha hb => (ih₁ a _ ha (.inl rfl)).trans (ih₂ _ b (.inl rfl) hb)
  have hab : S.piece a.2.choose = S.piece b.2.choose := h
  exact key _ _ (Quot.eqvGen_exact hab) _ _ a.2.choose_spec b.2.choose_spec

/-- An E_R edge joins two copies of one piece. -/
theorem pieceOf_er (a b : S.EndCopy) (h : S.ER a.1 b.1) :
    S.pieceOf a = S.pieceOf b := by
  obtain ⟨x, hx | hx⟩ := h
  · rw [S.pieceOf_eq a (.inl hx.1), S.pieceOf_eq b (.inr hx.2)]
  · rw [S.pieceOf_eq a (.inr hx.1), S.pieceOf_eq b (.inl hx.2)]

/-! ### Property (2): the E_C edges -/

theorem atTail_partner {x : E × Lab} (hx : S.IsTok x) : S.atTail (G.partner x) = !S.atTail x := by
  obtain ⟨d, l⟩ := x
  cases l
  · have hd : d ∉ S.inc := by unfold IsTok at hx; simpa using hx
    exact S.hostT_rev d hd
  · rfl
  · rfl

theorem isEnd_att (x : E × Lab) : S.IsEnd x (S.att x) := by
  unfold att
  split_ifs
  · exact .inl rfl
  · exact .inr rfl

/-- The end of the E_C edge of the pair of `x` at `x` lies on the path of the piece of `x`. -/
theorem pieceOf_att (x : S.Tok) :
    S.pieceOf ⟨S.att x.1, x, S.isEnd_att x.1⟩ = S.piece x :=
  S.pieceOf_eq _ (S.isEnd_att x.1)

/-- **Property (2) of Lemma R.** Both ends of the E_C edge of a pair are copies of its host. -/
theorem owner_att_partner {x : E × Lab} (hx : S.IsTok x) :
    G.owner (S.att (G.partner x)) = G.owner (S.att x) := by
  unfold att
  rw [S.atTail_partner hx]
  cases h : S.atTail x
  · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [S.owner_alpha, S.owner_beta]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [S.owner_alpha, S.owner_beta]
    show G.tail (G.rev (G.rev x.1)) = G.tail x.1
    rw [G.rev_rev]

/-- The host of the pair of an incised edge is the tail of the dart of its token labelled `1`. -/
theorem atTail_one (d : E) : S.atTail (d, .one) = true := rfl

end RData

end RotSystem

end SsspFlow
