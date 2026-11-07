import SsspFlow.GHat

/-!
# Distances in the repaired graph

The repaired graph `Ĝ_ℓ` of Definition R as a multigraph on the copies (`RData.Arc`): the E_R edge
of each token in both directions, for each token `x` the arc of the E_C edge of its pair from
`att(x)` to `att(x')`, where `x'` is the other token of the pair, and each E_S edge in both
directions. Its arcs weigh `0` on E_R edges, `lam x` on the E_C arc of `x` and `M` on E_S edges
(`RData.w`). The token graph has the pieces as nodes and, for each token `x`, an arc from the piece
of `x` to the piece of `x'` of weight `lam x` (`RData.DArc`, `RData.dw`).

Let `lam ≥ 0` and `M ≥ 0`, and let `a` and `b` be copies on E_R edges, of the pieces `f` and `g`.
* A walk of the token graph from `f` to `g` lifts to a walk of `Ĝ_ℓ` from `a` to `b` of the same
  weight, along the E_R paths of the pieces (`lift`).
* A walk of `Ĝ_ℓ` from `a` to `b` of weight below `M` uses no E_S edge, and it projects to a walk of
  the token graph from `f` to `g` of the same weight (`project`).

So the distance from `a` to `b` in `Ĝ_ℓ` is the distance from `f` to `g` in the token graph if the
latter is below `M`, and at least `M` otherwise (`gdist_eq`). A walk of the token graph that starts
in a set of pieces closed under pairs stays in it (`mem_of_walk`). This is the distance bullet of
Theorem D: there the E_C edges of the live annuli weigh `K·c(e) + 1`, all other E_C edges `M`, and
each live annulus is closed under pairs, so the distance from `f` is taken in the annulus of `f`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

namespace RData

universe u

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- The arcs of `Ĝ_ℓ`. -/
inductive Arc : Copy G.Vertex E → Copy G.Vertex E → Type u
  | er (x : S.Tok) : Arc (S.alpha x.1) (S.beta x.1)
  | er' (x : S.Tok) : Arc (S.beta x.1) (S.alpha x.1)
  | ec (x : S.Tok) : Arc (S.att x.1) (S.att (G.partner x.1))
  | es {a b : Copy G.Vertex E} (h : S.ES a b) : Arc a b
  | es' {a b : Copy G.Vertex E} (h : S.ES a b) : Arc b a

variable (lam : S.Tok → ℝ) (M : ℝ)

/-- The arc weights of `Ĝ_ℓ`. -/
def w : ∀ a b, S.Arc a b → ℝ
  | _, _, .er _ => 0
  | _, _, .er' _ => 0
  | _, _, .ec x => lam x
  | _, _, .es _ => M
  | _, _, .es' _ => M

/-- The arcs of the token graph from the piece `f` to the piece `g`. -/
abbrev DArc (f g : S.Piece) : Type u :=
  {x : S.Tok // S.piece x = f ∧ S.piece (S.partnerTok x) = g}

/-- The arc weights of the token graph. -/
def dw : ∀ f g, S.DArc f g → ℝ := fun _ _ x => lam x.1

/-- The distance in `Ĝ_ℓ`. -/
noncomputable def gdist (a b : Copy G.Vertex E) : EReal :=
  ⨅ p : FaceDisjoint.Walk S.Arc a b, ((p.wt (S.w lam M) : ℝ) : EReal)

/-- The distance in the token graph. -/
noncomputable def ddist (f g : S.Piece) : EReal :=
  ⨅ P : FaceDisjoint.Walk S.DArc f g, ((P.wt (S.dw lam) : ℝ) : EReal)

theorem er_walk {a b : Copy G.Vertex E} (h : S.ER a b) :
    ∃ p : FaceDisjoint.Walk S.Arc a b, p.wt (S.w lam M) = 0 := by
  obtain ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact ⟨.cons (.er x) (.nil _), by simp [w]⟩
  · exact ⟨.cons (.er' x) (.nil _), by simp [w]⟩

/-- Copies joined by E_R edges are joined by a walk of weight `0`. -/
theorem ring_walk {a b : Copy G.Vertex E} (h : Relation.ReflTransGen S.ER a b) :
    ∃ p : FaceDisjoint.Walk S.Arc a b, p.wt (S.w lam M) = 0 := by
  induction h with
  | refl => exact ⟨.nil _, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := S.er_walk lam M hbc
    exact ⟨p.append q, by simp [hp, hq]⟩

/-- **Lift.** A walk of the token graph lifts to a walk of `Ĝ_ℓ` of the same weight between any
copies of its end pieces. -/
theorem lift : ∀ {f g : S.Piece} (P : FaceDisjoint.Walk S.DArc f g) (a b : S.EndCopy),
    S.pieceOf a = f → S.pieceOf b = g →
    ∃ p : FaceDisjoint.Walk S.Arc a.1 b.1, p.wt (S.w lam M) = P.wt (S.dw lam) := by
  intro f g P
  induction P with
  | nil f =>
    intro a b ha hb
    obtain ⟨p, hp⟩ := S.ring_walk lam M (S.ring_conn a b (ha.trans hb.symm))
    exact ⟨p, by simp [hp]⟩
  | cons e P ih =>
    intro a b ha hb
    obtain ⟨x, hxf, hxg⟩ := e
    obtain ⟨p₀, h₀⟩ := S.ring_walk lam M (S.ring_conn a ⟨S.att x.1, x, S.isEnd_att x.1⟩
      (ha.trans ((S.pieceOf_att x).trans hxf).symm))
    obtain ⟨p₁, h₁⟩ := ih ⟨S.att (G.partner x.1), S.partnerTok x, S.isEnd_att _⟩ b
      ((S.pieceOf_att (S.partnerTok x)).trans hxg) hb
    refine ⟨p₀.append (.cons (.ec x) p₁), ?_⟩
    rw [FaceDisjoint.Walk.wt_append, FaceDisjoint.Walk.wt_cons, FaceDisjoint.Walk.wt_cons, h₀, h₁,
      zero_add]
    rfl

variable {lam M}

theorem w_nonneg (hlam : ∀ x, 0 ≤ lam x) (hM : 0 ≤ M) : ∀ a b (e : S.Arc a b), 0 ≤ S.w lam M a b e
  | _, _, .er _ => le_rfl
  | _, _, .er' _ => le_rfl
  | _, _, .ec x => hlam x
  | _, _, .es _ => hM
  | _, _, .es' _ => hM

theorem wt_nonneg (hlam : ∀ x, 0 ≤ lam x) (hM : 0 ≤ M) :
    ∀ {a b : Copy G.Vertex E} (p : FaceDisjoint.Walk S.Arc a b), 0 ≤ p.wt (S.w lam M)
  | _, _, .nil _ => le_rfl
  | _, _, .cons e p => by
    rw [FaceDisjoint.Walk.wt_cons]
    exact add_nonneg (S.w_nonneg hlam hM _ _ e) (wt_nonneg hlam hM p)

/-- **Project.** A walk of `Ĝ_ℓ` between copies on E_R edges of weight below `M` projects to a
walk of the token graph between their pieces of the same weight. -/
theorem project (hlam : ∀ x, 0 ≤ lam x) (hM : 0 ≤ M) : ∀ {a b : Copy G.Vertex E}
    (p : FaceDisjoint.Walk S.Arc a b), p.wt (S.w lam M) < M →
    ∀ (ha : ∃ x : S.Tok, S.IsEnd x.1 a) (hb : ∃ x : S.Tok, S.IsEnd x.1 b) {f g : S.Piece},
    S.pieceOf ⟨a, ha⟩ = f → S.pieceOf ⟨b, hb⟩ = g →
    ∃ P : FaceDisjoint.Walk S.DArc f g, P.wt (S.dw lam) = p.wt (S.w lam M) := by
  intro a b p
  induction p with
  | nil a =>
    intro _ ha hb f g hf hg
    obtain rfl : f = g := hf.symm.trans hg
    exact ⟨.nil _, by simp⟩
  | cons e q ih =>
    intro hlt ha hb f g hf hg
    rw [FaceDisjoint.Walk.wt_cons] at hlt
    have hq : q.wt (S.w lam M) < M := by
      linarith [S.w_nonneg hlam hM _ _ e]
    have hq0 := S.wt_nonneg hlam hM q
    cases e with
    | er x =>
      obtain ⟨P, hP⟩ := ih hq ⟨x, .inr rfl⟩ hb
        ((S.pieceOf_eq _ (.inr rfl)).trans ((S.pieceOf_eq ⟨_, ha⟩ (.inl rfl)).symm.trans hf)) hg
      exact ⟨P, by simp [w, hP]⟩
    | er' x =>
      obtain ⟨P, hP⟩ := ih hq ⟨x, .inl rfl⟩ hb
        ((S.pieceOf_eq _ (.inl rfl)).trans ((S.pieceOf_eq ⟨_, ha⟩ (.inr rfl)).symm.trans hf)) hg
      exact ⟨P, by simp [w, hP]⟩
    | ec x =>
      obtain ⟨P, hP⟩ := ih hq ⟨S.partnerTok x, S.isEnd_att (S.partnerTok x).1⟩ hb
        (S.pieceOf_eq _ (S.isEnd_att (S.partnerTok x).1)) hg
      have hx : S.piece x = f := (S.pieceOf_eq ⟨_, ha⟩ (S.isEnd_att x.1)).symm.trans hf
      refine ⟨.cons ⟨x, hx, rfl⟩ P, ?_⟩
      rw [FaceDisjoint.Walk.wt_cons, FaceDisjoint.Walk.wt_cons, hP]
      rfl
    | es h =>
      exfalso
      simp only [w] at hlt
      linarith
    | es' h =>
      exfalso
      simp only [w] at hlt
      linarith

/-- **The distance bullet of Theorem D.** For copies `a`, `b` on E_R edges, the distance in `Ĝ_ℓ`
is the distance of their pieces in the token graph if that is below `M`, and at least `M`
otherwise. -/
theorem gdist_eq (hlam : ∀ x, 0 ≤ lam x) (hM : 0 ≤ M) (a b : S.EndCopy) :
    (S.ddist lam (S.pieceOf a) (S.pieceOf b) < M →
      S.gdist lam M a.1 b.1 = S.ddist lam (S.pieceOf a) (S.pieceOf b)) ∧
    ((M : EReal) ≤ S.ddist lam (S.pieceOf a) (S.pieceOf b) →
      (M : EReal) ≤ S.gdist lam M a.1 b.1) := by
  have hup : S.gdist lam M a.1 b.1 ≤ S.ddist lam (S.pieceOf a) (S.pieceOf b) := by
    refine le_iInf fun P => ?_
    obtain ⟨p, hp⟩ := S.lift lam M P a b rfl rfl
    rw [← hp]
    exact iInf_le _ p
  have hlow : min (S.ddist lam (S.pieceOf a) (S.pieceOf b)) (M : EReal) ≤
      S.gdist lam M a.1 b.1 := by
    refine le_iInf fun p => ?_
    by_cases hp : p.wt (S.w lam M) < M
    · obtain ⟨P, hP⟩ := S.project hlam hM p hp a.2 b.2 rfl rfl
      refine min_le_of_left_le ?_
      rw [← hP]
      exact iInf_le _ P
    · refine min_le_of_right_le ?_
      exact EReal.coe_le_coe_iff.2 (not_lt.1 hp)
  constructor
  · intro hlt
    refine le_antisymm hup ?_
    rwa [min_eq_left hlt.le] at hlow
  · intro hle
    rwa [min_eq_right hle] at hlow

/-- A walk of the token graph from a set of pieces closed under pairs stays in it. -/
theorem mem_of_walk {A : Set S.Piece}
    (hA : ∀ x : S.Tok, S.piece x ∈ A → S.piece (S.partnerTok x) ∈ A) :
    ∀ {f g : S.Piece} (P : FaceDisjoint.Walk S.DArc f g), f ∈ A → g ∈ A ∧
      ∀ h ∈ P.support, h ∈ A := by
  intro f g P
  induction P with
  | nil f => exact fun hf => ⟨hf, fun h hh => by simp at hh; exact hh ▸ hf⟩
  | cons e P ih =>
    intro hf
    obtain ⟨x, hxf, hxg⟩ := e
    have hg' := hxg ▸ hA x (hxf ▸ hf)
    obtain ⟨hg, hP⟩ := ih hg'
    refine ⟨hg, fun h hh => ?_⟩
    rw [FaceDisjoint.Walk.support_cons, List.mem_cons] at hh
    rcases hh with rfl | hh
    · exact hf
    · exact hP h hh

end RData

end RotSystem

namespace FaceDisjoint.Walk

universe v

variable {N : Type v} {A : N → N → Type v}

/-- The cost of a walk for natural arc costs. -/
def nwt (c : ∀ a b, A a b → ℕ) : {a b : N} → Walk A a b → ℕ
  | _, _, nil _ => 0
  | _, _, @cons _ _ a m _ e p => c a m e + p.nwt c

@[simp] theorem nwt_nil (c : ∀ a b, A a b → ℕ) (a : N) : (nil a : Walk A a a).nwt c = 0 := rfl

@[simp] theorem nwt_cons (c : ∀ a b, A a b → ℕ) {a b d : N} (e : A a b) (p : Walk A b d) :
    (cons e p).nwt c = c a b e + p.nwt c := rfl

theorem nwt_append (c : ∀ a b, A a b → ℕ) : ∀ {a b d : N} (p : Walk A a b) (q : Walk A b d),
    (p.append q).nwt c = p.nwt c + q.nwt c
  | _, _, _, nil _, q => by simp
  | _, _, _, cons e p, q => by simp [nwt_append c p q, add_assoc]

/-- The weights `K·c + 1` for natural arc costs `c`. -/
def scaled (c : ∀ a b, A a b → ℕ) (K : ℕ) : ∀ a b, A a b → ℝ :=
  fun a b e => ((K * c a b e + 1 : ℕ) : ℝ)

/-- The natural arc costs as real weights. -/
def cost (c : ∀ a b, A a b → ℕ) : ∀ a b, A a b → ℝ := fun a b e => (c a b e : ℝ)

theorem wt_scaled (c : ∀ a b, A a b → ℕ) (K : ℕ) : ∀ {a b : N} (p : Walk A a b),
    p.wt (scaled c K) = ((K * p.nwt c + p.len : ℕ) : ℝ)
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    rw [wt_cons, wt_scaled c K p, nwt_cons, len_cons]
    simp only [scaled]
    push_cast
    ring

theorem wt_cost (c : ∀ a b, A a b → ℕ) : ∀ {a b : N} (p : Walk A a b),
    p.wt (cost c) = (p.nwt c : ℝ)
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    rw [wt_cons, wt_cost c p, nwt_cons]
    simp [cost]

/-- **Decoding.** Let `K` be at least the number of nodes. A walk of least weight for the weights
`K·c + 1` has fewer than `K` arcs and least cost among all walks between its ends, so its weight
divided by `K` is the least cost. -/
theorem decode [Fintype N] (c : ∀ a b, A a b → ℕ) (K : ℕ) (hK : Fintype.card N ≤ K) {a b : N}
    (Q : Walk A a b) (hQ : ∀ Q' : Walk A a b, Q.wt (scaled c K) ≤ Q'.wt (scaled c K)) :
    Q.len < K ∧ (∀ Q' : Walk A a b, Q.nwt c ≤ Q'.nwt c) ∧
      (K * Q.nwt c + Q.len) / K = Q.nwt c := by
  have hnd : Q.support.Nodup := by
    by_contra hd
    obtain ⟨y, p₁, cyc, p₂, hc, rfl⟩ := Q.dup_split hd
    have h := hQ (p₁.append p₂)
    simp only [wt_scaled, nwt_append, len_append] at h
    push_cast at h
    have h1 : (0 : ℝ) < cyc.len := by exact_mod_cast hc
    have h2 : (0 : ℝ) ≤ (K : ℝ) * (cyc.nwt c : ℝ) := by positivity
    linarith
  have hlen : Q.len < K := lt_of_lt_of_le (Q.len_lt_of_nodup hnd) hK
  have hK0 : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hlen
  refine ⟨hlen, fun Q' => ?_, ?_⟩
  · obtain ⟨Q'', hl, hw⟩ := Walk.short (cost c) (fun y cyc => by rw [wt_cost]; positivity) _ Q' rfl
    rw [wt_cost, wt_cost] at hw
    have hw' : Q''.nwt c ≤ Q'.nwt c := by exact_mod_cast hw
    have h := hQ Q''
    rw [wt_scaled, wt_scaled] at h
    have h' : K * Q.nwt c + Q.len ≤ K * Q''.nwt c + Q''.len := by exact_mod_cast h
    have hl' : Q''.len < K := lt_of_lt_of_le hl hK
    have hlt : Q.nwt c < Q''.nwt c + 1 := by
      by_contra hcon
      have h3 := Nat.mul_le_mul_left K (not_lt.1 hcon)
      rw [mul_add, mul_one] at h3
      linarith
    omega
  · rw [Nat.mul_add_div hK0, Nat.div_eq_of_lt hlen, add_zero]

end FaceDisjoint.Walk

end SsspFlow
