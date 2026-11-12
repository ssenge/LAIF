import SsspFlow.GHatLevelWalk
import SsspFlow.GHatSplit

/-!
# The vertices visited by the transferred walks

The walks of `RData.walk_project`, `RData.project` and `RData.split_walk` visit the same places:

* `RData.walk_project_supp`: the walk of `Ĝ_ℓ` from a walk of finite length of the network of a
  level visits exactly the copies of the nodes of that walk.
* `RData.project_supp`: the walk of the token graph from a walk of `Ĝ_ℓ` between copies on E_R
  edges, of weight below `M`, visits exactly the pieces of the copies of that walk.
* `RData.split_walk_visits`: the walk of the split from a walk of the token graph visits exactly
  the vertices of the pieces of that walk.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Token

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

variable {lam : S.Tok → ℝ} {M : ℝ}

/-- **Projected walks visit the pieces of their copies.** A walk of `Ĝ_ℓ` between copies on E_R
edges, of weight below `M`, projects to a walk of the token graph of the same weight whose pieces
are exactly the pieces of the copies of the walk. -/
theorem project_supp (hlam : ∀ x, 0 ≤ lam x) (hM : 0 ≤ M) : ∀ {a b : Copy G.Vertex E}
    (p : FaceDisjoint.Walk S.Arc a b), p.wt (S.w lam M) < M →
    ∀ (ha : ∃ x : S.Tok, S.IsEnd x.1 a) (hb : ∃ x : S.Tok, S.IsEnd x.1 b) {f g : S.Piece},
    S.pieceOf ⟨a, ha⟩ = f → S.pieceOf ⟨b, hb⟩ = g →
    ∃ P : FaceDisjoint.Walk S.DArc f g, P.wt (S.dw lam) = p.wt (S.w lam M) ∧
      (∀ f' ∈ P.support, ∃ c ∈ p.support, ∃ hc : ∃ x : S.Tok, S.IsEnd x.1 c,
        S.pieceOf ⟨c, hc⟩ = f') ∧
      ∀ c ∈ p.support, ∃ hc : ∃ x : S.Tok, S.IsEnd x.1 c, S.pieceOf ⟨c, hc⟩ ∈ P.support := by
  intro a b p
  induction p with
  | nil a =>
    intro _ ha hb f g hf hg
    obtain rfl : f = g := hf.symm.trans hg
    refine ⟨.nil _, by simp, fun f' hf' => ⟨a, by simp, ha, ?_⟩, fun c hc => ?_⟩
    · rw [FaceDisjoint.Walk.support_nil, List.mem_singleton] at hf'
      rw [hf', hf]
    · rw [FaceDisjoint.Walk.support_nil, List.mem_singleton] at hc
      subst hc
      exact ⟨ha, by rw [hf]; simp⟩
  | cons e q ih =>
    intro hlt ha hb f g hf hg
    rw [FaceDisjoint.Walk.wt_cons] at hlt
    have hq : q.wt (S.w lam M) < M := by
      linarith [S.w_nonneg hlam hM _ _ e]
    have hq0 := S.wt_nonneg hlam hM q
    cases e with
    | er x =>
      obtain ⟨P, hP, hF, hB⟩ := ih hq ⟨x, .inr rfl⟩ hb
        ((S.pieceOf_eq _ (.inr rfl)).trans ((S.pieceOf_eq ⟨_, ha⟩ (.inl rfl)).symm.trans hf)) hg
      refine ⟨P, by simp [w, hP], fun f' hf' => ?_, fun c hc => ?_⟩
      · obtain ⟨c, hc, hc', h⟩ := hF f' hf'
        exact ⟨c, List.mem_cons_of_mem _ hc, hc', h⟩
      · rw [FaceDisjoint.Walk.support_cons, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ⟨ha, by rw [hf]; exact P.start_mem⟩
        · exact hB c hc
    | er' x =>
      obtain ⟨P, hP, hF, hB⟩ := ih hq ⟨x, .inl rfl⟩ hb
        ((S.pieceOf_eq _ (.inl rfl)).trans ((S.pieceOf_eq ⟨_, ha⟩ (.inr rfl)).symm.trans hf)) hg
      refine ⟨P, by simp [w, hP], fun f' hf' => ?_, fun c hc => ?_⟩
      · obtain ⟨c, hc, hc', h⟩ := hF f' hf'
        exact ⟨c, List.mem_cons_of_mem _ hc, hc', h⟩
      · rw [FaceDisjoint.Walk.support_cons, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ⟨ha, by rw [hf]; exact P.start_mem⟩
        · exact hB c hc
    | ec x =>
      obtain ⟨P, hP, hF, hB⟩ := ih hq ⟨S.partnerTok x, S.isEnd_att (S.partnerTok x).1⟩ hb
        (S.pieceOf_eq _ (S.isEnd_att (S.partnerTok x).1)) hg
      have hx : S.piece x = f := (S.pieceOf_eq ⟨_, ha⟩ (S.isEnd_att x.1)).symm.trans hf
      refine ⟨.cons ⟨x, hx, rfl⟩ P, ?_, fun f' hf' => ?_, fun c hc => ?_⟩
      · rw [FaceDisjoint.Walk.wt_cons, FaceDisjoint.Walk.wt_cons, hP]
        rfl
      · rw [FaceDisjoint.Walk.support_cons, List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact ⟨_, by simp, ha, hf⟩
        · obtain ⟨c, hc, hc', h⟩ := hF f' hf'
          exact ⟨c, List.mem_cons_of_mem _ hc, hc', h⟩
      · rw [FaceDisjoint.Walk.support_cons, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ⟨ha, by rw [hf]; simp⟩
        · obtain ⟨hc', h⟩ := hB c hc
          exact ⟨hc', List.mem_cons_of_mem _ h⟩
    | es h =>
      exfalso
      simp only [w] at hlt
      linarith
    | es' h =>
      exfalso
      simp only [w] at hlt
      linarith

variable (c : E → ℝ)

/-- **Split walks visit the vertices of their pieces.** A walk of the token graph gives a walk of the
split of the same weight, for weights that agree on the two darts of an edge, whose vertices are
exactly the vertices of the pieces of the walk. -/
theorem split_walk_visits (hcr : ∀ d, c (G.rev d) = c d) : ∀ {f h : S.Piece}
    (P : FaceDisjoint.Walk S.DArc f h), ∃ p : List (E × Bool),
      S.dualSplit.IsWalk (S.vertexEquiv f) p (S.vertexEquiv h) ∧
      (p.map fun z => c z.1).sum = P.wt (S.dw fun x => c x.1.1) ∧
      ∀ v, (v = S.vertexEquiv f ∨ ∃ y ∈ p, S.dualSplit.head y = v) ↔
        ∃ f' ∈ P.support, S.vertexEquiv f' = v
  | _, _, .nil _ => ⟨[], rfl, by simp, fun v => by simp [eq_comm]⟩
  | _, _, .cons (b := m) x P => by
    obtain ⟨p, hp, hw, hv⟩ := split_walk_visits hcr P
    have hhd : S.dualSplit.head (G.tokDart x.1.1) = S.vertexEquiv m := by
      rw [S.head_tokDart, x.2.2]
    refine ⟨G.tokDart x.1.1 :: p, (S.dualSplit.isWalk_cons _ _ _ _).2 ⟨?_, ?_⟩, ?_, fun v => ?_⟩
    · exact (S.vertexEquiv_piece x.1).symm.trans (congrArg S.vertexEquiv x.2.1)
    · rw [hhd]
      exact hp
    · simp only [List.map_cons, List.sum_cons, hw, FaceDisjoint.Walk.wt_cons, G.tokDart_fst, hcr,
        dw]
    · rw [FaceDisjoint.Walk.support_cons]
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [hhd, ← hv v]
      constructor
      · rintro (h | h | h)
        · exact .inl h.symm
        · exact .inr (.inl h.symm)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl h.symm
        · exact .inr (.inl h.symm)
        · exact .inr (.inr h)

end Token

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- **Walks project onto their copies.** A walk of finite length of the network of a level gives a
walk of `Ĝ_ℓ` between the copies of its ends, of the same length, whose copies are exactly the
copies of the nodes of the walk. -/
theorem walk_project_supp : ∀ {z z' : Fin (n * (n * 21))} (p : SsspFlow.Walk (S.levelNet hN).G.Adj z z'),
    p.wt (lenTop (S.levelLen hN lam M)) ≠ ⊤ →
    ∃ q : FaceDisjoint.Walk S.Arc (S.copyAt hN z) (S.copyAt hN z'),
      ((S.awt lam M q : ℕ) : ℝ≥0∞) = p.wt (lenTop (S.levelLen hN lam M)) ∧
        (∀ c ∈ q.support, ∃ y ∈ p.support, S.copyAt hN y = c) ∧
        ∀ y ∈ p.support, S.copyAt hN y ∈ q.support
  | _, _, .nil z, _ => ⟨.nil _, by simp [awt, SsspFlow.Walk.wt], fun c hc => ⟨z, by simp,
      (List.mem_singleton.1 hc).symm⟩, fun y hy => by
        rw [List.mem_singleton.1 hy]; simp⟩
  | z, _, .cons (b := y) e p, hfin => by
    rw [SsspFlow.Walk.wt_cons] at hfin
    have hf1 : S.levelLen hN lam M z y ≠ ⊤ := fun h0 => hfin (by simp [lenTop, h0])
    have hf2 : p.wt (lenTop (S.levelLen hN lam M)) ≠ ⊤ := fun h0 => hfin (by rw [h0, add_top])
    obtain ⟨q, hq, hs, hs'⟩ := walk_project_supp p hf2
    rcases S.levelStep_cases hN lam M e hf1 with ⟨hc, h0⟩ | ⟨e', he'⟩
    · rw [hc]
      refine ⟨q, ?_, fun c hc' => ?_, fun y' hy' => ?_⟩
      · rw [SsspFlow.Walk.wt_cons, hq]
        simp [lenTop, h0]
      · obtain ⟨y', hy', hc''⟩ := hs c hc'
        exact ⟨y', by simp [hy'], hc''⟩
      · simp only [SsspFlow.Walk.support_cons, List.mem_cons] at hy'
        rcases hy' with rfl | hy'
        · rw [hc]
          exact q.start_mem
        · exact hs' y' hy'
    · refine ⟨.cons e' q, ?_, fun c hc' => ?_, fun y' hy' => ?_⟩
      · rw [SsspFlow.Walk.wt_cons, ← hq]
        simp only [awt, Nat.cast_add, lenTop]
        rw [← he']
        rfl
      · simp only [FaceDisjoint.Walk.support_cons, List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨z, by simp, rfl⟩
        · obtain ⟨y', hy', hc''⟩ := hs c hc'
          exact ⟨y', by simp [hy'], hc''⟩
      · simp only [SsspFlow.Walk.support_cons, List.mem_cons] at hy'
        rw [FaceDisjoint.Walk.support_cons]
        rcases hy' with rfl | hy'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs' y' hy')

end RData

end RotSystem

end SsspFlow
