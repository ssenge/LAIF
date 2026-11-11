import SsspFlow.GHatRun
import SsspFlow.SubNet

/-!
# The repaired graph as a network

The full repaired graph `hRot` with each edge subdivided twice is a simple graph
(`RotSystem.subNet`). The edges that `Ĝ_ℓ` drops can be given the length `⊤`, so distances in this
network are distances in `Ĝ_ℓ`.

* `RData.valid_tl`: every dart of `hRot` starts at a valid copy.
* `RData.isWalk_of_arcs`: a walk of `Ĝ_ℓ` with `k` arcs is a walk of `hRot` with `k` darts.
* `RData.arc_hop`: two valid copies whose vertices are joined by a walk of length at most `D` in `G`
  are joined by a walk of at most `4 D + 4` arcs of `Ĝ_ℓ`.
* `RData.hatNet_planar`, `RData.hatNet_diam`: for a connected planar `G` of diameter at most `D` and
  data without conflict with at most three cut corners, the subdivided repaired graph is planar and
  has diameter at most `12 D + 14`.
* `CutPath.Run.hatNet`: so for every level of a run, renamed to `Fin n`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- Every dart of `hRot` starts at a valid copy. -/
theorem valid_tl (x : S.HD) : S.Valid (S.tl x) := by
  obtain ⟨e, b⟩ := x
  cases e with
  | sp c => cases b <;> trivial
  | rim d =>
    cases b
    · exact S.valid_alphaD _
    · exact S.valid_betaD _
  | tok x =>
    cases b
    · exact S.valid_alpha x.2
    · exact S.valid_beta x.2
  | lsp a =>
    cases b
    · trivial
    · show G.inDart (G.headCorner a.1) ∈ S.inc
      rw [G.inDart_headCorner]
      exact a.2
  | rsp a =>
    cases b
    · trivial
    · show G.outDart (G.tailCorner a.1) ∈ S.inc
      rw [G.outDart_tailCorner]
      exact a.2
  | xsp c =>
    cases b
    · trivial
    · exact c.2

theorem hRot_tail_eq_iff (x y : S.HD) : S.hRot.tail x = S.hRot.tail y ↔ S.tl x = S.tl y :=
  S.listData.tail_eq_iff x y

/-- A walk of `Ĝ_ℓ` with `k` arcs is a walk of `hRot` with `k` darts. -/
theorem isWalk_of_arcs : ∀ {a b : Copy G.Vertex E} (q : FaceDisjoint.Walk S.Arc a b) (xa xb : S.HD),
    S.tl xa = a → S.tl xb = b →
    ∃ p : List S.HD, S.hRot.IsWalk (S.hRot.tail xa) p (S.hRot.tail xb) ∧ p.length = q.len
  | _, _, .nil _, xa, xb, ha, hb => ⟨[], (S.hRot_tail_eq_iff xa xb).2 (ha.trans hb.symm), rfl⟩
  | _, _, .cons e q, xa, xb, ha, hb => by
    obtain ⟨x, -, hx, hx'⟩ := S.keep_of_arc _ _ e
    obtain ⟨p, hp, hl⟩ := isWalk_of_arcs q (S.hrev x) xb hx' hb
    refine ⟨x :: p, ⟨(S.hRot_tail_eq_iff x xa).2 (hx.trans ha.symm), hp⟩, ?_⟩
    simp only [List.length_cons, FaceDisjoint.Walk.len, hl]

/-- A valid copy reaches the star centre of its vertex in at most two arcs, and back. -/
theorem star_reach {a : Copy G.Vertex E} (ha : S.Valid a) :
    (∃ q : FaceDisjoint.Walk S.Arc a (.star (G.owner a)), q.len ≤ 2) ∧
      ∃ q : FaceDisjoint.Walk S.Arc (.star (G.owner a)) a, q.len ≤ 2 := by
  by_cases hs : ∀ v, a ≠ .star v
  · obtain ⟨⟨p, hp⟩, q, hq⟩ := S.star_walk ha hs rfl
    have := a.leaf_le_one
    exact ⟨⟨q, by omega⟩, p, by omega⟩
  · simp only [not_forall, not_not] at hs
    obtain ⟨v, rfl⟩ := hs
    exact ⟨⟨.nil _, by simp [FaceDisjoint.Walk.len]⟩, .nil _, by simp [FaceDisjoint.Walk.len]⟩

/-- **Hops between copies.** -/
theorem arc_hop (hcut : S.cut.card ≤ 3) {a b : Copy G.Vertex E} (ha : S.Valid a) (hb : S.Valid b)
    {p : List E} (hp : G.IsWalk (G.owner a) p (G.owner b)) :
    ∃ q : FaceDisjoint.Walk S.Arc a b, q.len ≤ 4 * p.length + 4 := by
  obtain ⟨⟨q₁, h₁⟩, -⟩ := S.star_reach ha
  obtain ⟨-, q₂, h₂⟩ := S.star_reach hb
  obtain ⟨q, hq⟩ := S.hop_walk hcut p hp
  refine ⟨q₁.append (q.append q₂), ?_⟩
  simp only [FaceDisjoint.Walk.len_append]
  omega

/-- Any two vertices of `hRot` are joined by a walk of at most `4 D + 4` darts. -/
theorem hRot_hop (hcut : S.cut.card ≤ 3) {D : ℕ}
    (hD : ∀ u v : G.Vertex, ∃ p, G.IsWalk u p v ∧ p.length ≤ D) (u v : S.hRot.Vertex) :
    ∃ p, S.hRot.IsWalk u p v ∧ p.length ≤ 4 * D + 4 := by
  obtain ⟨xu, rfl⟩ := S.hRot.exists_tail_eq u
  obtain ⟨xv, rfl⟩ := S.hRot.exists_tail_eq v
  obtain ⟨p, hp, hpD⟩ := hD (G.owner (S.tl xu)) (G.owner (S.tl xv))
  obtain ⟨q, hq⟩ := S.arc_hop hcut (S.valid_tl xu) (S.valid_tl xv) hp
  obtain ⟨p', hp', hl⟩ := S.isWalk_of_arcs q xu xv rfl rfl
  exact ⟨p', hp', by omega⟩

/-- **The subdivided repaired graph is planar.** -/
theorem hatNet_planar (hP : G.Planar) (hc : G.Connected) (hN : S.NoConflict) :
    S.hRot.subNet.toRot.Planar :=
  S.hRot.subNet_planar (S.hRot_planar hP hc hN) (S.hRot_connected hc)

/-- **The subdivided repaired graph has diameter at most `12 D + 14`.** -/
theorem hatNet_diam (hcut : S.cut.card ≤ 3) {D : ℕ}
    (hD : ∀ u v : G.Vertex, ∃ p, G.IsWalk u p v ∧ p.length ≤ D) :
    S.hRot.subNet.DiamLE (12 * D + 14) := by
  have := S.hRot.subNet_diam (S.hRot_hop hcut hD)
  rwa [show 3 * (4 * D + 4) + 2 = 12 * D + 14 by ring] at this

/-- **The subdivided repaired graph as a network on `Fin n`.** -/
theorem hatNet_fin (hP : G.Planar) (hc : G.Connected) (hN : S.NoConflict) (hcut : S.cut.card ≤ 3)
    {D : ℕ} (hD : ∀ u v : G.Vertex, ∃ p, G.IsWalk u p v ∧ p.length ≤ D) :
    ∃ (n : ℕ) (e : S.hRot.Vertex ⊕ S.HD ≃ Fin n),
      (S.hRot.subNet.relabel e).toRot.Planar ∧ (S.hRot.subNet.relabel e).DiamLE (12 * D + 14) := by
  classical
  let e := Fintype.equivFin (S.hRot.Vertex ⊕ S.HD)
  exact ⟨_, e, S.hRot.subNet.relabel_planar e (S.hatNet_planar hP hc hN)
    (S.hRot.subNet_G_connected (S.hRot_connected hc)) S.hRot.subNet_noIso,
    S.hRot.subNet.relabel_diam e (S.hatNet_diam hcut hD)⟩

end RData

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} {C : G.dual.CutPath}
  {hR : G.dual.Planar} {hC : G.dual.Connected} {g : E → ℝ≥0∞} {hg : ∀ x, g (G.dual.rev x) = g x}

namespace CutPath

variable (r : Run hR hC hg C.Γ (C.liveOne g) 0 C.m) (ℓ : ℕ) (modeL hostT : E → Bool)
  (hhost : ∀ d, (d, false) ∉ C.Γ ∪ r.steps ℓ → hostT (G.rev d) = !hostT d)

/-- A level of a run has at most two cut corners. -/
theorem Run.card_cut : (r.data ℓ modeL hostT hhost).cut.card ≤ 2 := by
  classical
  have hsub : (r.data ℓ modeL hostT hhost).cut ⊆ {C.cs, C.ct} := fun c hc => by
    rcases r.cut_data ℓ modeL hostT hhost hc with rfl | rfl <;> simp
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- **Every level of a run as a planar network on `Fin n` of diameter at most `12 D + 14`.** -/
theorem Run.hatNet (hP : G.Planar) (hc : G.Connected) {D' : ℕ}
    (hD : ∀ u v : G.Vertex, ∃ p, G.IsWalk u p v ∧ p.length ≤ D') :
    ∃ (n : ℕ) (e : (r.data ℓ modeL hostT hhost).hRot.Vertex ⊕ (r.data ℓ modeL hostT hhost).HD ≃ Fin n),
      ((r.data ℓ modeL hostT hhost).hRot.subNet.relabel e).toRot.Planar ∧
        ((r.data ℓ modeL hostT hhost).hRot.subNet.relabel e).DiamLE (12 * D' + 14) :=
  RData.hatNet_fin _ hP hc (r.noConflict ℓ modeL hostT hhost)
    ((r.card_cut ℓ modeL hostT hhost).trans (by norm_num)) hD

end CutPath

end RotSystem

end SsspFlow
