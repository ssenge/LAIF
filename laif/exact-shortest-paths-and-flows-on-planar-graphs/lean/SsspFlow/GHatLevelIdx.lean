import SsspFlow.GHatSupport
import SsspFlow.GHatLevelShortest

/-!
# The indices of the cut path on a short walk of a level

The shortest walk of the annulus that a walk of the network of a level gives (`RData.level_shortest`)
visits the vertices of the pieces of the copies of the nodes of that walk. So its indices on the cut
path (`CutPath.idx`) are the indices `r` of the corners `p_r^σ` that lie, in the cut along the path,
at a vertex of the piece of the copy of a node of the walk.

* `RData.cut_tail_of_split`: darts at one vertex of the split of `S` lie at one vertex of the cut,
  when the corners of the cut are corners of `S`.
* `RData.level_shortest_idx`: a walk of the network of a level between copies on E_R edges of the
  pieces at `κ0(t)` and `κ1(t)`, of length below `M` and at most `λ_t`, gives a shortest walk of the
  annulus of the same length whose indices on the cut path are the indices at the pieces of the
  copies of its nodes.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- Darts at one vertex of the split of `S` lie at one vertex of the cut along `C`, when the
corners of the cut are corners of `S`. -/
theorem cut_tail_of_split {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)
    {C : G.dual.CutPath} (hsub : C.Γ ⊆ S.Γ) {z z' : E × Bool}
    (h : S.dualSplit.tail z = S.dualSplit.tail z') : C.cut.tail z = C.cut.tail z' :=
  (C.cut.tail_eq_iff _ _).2
    (G.dual.fconnect_of_split_subset hsub (((G.dual.double.split S.Γ).tail_eq_iff _ _).1 h))

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {Γ : Finset (N.G.Dart × Bool)}

/-- **Indices of the cut path on a short walk of a level.** Under the conditions of
`RData.level_shortest`, the walk of the network of a level gives a shortest walk of the annulus of
the same length, and an index `r ≤ m` is an index of that walk on the cut path exactly when some
corner `p_r^σ` lies, in the cut along the path, at the vertex of the piece of the copy of a node of
the walk. -/
theorem level_shortest_idx (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    {u v : S.hRot.Vertex} (p : SsspFlow.Walk (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inl u))
      ((S.levelPad hN).ι (.inl v)))
    (hp : p.wt (lenTop (S.levelLen hN lam M)) < M)
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hle : p.wt (lenTop (S.levelLen hN lam M)) ≤ C.lamD g t) :
    ∃ ps : List (N.G.Dart × Bool), L.Shortest t ps ∧
      (ps.map (g ∘ Prod.fst)).sum = p.wt (lenTop (S.levelLen hN lam M)) ∧
      ∀ r, r ∈ C.idx (L.κ0 t) ps ↔ r ≤ C.m ∧ ∃ σ, ∃ y ∈ p.support,
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
          S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
          C.cut.tail z = C.cut.tail (C.k σ r) := by
  have hfin : p.wt (lenTop (S.levelLen hN lam M)) ≠ ⊤ := ne_top_of_lt hp
  obtain ⟨q, hq, hs, hs'⟩ := S.walk_project_supp hN lam M p hfin
  have key : ∀ (a b : Copy N.toRot.Vertex N.G.Dart) (q : FaceDisjoint.Walk S.Arc a b),
      a = S.vcopy u → b = S.vcopy v → S.awt lam M q < M →
      (∀ c ∈ q.support, ∃ y ∈ p.support, S.copyAt hN y = c) →
      (∀ y ∈ p.support, S.copyAt hN y ∈ q.support) →
      ∃ ps : List (N.G.Dart × Bool),
        S.dualSplit.IsWalk (S.vertexEquiv (S.pieceOf ⟨S.vcopy u, hu⟩)) ps
          (S.vertexEquiv (S.pieceOf ⟨S.vcopy v, hv⟩)) ∧
        (ps.map fun z => (c z.1 : ℝ)).sum = S.awt lam M q ∧
        ∀ w, (w = S.vertexEquiv (S.pieceOf ⟨S.vcopy u, hu⟩) ∨ ∃ y ∈ ps, S.dualSplit.head y = w) ↔
          ∃ y ∈ p.support, ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
            S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = w := by
    intro a b q ha hb hlt hs hs'
    subst ha hb
    have hreal : q.wt (S.w (fun x => (lam x : ℝ)) M) < M := by
      rw [← S.awt_eq_wt]
      exact_mod_cast hlt
    obtain ⟨P, hP, hF, hB⟩ := S.project_supp (lam := fun x => (lam x : ℝ)) (M := (M : ℝ))
      (fun _ => Nat.cast_nonneg _) (Nat.cast_nonneg _) q hreal hu hv rfl rfl
    obtain ⟨ps, hps, hw, hvis⟩ := S.split_walk_visits (fun d => (c d : ℝ))
      (fun d => congrArg (Nat.cast : ℕ → ℝ) (hcr d)) P
    refine ⟨ps, hps, ?_, fun w => ?_⟩
    · rw [hw, S.awt_eq_wt, ← hP]
      congr 1
      funext f g x
      simp [dw, hlam]
    · rw [hvis w]
      constructor
      · rintro ⟨f', hf', hw'⟩
        obtain ⟨c', hc', hcc, rfl⟩ := hF f' hf'
        obtain ⟨y, hy, rfl⟩ := hs c' hc'
        exact ⟨y, hy, hcc, hw'⟩
      · rintro ⟨y, hy, hcy, hw'⟩
        obtain ⟨hc', hm⟩ := hB _ (hs' y hy)
        exact ⟨_, hm, hw'⟩
  have e1 : S.copyAt hN ((S.levelPad hN).ι (.inl u)) = S.vcopy u := S.copyAt_ι hN _
  have e2 : S.copyAt hN ((S.levelPad hN).ι (.inl v)) = S.vcopy v := S.copyAt_ι hN _
  have hlt : S.awt lam M q < M := by
    have : ((S.awt lam M q : ℕ) : ℝ≥0∞) < M := hq ▸ hp
    exact_mod_cast this
  obtain ⟨ps, hps, hw, hvis⟩ := key _ _ q e1 e2 hlt hs hs'
  rw [hpu, hpv] at hps
  rw [hpu, S.vertexEquiv_pieceAt] at hvis
  have hgc' : ∀ d, g d = ENNReal.ofReal (c d : ℝ) := fun d => by rw [hgc, ENNReal.ofReal_natCast]
  have hk' : ENNReal.ofReal (ps.map fun z => (c z.1 : ℝ)).sum = p.wt (lenTop (S.levelLen hN lam M)) := by
    rw [hw, ENNReal.ofReal_natCast, hq]
  have hsub : C.Γ ⊆ S.Γ := L.sub.trans hS
  refine ⟨ps, S.shortest_live (fun d => (c d : ℝ)) (fun _ => Nat.cast_nonneg _) hgc' L hS hz h1 h2 h3 h4
    ps hps (hk' ▸ hle), ?_, fun r => ?_⟩
  · rw [← hk', RData.ofReal_sum_map _ (fun _ => Nat.cast_nonneg _)]
    congr 1
    exact List.map_congr_left fun z _ => hgc' z.1
  · show (r ≤ C.m ∧ ∃ σ, _) ↔ _
    refine and_congr_right fun _ => exists_congr fun σ => ?_
    constructor
    · rintro (h | ⟨y', hy', h⟩)
      · obtain ⟨y, hy, hcy, hw'⟩ := (hvis _).1 (.inl rfl)
        exact ⟨y, hy, hcy, L.κ0 t, hw'.symm, h.symm⟩
      · obtain ⟨y, hy, hcy, hw'⟩ := (hvis _).1 (.inr ⟨y', hy', rfl⟩)
        exact ⟨y, hy, hcy, N.toRot.dual.double.rev y', hw'.symm, h⟩
    · rintro ⟨y, hy, hcy, z, hz1, hz2⟩
      rcases (hvis _).2 ⟨y, hy, hcy, hz1.symm⟩ with h | ⟨y', hy', h⟩
      · exact .inl (hz2.symm.trans (S.cut_tail_of_split hsub h))
      · exact .inr ⟨y', hy', (S.cut_tail_of_split hsub h).trans hz2⟩

end RData

end RotSystem

end SsspFlow
