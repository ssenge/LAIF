import SsspFlow.GHatLevelWalk
import SsspFlow.GHatSplit

/-!
# Walks of a level as walks of the split dual

Let the token lengths be the costs of the darts of the tokens, the same on both darts of an edge. A
walk of the network of a level between two copies on E_R edges, shorter than `M`, gives a walk of the
same length between their pieces in the split of the doubled dual (`RData.dualSplit`).

* `RData.awt_eq_wt`: the natural length of a walk of `Ĝ_ℓ` is its real weight.
* `RData.level_split_walk`: a walk of the network of a level between copies on E_R edges, shorter
  than `M`, gives a walk of the split between their pieces, whose sum of costs is its length.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Cast

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData) (lam : S.Tok → ℕ) (M : ℕ)

/-- The natural length of a walk of `Ĝ_ℓ` is its real weight. -/
theorem awt_eq_wt : ∀ {a b : Copy G.Vertex E} (q : FaceDisjoint.Walk S.Arc a b),
    ((S.awt lam M q : ℕ) : ℝ) = q.wt (S.w (fun x => (lam x : ℝ)) M)
  | _, _, .nil _ => by simp [awt]
  | _, _, .cons e q => by
    rw [FaceDisjoint.Walk.wt_cons, ← awt_eq_wt q]
    cases e <;> simp [awt, arcW, w]

end Cast

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- **A walk of a level is a walk of the split.** For token lengths that are the costs `c` of their
darts, with `c` equal on the two darts of an edge, a walk of the network of a level between copies on
E_R edges, shorter than `M`, gives a walk of the split between their pieces whose sum of costs is its
length. -/
theorem level_split_walk (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    {u v : S.hRot.Vertex} (p : SsspFlow.Walk (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inl u))
      ((S.levelPad hN).ι (.inl v)))
    (hp : p.wt (lenTop (S.levelLen hN lam M)) < M)
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)) :
    ∃ (ps : List (N.G.Dart × Bool)) (k : ℕ),
      S.dualSplit.IsWalk (S.vertexEquiv (S.pieceOf ⟨S.vcopy u, hu⟩)) ps
        (S.vertexEquiv (S.pieceOf ⟨S.vcopy v, hv⟩)) ∧
      (ps.map fun z => (c z.1 : ℝ)).sum = k ∧ (k : ℝ≥0∞) = p.wt (lenTop (S.levelLen hN lam M)) := by
  have hfin : p.wt (lenTop (S.levelLen hN lam M)) ≠ ⊤ := ne_top_of_lt hp
  obtain ⟨q, hq, -⟩ := S.walk_project hN lam M p hfin
  have key : ∀ (a b : Copy N.toRot.Vertex N.G.Dart) (q : FaceDisjoint.Walk S.Arc a b),
      a = S.vcopy u → b = S.vcopy v → S.awt lam M q < M →
      ∃ ps : List (N.G.Dart × Bool),
        S.dualSplit.IsWalk (S.vertexEquiv (S.pieceOf ⟨S.vcopy u, hu⟩)) ps
          (S.vertexEquiv (S.pieceOf ⟨S.vcopy v, hv⟩)) ∧
        (ps.map fun z => (c z.1 : ℝ)).sum = S.awt lam M q := by
    intro a b q ha hb hlt
    subst ha hb
    have hreal : q.wt (S.w (fun x => (lam x : ℝ)) M) < M := by
      rw [← S.awt_eq_wt]
      exact_mod_cast hlt
    obtain ⟨P, hP⟩ := S.project (lam := fun x => (lam x : ℝ)) (M := (M : ℝ)) (fun x => Nat.cast_nonneg _) (Nat.cast_nonneg _) q
      hreal hu hv rfl rfl
    obtain ⟨ps, hps, hw⟩ := S.split_walk (fun d => (c d : ℝ)) (fun d => congrArg (Nat.cast : ℕ → ℝ) (hcr d)) P
    refine ⟨ps, hps, ?_⟩
    rw [hw, S.awt_eq_wt]
    rw [← hP]
    congr 1
    funext f g x
    simp [dw, hlam]
  have h1 : S.copyAt hN ((S.levelPad hN).ι (.inl u)) = S.vcopy u := S.copyAt_ι hN _
  have h2 : S.copyAt hN ((S.levelPad hN).ι (.inl v)) = S.vcopy v := S.copyAt_ι hN _
  have hlt : S.awt lam M q < M := by
    have : ((S.awt lam M q : ℕ) : ℝ≥0∞) < M := hq ▸ hp
    exact_mod_cast this
  obtain ⟨ps, hps, hw⟩ := key _ _ q h1 h2 hlt
  exact ⟨ps, S.awt lam M q, hps, hw, hq⟩

end RData

end RotSystem

end SsspFlow
