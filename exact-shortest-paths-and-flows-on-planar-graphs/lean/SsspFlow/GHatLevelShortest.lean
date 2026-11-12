import SsspFlow.GHatLevelSplit
import SsspFlow.Annuli

/-!
# Short walks of a level are shortest walks of the annulus

Let the corners of the data `S` hold those of a live annulus, the others out of its reach. A walk of
the split of `S` between the pieces at `κ0(t)` and `κ1(t)` whose sum of costs is at most `λ_t` is a
shortest walk of the annulus. With `RData.level_split_walk` this holds for a walk of the network of
a level between copies on E_R edges of these pieces, of length below `M` and at most `λ_t`.

* `RData.shortest_live`: a walk of the split between the pieces at `κ0(t)` and `κ1(t)` of cost at
  most `λ_t` is a shortest walk of the annulus from `κ0(t)` to `κ1(t)`.
* `RData.level_shortest`: a walk of the network of a level between copies on E_R edges of the
  pieces at `κ0(t)` and `κ1(t)`, of length below `M` and at most `λ_t`, gives a shortest walk of the
  annulus of the same length.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Live

variable {E : Type} [Fintype E] [DecidableEq E] (c : E → ℝ)

omit [Fintype E] [DecidableEq E] in
theorem ofReal_sum_map (hc0 : ∀ d, 0 ≤ c d) : ∀ ps : List (E × Bool),
    ENNReal.ofReal (ps.map fun z => c z.1).sum = (ps.map fun z => ENNReal.ofReal (c z.1)).sum
  | [] => by simp
  | z :: ps => by
    rw [List.map_cons, List.sum_cons, ENNReal.ofReal_add (hc0 _) (List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact hc0 _), ofReal_sum_map hc0 ps]
    simp

variable {G : RotSystem E} (S : G.RData) {C : G.dual.CutPath} {g : E → ℝ≥0∞} {Γ : Finset (E × Bool)}

/-- **Shortest walks from the split.** Let the weights `c ≥ 0` give `g`, and let the corners of `S`
hold those of a live annulus, the others out of its reach. A walk of the split between the pieces at
`κ0(t)` and `κ1(t)` of cost at most `λ_t` is a shortest walk of the annulus. -/
theorem shortest_live (hc0 : ∀ d, 0 ≤ c d) (hgc : ∀ d, g d = ENNReal.ofReal (c d)) (L : C.Live g Γ)
    (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (G.dual.double.split Γ).IsWalk
      ((G.dual.double.split Γ).tail (L.κ0 t)) p ((G.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb) (ps : List (E × Bool))
    (hps : S.dualSplit.IsWalk (S.vertexEquiv (S.pieceAt (L.κ0 t))) ps
      (S.vertexEquiv (S.pieceAt (L.κ1 t))))
    (hle : ENNReal.ofReal (ps.map fun z => c z.1).sum ≤ C.lamD g t) :
    L.Shortest t ps := by
  rw [S.vertexEquiv_pieceAt, S.vertexEquiv_pieceAt] at hps
  have hw := (G.dual.double.isWalk_split_split_iff hS hz ps ⟨[], rfl⟩ _).1 hps
  have hsum : (ps.map (g ∘ Prod.fst)).sum = ENNReal.ofReal (ps.map fun z => c z.1).sum := by
    rw [ofReal_sum_map c hc0]
    congr 1
    exact List.map_congr_left fun z _ => hgc z.1
  refine ⟨hw, fun p' hp' => ?_, by rw [hsum]; exact ENNReal.ofReal_ne_top⟩
  rw [hsum]
  refine hle.trans ?_
  rw [← L.dist t h1 h2 h3 h4]
  exact walkDist_le _ hp'

end Live

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {Γ : Finset (N.G.Dart × Bool)}

/-- **Short walks of a level are shortest.** For token lengths that are the costs `c` of their darts,
with `c` equal on the two darts of an edge and giving `g`, and corners of `S` that hold those of a
live annulus, the others out of its reach: a walk of the network of a level between copies on E_R
edges of the pieces at `κ0(t)` and `κ1(t)`, of length below `M` and at most `λ_t`, gives a shortest
walk of the annulus of the same length. -/
theorem level_shortest (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
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
      (ps.map (g ∘ Prod.fst)).sum = p.wt (lenTop (S.levelLen hN lam M)) := by
  obtain ⟨ps, k, hps, hsum, hk⟩ := S.level_split_walk hN lam M c hcr hlam p hp hu hv
  rw [hpu, hpv] at hps
  have hgc' : ∀ d, g d = ENNReal.ofReal (c d : ℝ) := fun d => by rw [hgc, ENNReal.ofReal_natCast]
  have hk' : ENNReal.ofReal (ps.map fun z => (c z.1 : ℝ)).sum = p.wt (lenTop (S.levelLen hN lam M)) := by
    rw [hsum, ENNReal.ofReal_natCast, hk]
  refine ⟨ps, S.shortest_live (fun d => (c d : ℝ)) (fun _ => Nat.cast_nonneg _) hgc' L hS hz h1 h2 h3 h4
    ps hps (hk' ▸ hle), ?_⟩
  rw [← hk', ofReal_sum_map _ (fun _ => Nat.cast_nonneg _)]
  congr 1
  exact List.map_congr_left fun z _ => hgc' z.1

end RData

end RotSystem

end SsspFlow
