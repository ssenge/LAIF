import SsspFlow.OracleWalk
import SsspFlow.GHatLevelIdx

/-!
# The parent chain of a target as a shortest walk of the annulus

Let an output of the oracle on the network of a level meet its specification, for offsets `0` at
some copies on E_R edges and `⊤` elsewhere. If every source with an offset lies at the piece at
`κ0(t)` or at distance at least `M` from a target copy at the piece at `κ1(t)`, and the distance of
the target is below `M` and at most `λ_t`, then the parent chain of the target is a walk that gives a
shortest walk of the annulus of that length. Its indices on the cut path are the indices at the
pieces of the copies of the nodes of the chain, the nodes that the marking run from the target
reaches.

* `RData.level_chain_idx`: the parent chain of a target gives a shortest walk of the annulus whose
  indices on the cut path are read at the copies of the nodes of the chain.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {Γ : Finset (N.G.Dart × Bool)}

/-- **The chain of a target is a shortest walk of the annulus.** Under the conditions of
`RData.level_shortest`, for an output `r` of the oracle on the network of a level whose sources lie
at the piece at `κ0(t)` or at distance at least `M` from the target copy at `v`, with distance of the
target below `M` and at most `λ_t`: there is a shortest walk of the annulus of that length whose
indices `r' ≤ m` on the cut path are exactly the indices of the corners `p_{r'}^σ` that lie, in the
cut, at the vertex of the piece of the copy of a node of the parent chain of the target. -/
theorem level_chain_idx (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r) {v : S.hRot.Vertex}
    (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)) (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hroot : ∀ z, ψ z ≠ ⊤ → ψ z = 0 ∧ ∃ u, z = (S.levelPad hN).ι (.inl u) ∧
      ∃ hu : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) ∨
          (M : ℝ≥0∞) ≤ S.arcDist lam M (S.vcopy u) (S.vcopy v))
    (hlt : ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) < M)
    (hle : ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ≤ C.lamD g t) :
    ∃ ps : List (N.G.Dart × Bool), L.Shortest t ps ∧
      (ps.map (g ∘ Prod.fst)).sum = ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
      ∀ r', r' ∈ C.idx (L.κ0 t) ps ↔ r' ≤ C.m ∧ ∃ σ, ∃ y,
        (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
          S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
          C.cut.tail z = C.cut.tail (C.k σ r') := by
  have hfin : (r ((S.levelPad hN).ι (.inl v))).1 ≠ ⊤ := fun e => by simp [e] at hlt
  obtain ⟨k, p, -, -, hwt, hsupp⟩ := hr.chain_walk _ hfin
  generalize (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = ρ at p hwt
  have hρ : ψ ρ ≠ ⊤ := fun e => by
    rw [offTop, e] at hwt
    simp only [ENat.toENNReal_top, top_add] at hwt
    exact hfin (by exact_mod_cast hwt.symm)
  obtain ⟨h0, u, rfl, hu, hcase⟩ := hroot ρ hρ
  rw [offTop, h0, ENat.toENNReal_zero, zero_add] at hwt
  have hp : p.wt (lenTop (S.levelLen hN lam M)) < M := hwt ▸ hlt
  have hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) := by
    refine hcase.resolve_right fun harc => ?_
    obtain ⟨q, hq, -⟩ := S.walk_project hN lam M p (ne_top_of_lt hp)
    have harc' : (M : ℝ≥0∞) ≤ S.arcDist lam M (S.copyAt hN ((S.levelPad hN).ι (.inl u)))
        (S.copyAt hN ((S.levelPad hN).ι (.inl v))) := by
      rw [S.copyAt_ι, S.copyAt_ι]
      exact harc
    have : S.arcDist lam M (S.copyAt hN ((S.levelPad hN).ι (.inl u)))
        (S.copyAt hN ((S.levelPad hN).ι (.inl v))) ≤ p.wt (lenTop (S.levelLen hN lam M)) := by
      rw [← hq]
      exact iInf_le _ q
    exact absurd (harc'.trans this) (not_le.2 hp)
  obtain ⟨ps, hps, hsum, hidx⟩ := S.level_shortest_idx hN lam M c hcr hlam hgc L hS hz h1 h2 h3 h4 p
    hp hu hv hpu hpv (hwt ▸ hle)
  refine ⟨ps, hps, hsum.trans hwt, fun r' => (hidx r').trans ?_⟩
  refine and_congr_right fun _ => exists_congr fun σ => ?_
  constructor
  · rintro ⟨y, hy, rest⟩
    exact ⟨y, (hsupp y).1 hy, rest⟩
  · rintro ⟨y, hy, rest⟩
    exact ⟨y, (hsupp y).2 hy, rest⟩

end RData

end RotSystem

end SsspFlow
