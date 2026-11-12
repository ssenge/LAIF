import SsspFlow.GHatChainRun
import SsspFlow.GHatChainStepLocal
import SsspFlow.GHatChainTargets

/-!
# The data of a node of a run, at a level

For an annulus of a level of a run, the recursion needs a shortest walk `p` at its middle index, the
least and the greatest index `i1`, `i2` of the cut path on `p`, and a step whose darts form a segment
of `p`. All of them come from one output of the oracle on the network of the level and the two runs
along its chains: `p` is the list of the darts of the chain of the target, `i1` and `i2` are the
values at the marked copies, and the step is decided at the nodes of the chain.

* `RData.chainDarts_split`: the darts of a chain split at two of its nodes.
* `RData.level_node_data`: for every annulus of a level, the walk, the two indices and the step, with
  the step a segment of the walk.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- The darts of `k` parent steps split at the nodes `iy ≤ ia ≤ k` above `v`. -/
theorem chainDarts_split (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (v : Fin (n * (n * 21))) {k ia iy : ℕ} (hya : iy ≤ ia) (hak : ia ≤ k) :
    S.chainDarts hN r v 0 k =
      S.chainDarts hN r v ia (k - ia) ++ S.chainDarts hN r v iy (ia - iy) ++ S.chainDarts hN r v 0 iy := by
  have e1 := S.chainDarts_add hN r v 0 (k - iy) iy
  have e2 := S.chainDarts_add hN r v iy (k - ia) (ia - iy)
  rw [show iy + (k - iy) = k by omega, Nat.zero_add] at e1
  rw [show ia - iy + (k - ia) = k - iy by omega, show iy + (ia - iy) = ia by omega] at e2
  rw [e1, e2]

section Level

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

open Classical in
/-- **The data of a node of a run, at a level.** For positive costs `c` of the darts, equal on the two
darts of an edge, token lengths that are these costs and `g = c`, let `Q` list annuli of a level of a
run with one index `t` each in their ranges and `λ_t < M`. Let `R` be an output of the oracle on the
network of the level from the sources of `Q`, and `r₂`, `r₃` the outputs of the counting run up its
chains and of the run down them, for the targets of `Q` and the flags of the nodes for `0` and `1`.
For an annulus of `Q` and values `x1`, `x2` as in `RData.level_i12_roots`, the darts of the chain of
its target form a shortest walk `p` of the annulus, whose least and greatest index on the cut path
`i1` and `i2` agree, capped at `M`, with `x1` and `m - x2`; and there is a step whose darts are those
of the parent arcs of the nodes of the chain that meet the local test, and they form a segment of
`p`. -/
theorem level_node_data (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (R r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R)
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool)
    (hfl : ∀ a, fl a = (S.tgtFlag hN Q a, decide (S.nodeFlag hN C 0 a), decide (S.nodeFlag hN C 1 a)))
    (hr₂ : (S.levelNet hN).ExactSpec (Net.markLenW R fun a => ((fl a).2.1.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) r₂)
    (hr₃ : (S.levelNet hN).ExactSpec (Net.downLenW R fun a => ((fl a).2.2.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) r₃)
    (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
    (hix : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, (r' : ℕ∞))
    (hjx : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, ((C.m - r' : ℕ) : ℕ∞))
    {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'} {t : ℕ} (hAt : (A, t) ∈ Q) (x1 x2 : ℝ≥0∞)
    (hx1 : min x1 M = min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u)
        (S.vcopy (S.endV (A.2.κ1 t)))),
      ⨅ (_ : ∃ t' i, S.tgtFlag hN Q t' = true ∧ (Net.parOf R)^[i] t' = (S.levelPad hN).ι (.inl u)),
        (ixI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M)
    (hx2 : min x2 M = min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u)
        (S.vcopy (S.endV (A.2.κ1 t)))),
      ⨅ (_ : ∃ t' i, S.tgtFlag hN Q t' = true ∧ (Net.parOf R)^[i] t' = (S.levelPad hN).ι (.inl u)),
        (jxI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M) :
    ∃ (kk i1 i2 : ℕ) (St : A.2.Step),
      A.2.Shortest t (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) 0 kk) ∧
      IsLeast (C.idx (A.2.κ0 t) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) 0 kk)) i1 ∧
      IsGreatest (C.idx (A.2.κ0 t) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) 0 kk)) i2 ∧
      min x1 M = min (i1 : ℝ≥0∞) M ∧ min x2 M = min ((C.m - i2 : ℕ) : ℝ≥0∞) M ∧
      (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l,
        Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) (l + 1) ∧
        (r₂ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))))).1 = 0 ∧
        (fl ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))))).2.1 = false ∧
        (r₃ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))))).1 = 0 ∧ ∃ x,
          S.edgeTok hN ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))))
            ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t))))) = some x ∧
          z = N.toRot.tokDart x.1) ∧
      ∃ p₁ p₃, S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) 0 kk =
        p₁ ++ (List.range St.n).map St.q ++ p₃ := by
  obtain ⟨ps, i1, i2, -, -, hl, hg', e1, e2, hidx⟩ := S.level_i12_roots hN r ℓ lam M c hcr hlam hgc hΓ Q hQ
    hQu R hr ixI jxI hix hjx hAt x1 x2 hx1 hx2
  obtain ⟨hA, hun, h1, h2, h3, h4, hroot, hup, hT, hTv⟩ :=
    S.level_roots_cond hN r ℓ lam M c hcr hlam hgc hΓ Q hQ hQu R hr hAt
  have hTc := S.tgtFlag_chains hN r ℓ lam M c hcr hlam hgc hΓ Q hQ hQu R hr
  obtain ⟨kk, u, hu, hs, hρu, -, hpu, hsum, hsh, hidx'⟩ := S.chain_data hN lam M c hcr hlam hgc A.2 hA
    hun h1 h2 h3 h4 _ _ hr (S.endV_end _) (S.pieceOf_endV _) hroot (hT _ hTv).1 hup
  have hE : C.idx (A.2.κ0 t) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) 0 kk) =
      C.idx (A.2.κ0 t) ps := Set.ext fun r' => (hidx' r').trans (hidx r').symm
  have hlt' : ((∑ l ∈ Finset.range kk, S.levelLen hN lam M
      ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))))
      ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t))))) : ℕ∞) : ℝ≥0∞) < M := by
    rw [hsum]; exact (hT _ hTv).1
  have hle' : ((∑ l ∈ Finset.range kk, S.levelLen hN lam M
      ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))))
      ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t))))) : ℕ∞) : ℝ≥0∞) ≤ C.lamD g t := by
    rw [hsum]; exact hup
  obtain rfl : g = Nat.cast ∘ c := funext fun d => hgc d
  obtain ⟨ia, iy, hya, hak, St, hSt, hSd⟩ := S.chain_step_local hN lam M hR hC c hc1 hcr hlam A.2 hA hun
    h1 h2 h3 h4 (S.tgtFlag hN Q) (S.srcOff hN Q) R r₂ r₃ fl hfl hr hr₂ hr₃ hs hρu hu (S.endV_end _)
    hpu (S.pieceOf_endV _) hlt' hle' hTc hTv
  refine ⟨kk, i1, i2, St, hsh, hE ▸ hl, hE ▸ hg', e1, e2, hSt,
    S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) ia (kk - ia),
    S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) 0 iy, ?_⟩
  rw [hSd]
  exact S.chainDarts_split hN R _ hya hak

end Level

end RData

end RotSystem

end SsspFlow
