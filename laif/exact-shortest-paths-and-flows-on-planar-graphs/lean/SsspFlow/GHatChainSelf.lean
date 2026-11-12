import SsspFlow.GHatChainFlags
import SsspFlow.OracleChainDown

/-!
# The ends of the step on a parent chain know themselves

Flag a node of the network of a level for `σ` when its copy holds a token whose piece lies at a copy
`p_t^σ` of the cut path. Each node knows its own flags. On the chain of a target, two more runs of the
oracle let the two nodes that bound the step of `RData.chain_step_flags` know that they are these
nodes: a counting run up the chains for the flag `0` marks the first node flagged for `0`, and a run
down from the marked nodes, counting the nodes flagged for `1`, marks the last node below it flagged
for `1`.

* `RData.nodeFlag`: the flag of a node for `σ`.
* `RData.chain_step_self`: the step of `RData.chain_step_flags`, with the two bounding nodes marked by
  the two runs.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- A node of the network of a level is flagged for `σ` when its copy holds a token whose piece lies
at a copy `p_t^σ`. -/
def nodeFlag (C : N.toRot.dual.CutPath) (σ : Fin 2) (a : Fin (n * (n * 21))) : Prop :=
  ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a)), S.CopyPiece C σ (S.pieceOf ⟨_, hy⟩)

open Classical in
/-- **The ends of the step know themselves.** Under the conditions of `RData.chain_step_flags`, let
the targets `isT` include the copy node of `v`, and let the valid chains of distinct targets not meet.
After a counting run up the chains for the flag `0`, a node of the chain of `v` is flagged for `0`
with distance `0` exactly when it is the first node `ia` flagged for `0`. After a run down from these
nodes, with the indicator of the flag `1` as lengths, a node of the chain up to `ia` is flagged for `1`
with distance `0` exactly when it is the last node `iy` up to `ia` flagged for `1`. The darts of the
tokens of the chain edges between `iy` and `ia` are exactly the darts of a step. -/
theorem chain_step_self {C : N.toRot.dual.CutPath} {Γ : Finset (N.G.Dart × Bool)}
    (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    (L : C.Live (Nat.cast ∘ c) Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    {u v : S.hRot.Vertex} {k : ℕ}
    (hs : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k)
    (hroot : (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u))
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hlt : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) < M)
    (hle : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) ≤ C.lamD (Nat.cast ∘ c) t)
    (isT : Fin (n * (n * 21)) → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    (hvT : isT ((S.levelPad hN).ι (.inl v)) = true) :
    ∃ ia iy : ℕ, iy ≤ ia ∧ ia ≤ k ∧
      (∀ m, Net.ParSteps r ((S.levelPad hN).ι (.inl v)) m →
        (decide (S.nodeFlag hN C 0 ((Net.parOf r)^[m] ((S.levelPad hN).ι (.inl v))) ∧
          (S.levelNet hN).dsrcTop (Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0)
            (Net.markOffB isT) ((Net.parOf r)^[m] ((S.levelPad hN).ι (.inl v))) = 0) = true ↔ m = ia)) ∧
      (∀ i ≤ ia, (S.nodeFlag hN C 1 ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v))) ∧
        (S.levelNet hN).dsrcTop (Net.downLenW r fun a => if S.nodeFlag hN C 1 a then 1 else 0)
          (Net.markOffB fun a => decide (S.nodeFlag hN C 0 a ∧ (S.levelNet hN).dsrcTop
            (Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0) (Net.markOffB isT) a = 0))
          ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v))) = 0) ↔ i = iy) ∧
      ∃ St : L.Step, (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l, iy ≤ l ∧ l < ia ∧ ∃ x,
        S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
          ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x ∧ z = N.toRot.tokDart x.1) ∧
        (List.range St.n).map St.q = S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) iy (ia - iy) := by
  obtain ⟨ia, iy, hya, hak, hA0, hmin, hA1, hmax, St, hSt⟩ := S.chain_step_flags hN lam M hR hC c hc1
    hcr hlam L hS hz h1 h2 h3 h4 ψ r hr hs hroot hu hv hpu hpv hlt hle
  have hia : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) ia := fun l hl => hs l (by omega)
  exact ⟨ia, iy, hya, hak,
    fun m hm => hr.first_iff (S.nodeFlag hN C 0) isT hT hvT hA0 hmin hm,
    fun i hi => hr.last_iff (S.nodeFlag hN C 0) (S.nodeFlag hN C 1) isT hT hvT hia hA0 hmin hya hA1 hmax hi,
    St, hSt⟩

end RData

end RotSystem

end SsspFlow
