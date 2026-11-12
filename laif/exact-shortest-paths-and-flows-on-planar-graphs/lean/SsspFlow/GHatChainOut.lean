import SsspFlow.GHatChainSelf

/-!
# The ends of the step read from the outputs of the runs

The nodes run the oracle on the network of a level, then the counting run up the parent chains and
the run down them, with the flags of `RData.nodeFlag` as their input bits. A node reads from its own
outputs whether it is one of the two nodes that bound the step on the chain of a target: the first
node flagged for `0` sees its flag `0` and count `0`, and the last node below it flagged for `1` sees
its flag `1` and distance `0` in the run down the chains.

* `RData.chain_step_out`: the step of `RData.chain_step_flags`, with its two bounding nodes read from
  the outputs of the three runs.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

open Classical in
/-- **The ends of the step from the outputs.** Under the conditions of `RData.chain_step_self`, let
the input bits of each node be its target flag and its flags of `RData.nodeFlag`, and let `r`, `r₂`
and `r₃` meet the specifications of the oracle, the counting run up the chains and the run down
them. A node of the chain of `v` has flag `0` and count `0` exactly when it is the first node `ia`
flagged for `0`; a node up to `ia` has flag `1` and distance `0` in the run down the chains exactly
when it is the last node `iy` up to `ia` flagged for `1`. The darts of the tokens of the chain edges
between them are exactly the darts of a step. -/
theorem chain_step_out {C : N.toRot.dual.CutPath} {Γ : Finset (N.G.Dart × Bool)}
    (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    (L : C.Live (Nat.cast ∘ c) Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (isT : Fin (n * (n * 21)) → Bool) (ψ : Fin (n * (n * 21)) → ℕ∞)
    (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool)
    (hfl : ∀ a, fl a = (isT a, decide (S.nodeFlag hN C 0 a), decide (S.nodeFlag hN C 1 a)))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    (hr₂ : (S.levelNet hN).ExactSpec (Net.markLenW r fun a => ((fl a).2.1.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) r₂)
    (hr₃ : (S.levelNet hN).ExactSpec (Net.downLenW r fun a => ((fl a).2.2.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) r₃)
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
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    (hvT : isT ((S.levelPad hN).ι (.inl v)) = true) :
    ∃ ia iy : ℕ, iy ≤ ia ∧ ia ≤ k ∧
      (∀ m, Net.ParSteps r ((S.levelPad hN).ι (.inl v)) m →
        (((fl ((Net.parOf r)^[m] ((S.levelPad hN).ι (.inl v)))).2.1 &&
          decide ((r₂ ((Net.parOf r)^[m] ((S.levelPad hN).ι (.inl v)))).1 = 0)) = true ↔ m = ia)) ∧
      (∀ i ≤ ia, ((fl ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)))).2.2 = true ∧
        (r₃ ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)))).1 = 0) ↔ i = iy) ∧
      ∃ St : L.Step, ∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l, iy ≤ l ∧ l < ia ∧ ∃ x,
        S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
          ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x ∧ z = N.toRot.tokDart x.1 := by
  have e₂ : (Net.markLenW r fun a => ((fl a).2.1.toNat : ℕ∞)) =
      Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0 := by
    congr 1
    funext a
    by_cases h : S.nodeFlag hN C 0 a <;> simp [hfl, h]
  have o₂ : (Net.markOffB fun a => (fl a).1) = Net.markOffB isT := by
    congr 1
    funext a
    simp [hfl]
  rw [e₂, o₂] at hr₂
  have eX : (fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) = fun a => decide (S.nodeFlag hN C 0 a ∧
      (S.levelNet hN).dsrcTop (Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0)
        (Net.markOffB isT) a = 0) := by
    funext a
    rw [hfl]
    show (decide (S.nodeFlag hN C 0 a) && decide ((r₂ a).1 = 0)) = _
    rw [← Bool.decide_and]
    exact decide_eq_decide.2 (and_congr_right fun _ => by rw [← hr₂.dist_eq a, ENat.toENNReal_eq_zero])
  have e₃ : (Net.downLenW r fun a => ((fl a).2.2.toNat : ℕ∞)) =
      Net.downLenW r fun a => if S.nodeFlag hN C 1 a then 1 else 0 := by
    congr 1
    funext a
    by_cases h : S.nodeFlag hN C 1 a <;> simp [hfl, h]
  rw [e₃, eX] at hr₃
  obtain ⟨ia, iy, hya, hak, hX, hY, St, hSt⟩ := S.chain_step_self hN lam M hR hC c hc1 hcr hlam L hS hz
    h1 h2 h3 h4 ψ r hr hs hroot hu hv hpu hpv hlt hle isT hT hvT
  refine ⟨ia, iy, hya, hak, fun m hm => ?_, fun i hi => ?_, St, hSt⟩
  · rw [congrFun eX]
    exact hX m hm
  · rw [← hY i hi, ← hr₃.dist_eq, ENat.toENNReal_eq_zero, hfl]
    simp

end RData

end RotSystem

end SsspFlow
