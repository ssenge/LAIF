import SsspFlow.GHatStepCorners
import SsspFlow.GHatStepDart

/-!
# The darts of the steps of a level from the step bits

The darts of the steps of all annuli of a level are the darts of the tokens on the arcs from the
copies with the step bit, read from distances, to their parents. So a node decides from its own copies
and their parents which darts of the steps of the level it holds.

* `RData.lvStepDart_iff`: the darts of the steps of a level are the darts of the tokens on the arcs
  from the copies with the step bit to their parents.
* `RData.stepCornerL_host`: the host of the head of an arc with a token is an end of its dart.
* `RData.lvStepDart_local`: the darts of the steps of a level from the step bits and `stepCornerL` at
  the hosts of the copies.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- **The host of the head of an arc with a token is an end of its dart.** -/
theorem stepCornerL_host {n : ℕ} (R : List (Fin n)) (f : Fin n → DInfo) (y par : Fin (n * (n * 21)))
    {a b : Fin n} {β : Bool} (h : stepCornerL R f y par = some (a, b, β)) : hostOf y = a ∨ hostOf y = b := by
  unfold stepCornerL at h
  split_ifs at h <;> cases h <;> first | exact .inl rfl | exact .inr rfl

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ)

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

/-- **The darts of the steps of a level from the step bits.** For any lengths and offsets for which the
chosen output of the oracle of the level is exact, a dart is a dart of the step of an annulus of the
level exactly when it is the dart of the token on the arc from a copy with the step bit to its
parent. -/
theorem lvStepDart_iff {len : Fin (n * (n * 21)) → Fin (n * (n * 21)) → ℕ∞} {φ : Fin (n * (n * 21)) → ℕ∞}
    (hr : ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelNet hN).ExactSpec
      len φ (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ))
    (z : N.G.Dart × Bool) :
    lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ↔
      ∃ y, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).stepBitD hN
          (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)
          (lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) y ∧
        ∃ x, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).edgeTok hN
            (Net.parOf (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) y) y =
              some x ∧ z = N.toRot.tokDart x.1 := by
  classical
  set rs := lvSeq hN modeL hostT hhost hE K D M r₀
  set S := lvS modeL hostT hhost (rs ℓ) ℓ
  set R := lvR hN modeL hostT hhost hE K D M (rs ℓ) ℓ
  set fl := lvFl hN modeL hostT hhost (rs ℓ) ℓ
  constructor
  · rintro ⟨s, hs, hjk, kk, i1, i2, St, -, htop, hz⟩
    obtain ⟨q, S', -, -, htop', ⟨kk', rfl, -, -, hiff⟩, -⟩ :=
      CutPath.pickF_corners hR hC hgc _ s.2.2 (hpick s hs hjk)
    rw [htop] at htop'
    have e := (Prod.mk.inj (Option.some_injective _ htop')).2
    rw [e] at hz
    obtain ⟨l, -, hb, x, hx, rfl⟩ := (hiff z).1 hz
    exact ⟨_, hb, x, hx, rfl⟩
  · rintro ⟨y, hb, x, hx, rfl⟩
    have hb' := hb
    obtain ⟨-, h0, -⟩ := hb'
    have hex : ∃ t i, (fl t).1 = true ∧ Net.ParSteps R t i ∧ (Net.parOf R)^[i] t = y := by
      by_contra hc
      rw [hr.dsrcTop_markW] at h0
      refine ENNReal.top_ne_zero (h0 ▸ ?_)
      symm
      simp only [iInf_eq_top]
      intro t ht i hi
      exact absurd ⟨t, i, ht, hi.1, hi.2⟩ hc
    obtain ⟨t, i, ht, hs, rfl⟩ := hex
    have ht' : S.tgtFlag hN ((rs ℓ).levelQ ℓ) t = true := ht
    rw [tgtFlag, decide_eq_true_iff] at ht'
    obtain ⟨q, hq, rfl⟩ := ht'
    obtain ⟨s, hs', hjk, rfl⟩ := ((rs ℓ).mem_levelQ ℓ).1 hq
    obtain ⟨_, St, i1, i2, htop, ⟨kk, rfl, hps, hnone, hiff⟩, h1, h2, -⟩ :=
      CutPath.pickF_corners hR hC hgc _ s.2.2 (hpick s hs' hjk)
    exact ⟨s, hs', hjk, kk, i1, i2, St, ⟨hps, hnone, h1, h2⟩, htop, (hiff _).2 ⟨i, hs, hb, x, hx, rfl⟩⟩

/-- **The darts of the steps of a level from local data.** With the outputs `r₂`, `r₃` of the two runs
along the chains, a dart is a dart of the step of an annulus of the level exactly when a copy `y` has
the step bit and `stepCornerL` at the host of `y` reads the corner of the dart from the arc to the
parent of `y`. -/
theorem lvStepDart_local {len : Fin (n * (n * 21)) → Fin (n * (n * 21)) → ℕ∞} {φ : Fin (n * (n * 21)) → ℕ∞}
    (hr : ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelNet hN).ExactSpec
      len φ (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ))
    (r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (h₂ : ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelNet hN).ExactSpec
      (Net.markLenW (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)
        fun a => (((lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ a).2.1).toNat : ℕ∞))
      (Net.markOffB fun a => (lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ a).1) r₂)
    (h₃ : ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelNet hN).ExactSpec
      (Net.downLenW (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)
        fun a => (((lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ a).2.2).toNat : ℕ∞))
      (Net.markOffB fun a => (lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ a).2.1 &&
        decide ((r₂ a).1 = 0)) r₃)
    (z : N.G.Dart × Bool) :
    lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ↔
      ∃ y, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).stepBit hN
          (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) r₂ r₃
          (lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) y ∧
        stepCornerL (N.rotList (hostOf y))
          ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).dinfoAt (hostOf y)) y
          (Net.parOf (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) y) =
            some (z.1.fst, z.1.snd, z.2) := by
  rw [lvStepDart_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick hr z]
  refine exists_congr fun y => ?_
  rw [(lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).stepBit_iff_D hN _ r₂ r₃ _ h₂ h₃ y,
    RData.stepCornerL_eq _ hN, Option.map_eq_some_iff]
  refine and_congr_right fun _ => exists_congr fun x => and_congr_right fun _ => ?_
  constructor
  · rintro rfl
    rfl
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact (Prod.ext (SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)) h3).symm

end RData

end RotSystem

end SsspFlow
