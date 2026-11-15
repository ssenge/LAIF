import SsspFlow.GHatStepSet

/-!
# The darts of the steps at the two ends of each dart

A node tests the copies it hosts: a copy with the four local parts of the step bit whose arc to its
parent carries a token gives, by `stepCornerL`, the corner of a dart of a step. The host of such a copy
is an end of the dart. So a dart is a dart of a step of the level exactly when the test holds at one of
its two ends, and one exchange of bits over every edge tells both ends.

* `bit2`, `dbit`: numbers from bits and the bits of a number.
* `stepLoc`: the test of a node for a corner given as tail, head and bit.
* `RData.lvStepDart_loc`: a dart is a dart of a step of the level exactly when the test holds at its
  tail or at its head.
-/

set_option autoImplicit false

namespace SsspFlow

/-- A bit followed by a number. -/
def bit2 (b : Bool) (x : ℕ) : ℕ := b.toNat + 2 * x

/-- The bit `i` of a number. -/
def dbit : ℕ → ℕ → Bool
  | x, 0 => decide (x % 2 = 1)
  | x, i + 1 => dbit (x / 2) i

@[simp] theorem dbit_bit2_zero (b : Bool) (x : ℕ) : dbit (bit2 b x) 0 = b := by
  cases b <;> simp [dbit, bit2]

@[simp] theorem dbit_bit2_succ (b : Bool) (x i : ℕ) : dbit (bit2 b x) (i + 1) = dbit x i := by
  have : (bit2 b x) / 2 = x := by cases b <;> simp [bit2]; omega
  simp [dbit, this]

theorem bit2_lt {b : Bool} {x k : ℕ} (h : x < 2 ^ k) : bit2 b x < 2 ^ (k + 1) := by
  have : b.toNat ≤ 1 := by cases b <;> simp
  rw [pow_succ]
  unfold bit2
  omega

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical in
/-- The test of the node `w` with level input `lin` for the corner `p`, as tail, head and bit: a copy
hosted at `w` with the four local parts of the step bit whose arc to its parent gives the corner `p`. -/
noncomputable def stepLoc {n : ℕ} (lin : LevelIn n) (w : Fin n)
    (R r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool) (p : Fin n × Fin n × Bool) : Bool :=
  decide (∃ y, hostOf y = w ∧ (R y).2 ≠ none ∧ (r₂ y).1 = 0 ∧ (fl y).2.1 = false ∧ (r₃ y).1 = 0 ∧
    stepCornerL lin.rot lin.own y (Net.parOf R y) = some p)

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

/-- **The darts of the steps at their ends.** With the outputs `r₂`, `r₃` of the two runs along the
chains, a dart is a dart of the step of an annulus of the level exactly when the test of its tail or of
its head holds for its corner. -/
theorem lvStepDart_loc {len : Fin (n * (n * 21)) → Fin (n * (n * 21)) → ℕ∞} {φ : Fin (n * (n * 21)) → ℕ∞}
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
    (lam : (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).Tok → ℕ) (M' : ℕ)
    (u₀ : (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).hRot.Vertex)
    (z : N.G.Dart × Bool) :
    lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ↔
      ∃ w, (w = z.1.fst ∨ w = z.1.snd) ∧
        stepLoc ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN lam M' u₀ w) w
          (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) r₂ r₃
          (lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) (z.1.fst, z.1.snd, z.2) = true := by
  classical
  set S := lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ
  set R := lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ
  rw [lvStepDart_local hN modeL hostT hhost hE K D M r₀ ℓ hpick hr r₂ r₃ h₂ h₃ z]
  unfold stepLoc
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨h1, h2, h3, h4, -⟩, hc⟩
    refine ⟨hostOf y, stepCornerL_host _ _ _ _ hc, y, rfl, h1, h2, h3, h4, hc⟩
  · rintro ⟨w, -, y, rfl, h1, h2, h3, h4, hc⟩
    refine ⟨y, ⟨h1, h2, h3, h4, ?_⟩, hc⟩
    have e := S.stepCornerL_eq hN y (Net.parOf R y)
    change stepCornerL (N.rotList (hostOf y)) (S.dinfoAt (hostOf y)) y (Net.parOf R y) = _ at hc
    rw [e] at hc
    intro hn
    rw [hn] at hc
    simp at hc

end RData

end RotSystem

end SsspFlow
