import SsspFlow.GHatLevelAdvance

/-!
# All levels of the recursion as one algorithm

The algorithm of one level, repeated, takes the stored state of level `0` to the stored state of
every level `ℓ`.

* `RData.LvInv`: the stored state of the nodes is that of level `ℓ`.
* `RData.levelIter_local`: the repetition of the algorithm of one level, with the state of level `ℓ`
  after `ℓ` repetitions.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ) (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k)

/-- The stored state `X` of the nodes is that of level `ℓ`: the input of the level with both sources
at the star centre of `w₀`, the number `m`, the base values, the states and codes of the corners of
the level, and the indices of the top annulus at the corners. -/
def LvInv (w₀ : Fin n) (ℓ : ℕ) (X : Fin n → LvX n) : Prop :=
  (∀ w, (X w).1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).starV hN w₀) w) ∧
  (∀ w, (X w).2.1 = Cp.m) ∧
  (∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((X d.fst).2.2.1 k).1 d.snd b = gsBase Cp k (d, b) ∧
    ((X d.snd).2.2.1 k).2 d.fst b = gsBase Cp k (d, b)) ∧
  (∀ (d : N.G.Dart) b, (X d.fst).2.2.2.2.1 d.snd b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b)) ∧
    (X d.snd).2.2.2.2.2 d.fst b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b))) ∧
  (∀ (d : N.G.Dart) b t, ((((X d.snd).2.2.2.1 d.fst b).1 t = true ↔ (d, b) = L₀.κ0 t) ∧
    (((X d.snd).2.2.2.1 d.fst b).2 t = true ↔ (d, b) = L₀.κ1 t)))

end RData

namespace RData

open Cslib.Congest.Algorithm

/-- **All levels as one algorithm.** The algorithm of one level, repeated with period `T`, takes a
stored state of level `0` to the stored state of level `ℓ` after `ℓ T` rounds, for every `ℓ`. -/
theorem levelIter_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (xI : Fin n → σ → LvX n),
    T ≤ 32 + 19 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (X₀ : Fin n → LvX n) (w₀ : Fin n),
      N.toRot.Planar → N.toRot.Connected → (∀ ℓ, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).NoConflict) → (∀ ℓ, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cut.card ≤ 3) →
      N.DiamLE D → (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) → (Cp.m + 2) ^ 8 ≤ M →
      LvInv hN modeL hostT hhost hE K D M r₀ w₀ 0 X₀ →
      ∀ ℓ, LvInv hN modeL hostT hhost hE K D M r₀ w₀ ℓ (fun w => xI w (A.run N.G X₀ (ℓ * T) w)) := by
  obtain ⟨C, c, hAd⟩ := levelAdvance_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, T, xN, hT0, hT, hA⟩ := hAd n D
  refine ⟨_, A.iter T (fun _ x => x) (fun v _ s => xN v s), T, fun _ s => s.1, hT, ?_⟩
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ X₀ w₀ hP hc hS hcut hD hc1 hcr hcb hM hMl hM8 h0 ℓ
  have hI : ∀ ℓ, LvInv hN modeL hostT hhost hE K D M r₀ w₀ ℓ
      (iterData A T (fun _ x => x) (fun v _ s => xN v s) N.G X₀ ℓ) := by
    intro ℓ
    induction ℓ with
    | zero => exact h0
    | succ ℓ ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      have hpick := lvPick hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hP hc (hS ℓ) (hcut ℓ) hD hc1 hcr hcb hM hMl
      have hQM : ∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq =>
        hMl _ ((((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ_range ℓ q hq).2.2.2.1).trans q.1.2.xb_le)
      have hstep := hA N hN modeL hostT hhost M r₀ ℓ _ w₀ hpick hP hc (hS ℓ) (hcut ℓ) hD hc1 hcr hcb hM hQM hM8
        h1 h2 h3 h4 h5
      dsimp only at hstep
      obtain ⟨e1, e2, e3, e4, e5⟩ := hstep
      refine ⟨e1, fun w => (e2 w).trans (h2 w), fun k hk d b => ?_, e5, fun d b t => ?_⟩
      · have h := h3 k hk d b
        rw [← e3 d.fst, ← e3 d.snd] at h
        exact h
      · have h := h5 d b t
        rw [← e4 d.snd] at h
        exact h
  have hrun : (A.iter T (fun _ x => x) (fun v _ s => xN v s)).run N.G X₀ (ℓ * T) = fun v =>
      (iterData A T (fun _ x => x) (fun v _ s => xN v s) N.G X₀ ℓ v, 0,
        A.run N.G (fun v => iterData A T (fun _ x => x) (fun v _ s => xN v s) N.G X₀ ℓ v) 0 v) := by
    have e := run_iter A (fun _ x => x) (fun v _ s => xN v s) N.G X₀ hT0 ℓ 0 hT0
    exact e
  have e : (fun w => ((A.iter T (fun _ x => x) (fun v _ s => xN v s)).run N.G X₀ (ℓ * T) w).1) =
      iterData A T (fun _ x => x) (fun v _ s => xN v s) N.G X₀ ℓ := funext fun w => by rw [hrun]
  show LvInv hN modeL hostT hhost hE K D M r₀ w₀ ℓ
    (fun w => ((A.iter T (fun _ x => x) (fun v _ s => xN v s)).run N.G X₀ (ℓ * T) w).1)
  exact (congrArg (LvInv hN modeL hostT hhost hE K D M r₀ w₀ ℓ) e).mpr (hI ℓ)

end RData

end RotSystem

end SsspFlow
