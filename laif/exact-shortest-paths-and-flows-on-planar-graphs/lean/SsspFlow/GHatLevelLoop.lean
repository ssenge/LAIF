import SsspFlow.GHatLevelValOv
import SsspFlow.GHatLevelIter

/-!
# All levels with their values, as one algorithm

Every node starts with its stored state of level `0` and the value `⊤`. One repetition runs the
algorithm of the values of the level (`levelValOv_local`) and keeps the least value, then the algorithm
of one level (`levelAdvance_local`). After `ℓ` repetitions every node holds its stored state of level
`ℓ` and a value that is at least the least `λ_t` over `t ≤ m`, and for every index computed by a
subrun at depth `ℓ' < ℓ` of the run of a later level some node holds a value at most `λ_t`.

* `RData.levelLoop_local`: the algorithm and its invariant.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **All levels with their values, as one algorithm.** -/
theorem levelLoop_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (xI : Fin n → σ → LvX n) (ac : Fin n → σ → ℕ∞),
    0 < T ∧ T ≤ 110 + 68 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
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
      ∀ ℓ, LvInv hN modeL hostT hhost hE K D M r₀ w₀ ℓ (fun w => xI w (A.run N.G X₀ (ℓ * T) w)) ∧
        (∀ w, (⨅ t, ⨅ (_ : t ≤ Cp.m), Cp.lamD (Nat.cast ∘ cc) t) ≤ (ac w (A.run N.G X₀ (ℓ * T) w) : ℝ≥0∞)) ∧
        ∀ ℓ' < ℓ, ∀ Nn, ℓ' < Nn → ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ Nn).subs ℓ', ∀ t ∈ s.2.2.loc,
          ∃ w, (ac w (A.run N.G X₀ (ℓ * T) w) : ℝ≥0∞) ≤ Cp.lamD (Nat.cast ∘ cc) t := by
  obtain ⟨C₁, c₁, hVO⟩ := levelValOv_local hE K
  obtain ⟨C₂, c₂, hAd⟩ := levelAdvance_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, vo, hT₁, hA₁⟩ := hVO n D
  obtain ⟨σ₂, A₂, T₂, xN, hT0, hT₂, hA₂⟩ := hAd n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have w₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  let B₁ := (A₁.widen w₁).keep (fun _ (x : LvX n × ℕ∞) => x.1)
  let B₂ := (A₂.widen w₂).keep (fun _ (y : LvX n × ℕ∞) => y.1)
  let Bs := B₁.seq T₁ (fun w s => (s.1.1, min s.1.2 (vo w s.2))) B₂
  let uI : Fin n → LvX n × ℕ∞ → ((ℕ × ((LvX n × ℕ∞) × σ₁)) ⊕ ((LvX n × ℕ∞) × σ₂)) → LvX n × ℕ∞ :=
    fun v x s => match s with
      | .inr p => (xN v p.2, p.1.2)
      | .inl _ => x
  let Ai := Bs.iter (T₁ + T₂) (fun _ x => x) uI
  refine ⟨_, Ai.keep (fun _ x => (x, (⊤ : ℕ∞))), T₁ + T₂, fun _ s => s.2.1.1, fun _ s => s.2.1.2, by omega, ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ X₀ w₀ hP hc hS hcut hD hc1 hcr hcb hM hMl hM8 h0
  have hstep : ∀ (x : Fin n → LvX n × ℕ∞) v, Bs.run N.G x (T₁ + T₂) v =
      .inr (((x v).1, min (x v).2 (vo v (A₁.run N.G (fun w => (x w).1) T₁ v))),
        A₂.run N.G (fun w => (x w).1) T₂ v) := by
    intro x v
    rw [run_seq]
    simp only [B₁, B₂, run_keep, run_widen]
  let Dt := iterData Bs (T₁ + T₂) (fun _ x => x) uI N.G (fun w => (X₀ w, (⊤ : ℕ∞)))
  have hDs : ∀ ℓ, Dt (ℓ + 1) = fun v => (xN v (A₂.run N.G (fun w => (Dt ℓ w).1) T₂ v),
      min (Dt ℓ v).2 (vo v (A₁.run N.G (fun w => (Dt ℓ w).1) T₁ v))) := by
    intro ℓ
    funext v
    show uI v (Dt ℓ v) (Bs.run N.G (fun v => Dt ℓ v) (T₁ + T₂) v) = _
    rw [hstep]
  have hI : ∀ ℓ, LvInv hN modeL hostT hhost hE K D M r₀ w₀ ℓ (fun w => (Dt ℓ w).1) ∧
      (∀ w, (⨅ t, ⨅ (_ : t ≤ Cp.m), Cp.lamD (Nat.cast ∘ cc) t) ≤ ((Dt ℓ w).2 : ℝ≥0∞)) ∧
      ∀ ℓ' < ℓ, ∀ Nn, ℓ' < Nn → ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ Nn).subs ℓ', ∀ t ∈ s.2.2.loc,
        ∃ w, ((Dt ℓ w).2 : ℝ≥0∞) ≤ Cp.lamD (Nat.cast ∘ cc) t := by
    intro ℓ
    induction ℓ with
    | zero =>
      refine ⟨h0, fun w => ?_, fun ℓ' h => absurd h (Nat.not_lt_zero _)⟩
      show _ ≤ ((⊤ : ℕ∞) : ℝ≥0∞)
      simp
    | succ ℓ ih =>
      obtain ⟨⟨h1, h2, h3, h4, h5⟩, hlo, hup⟩ := ih
      have hpick := lvPick hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hP hc (hS ℓ) (hcut ℓ) hD hc1 hcr hcb hM hMl
      have hQM : ∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq =>
        hMl _ ((((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ_range ℓ q hq).2.2.2.1).trans q.1.2.xb_le)
      have hst := hA₂ N hN modeL hostT hhost M r₀ ℓ _ w₀ hpick hP hc (hS ℓ) (hcut ℓ) hD hc1 hcr hcb hM hQM hM8
        h1 h2 h3 h4 h5
      dsimp only at hst
      obtain ⟨e1, e2, e3, e4, e5⟩ := hst
      obtain ⟨vlo, vup⟩ := hA₁ N hN modeL hostT hhost M r₀ ℓ _ ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).starV hN w₀) hpick hP hc (hS ℓ) (hcut ℓ) hD
        hc1 hcr hcb hM hMl hM8 h1 h2 h3 h4 h5
      rw [hDs ℓ]
      refine ⟨⟨e1, fun w => (e2 w).trans (h2 w), fun k hk d b => ?_, e5, fun d b t => ?_⟩, fun w => ?_,
        fun ℓ' hℓ' Nn hN' s hs t ht => ?_⟩
      · have h := h3 k hk d b
        rw [← e3 d.fst, ← e3 d.snd] at h
        exact h
      · have h := h5 d b t
        rw [← e4 d.snd] at h
        exact h
      · dsimp only
        rw [ENat.toENNReal_min]
        exact le_min (hlo w) (vlo w)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ' with h | rfl
        · obtain ⟨w, hw⟩ := hup ℓ' h Nn hN' s hs t ht
          refine ⟨w, ?_⟩
          dsimp only
          rw [ENat.toENNReal_min]
          exact (min_le_left _ _).trans hw
        · obtain ⟨w, hw⟩ := vup Nn hN' s hs t ht
          refine ⟨w, ?_⟩
          dsimp only
          rw [ENat.toENNReal_min]
          exact (min_le_right _ _).trans hw
  intro ℓ
  have hrun : (Ai.keep (fun _ x => (x, (⊤ : ℕ∞)))).run N.G X₀ (ℓ * (T₁ + T₂)) =
      fun w => (X₀ w, Dt ℓ w, 0, Bs.run N.G (fun v => Dt ℓ v) 0 w) := by
    rw [run_keep]
    funext w
    have e := run_iter (T := T₁ + T₂) Bs (fun _ x => x) uI N.G (fun w => (X₀ w, (⊤ : ℕ∞))) (by omega) ℓ 0 (by omega)
    exact congrArg (fun y => (X₀ w, y)) (congrFun e w)
  rw [hrun]
  exact hI ℓ

end RData

end RotSystem

end SsspFlow
