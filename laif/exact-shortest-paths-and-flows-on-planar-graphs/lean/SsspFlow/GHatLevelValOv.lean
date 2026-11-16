import SsspFlow.GHatOvLevel
import SsspFlow.GHatCover

/-!
# The values of one level, as one algorithm

Every node starts with its stored state of level `ℓ`. The algorithm of the three rules
(`levelVals_local`) and the algorithm of the two overlap sides (`levelOv_local`) run one after the
other on this state, and every node keeps the least value. Every value is at least the least `λ_t`
over `t ≤ m`, and for every index computed by a subrun at depth `ℓ` of the run of a later level some
node holds a value at most `λ_t`.

* `RData.levelValOv_local`: the algorithm and the two bounds.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **The values of one level, as one algorithm.** Every node starts with its stored state of level
`ℓ`. After `T` rounds every value is at least the least `λ_t` over `t ≤ m`, and for every index `t`
computed by a subrun at depth `ℓ` of the run of a later level some node holds a value at most
`λ_t`. -/
theorem levelValOv_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (vo : Fin n → σ → ℕ∞),
    T ≤ 78 + 49 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (X : Fin n → LvX n) (u₀ : (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).hRot.Vertex),
      (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
        Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
          lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts}) →
      N.toRot.Planar → N.toRot.Connected → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).NoConflict → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cut.card ≤ 3 → N.DiamLE D →
      (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) → (Cp.m + 2) ^ 8 ≤ M →
      (∀ w, (X w).1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w) → (∀ w, (X w).2.1 = Cp.m) →
      (∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((X d.fst).2.2.1 k).1 d.snd b = gsBase Cp k (d, b) ∧
        ((X d.snd).2.2.1 k).2 d.fst b = gsBase Cp k (d, b)) →
      (∀ (d : N.G.Dart) b, (X d.fst).2.2.2.2.1 d.snd b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b)) ∧
        (X d.snd).2.2.2.2.2 d.fst b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b))) →
      (∀ (d : N.G.Dart) b t, ((((X d.snd).2.2.2.1 d.fst b).1 t = true ↔ (d, b) = L₀.κ0 t) ∧
        (((X d.snd).2.2.2.1 d.fst b).2 t = true ↔ (d, b) = L₀.κ1 t))) →
      (∀ w, (⨅ t, ⨅ (_ : t ≤ Cp.m), Cp.lamD (Nat.cast ∘ cc) t) ≤ (vo w (A.run N.G X T w) : ℝ≥0∞)) ∧
      ∀ Nn, ℓ < Nn → ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ Nn).subs ℓ, ∀ t ∈ s.2.2.loc,
        ∃ w, (vo w (A.run N.G X T w) : ℝ≥0∞) ≤ Cp.lamD (Nat.cast ∘ cc) t := by
  obtain ⟨C₁, c₁, hV⟩ := levelVals_local hE K
  obtain ⟨C₂, c₂, hO⟩ := levelOv_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, v₁, hT₁, hA₁⟩ := hV n D
  obtain ⟨σ₂, A₂, T₂, v₂, hT₂, hA₂⟩ := hO n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have w₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  let B₁ := (A₁.widen w₁).keep (fun _ (x : LvX n) => x)
  let B₂ := (A₂.widen w₂).keep (fun _ (y : LvX n × ℕ∞) => y.1)
  refine ⟨_, B₁.seq T₁ (fun w s => (s.1, v₁ w s.2)) B₂, T₁ + T₂, fun w s => match s with
      | .inr p => min p.1.2 (v₂ w p.2)
      | .inl _ => ⊤, ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ ℓ X u₀ hpick hP hc hS hcut hD hc1 hcr hcb hM hMl hM8
    hX1 hX2 hXb hXc hXk
  obtain ⟨p₁T, p₁S, hp₁, hv⟩ := hA₁ N hN modeL hostT hhost M r₀ ℓ X u₀ hpick hP hc hS hcut hD hc1 hcr hcb hM hMl hM8
    hX1 hX2 hXb hXc hXk
  obtain ⟨p₂T, p₂S, hp₂, ho⟩ := hA₂ N hN modeL hostT hhost M r₀ ℓ X u₀ hP hc hS hcut hD hc1 hcr hcb hM hMl hM8
    hX1 hX2 hXb hXc hXk
  have hrun : ∀ w, (B₁.seq T₁ (fun w s => (s.1, v₁ w s.2)) B₂).run N.G X (T₁ + T₂) w =
      .inr ((X w, v₁ w (A₁.run N.G X T₁ w)), A₂.run N.G X T₂ w) := by
    intro w
    rw [run_seq]
    simp only [B₁, B₂, run_keep, run_widen]
  have hval : ∀ w, (((match (B₁.seq T₁ (fun w s => (s.1, v₁ w s.2)) B₂).run N.G X (T₁ + T₂) w with
      | .inr p => min p.1.2 (v₂ w p.2)
      | .inl _ => ⊤ : ℕ∞)) : ℝ≥0∞) =
      min ((v₁ w (A₁.run N.G X T₁ w) : ℕ∞) : ℝ≥0∞) ((v₂ w (A₂.run N.G X T₂ w) : ℕ∞) : ℝ≥0∞) := fun w => by
    rw [hrun w]
    exact ENat.toENNReal_min _ _
  refine ⟨fun w => ?_, fun Nn hℓ s hs t ht => ?_⟩
  · rw [hval w, hv w, ho w]
    refine le_min (le_iInf fun i => le_iInf₂ fun q hq => le_iInf fun _ => ?_)
      (le_iInf fun σ => le_iInf₂ fun q hq => le_iInf fun μ => le_iInf fun hμ => le_iInf fun _ => ?_)
    · exact iInf₂_le q.2 (lv_sel_le hN modeL hostT hhost hE K D M r₀ ℓ hpick p₁T p₁S hp₁ i hq)
    · exact iInf₂_le μ (lv_ov_le hN modeL hostT hhost hE K D M r₀ ℓ hpick p₂T p₂S hp₂ σ hq hμ)
  · rcases lv_cover hN modeL hostT hhost hE K D M r₀ ℓ hpick hℓ p₁T p₁S p₂T p₂S hp₁ hp₂ hs ht with
      ⟨i, q, hq, rfl⟩ | ⟨σ, q, hq, hov⟩
    · refine ⟨hostOf (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))), ?_⟩
      rw [hval, hv]
      exact (min_le_left _ _).trans (iInf_le_of_le i (iInf₂_le_of_le q hq (iInf_le _ rfl)))
    · refine ⟨(q.1.2.κ1 t).1.snd, ?_⟩
      rw [hval, ho]
      exact (min_le_right _ _).trans (iInf_le_of_le σ (iInf₂_le_of_le q hq
        (iInf_le_of_le t (iInf_le_of_le hov (iInf_le _ rfl)))))

end RData

end RotSystem

end SsspFlow
