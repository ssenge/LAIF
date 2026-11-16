import SsspFlow.RunLoc
import SsspFlow.GHatValLevel
import SsspFlow.GHatOvVal

/-!
# The computed indices are covered by the levels

In the runs of the levels for the rule of a level, every computed index of a subrun at depth `ℓ` of a
later run is the middle index, `i1` or `i2` of an annulus of the list of level `ℓ`, read by one of the
three rules from the values of the annulus, or an index that passes the test of a side with these
values. All of these indices lie in `[0, m]`.

* `RData.LvPay`: the values of the annuli of a level hold their ranges, indices and bits.
* `RData.lv_cover`: the computed indices are covered.
* `RData.lv_rng_le`: the ranges read from the values lie in `[0, m]`.
* `RData.lv_sel_le`, `RData.lv_ov_le`: the covered indices are at most `m`.
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
  (hE : ExactSsspBound) (K D M : ℕ)

/-- The values of the annuli of the list of level `ℓ` hold the range, the least and greatest index of
the walk of the chain of the target and its bits, below `M`. -/
def LvPay (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
    (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ) : Prop :=
  ∀ s ∈ r.subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M r ℓ s kk i1 i2 →
      decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
      decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) = lvBits hN modeL hostT hhost hE K D M r ℓ s kk ∧
      payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

/-- **The computed indices are covered.** Every computed index of a subrun at depth `ℓ` of the run of a
later level is read by one of the three rules from the values of an annulus of the list of level `ℓ`,
or passes the test of a side with the values of such an annulus. -/
theorem lv_cover {Nn : ℕ} (hℓ : ℓ < Nn)
    (payT₁ payS₁ payT₂ payS₂ : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (hp₁ : LvPay hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ payT₁ payS₁)
    (hp₂ : LvPay hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ payT₂ payS₂)
    {s : CutPath.Sub Cp hR hC hgc} (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ Nn).subs ℓ)
    {t : ℕ} (ht : t ∈ s.2.2.loc) :
    (∃ i : Fin 3, ∃ q ∈ selQ (pk i) payT₁ payS₁ ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ), q.2 = t) ∨
      (∃ σ : Fin 2, ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ,
        ovIn σ (decT (payT₂ q)) (decS (payS₂ q)) t) := by
  obtain ⟨s', hs', -, e2, d, hd, hdis⟩ := CutPath.Run.seq_loc hR hC hgc
    (fun ℓ r => lvPof hN modeL hostT hhost hE K D M ℓ r) r₀ hℓ hpick hs ht
  obtain ⟨l1, l2⟩ := s.2.2.loc_lt t ht
  rw [← e2] at l1 l2
  have hjk := d.hjk
  obtain ⟨kk, hq, hps, hnone, -⟩ := hd
  have hw : lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s' kk = d.q :=
    hq.symm
  have hdat : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s' kk d.i1 d.i2 :=
    ⟨hps, hnone, by rw [hw]; exact d.hI1, by rw [hw]; exact d.hI2⟩
  have hmem : (s'.1, (s'.2.1.1 + s'.2.1.2) / 2) ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ :=
    ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_levelQ ℓ).2 ⟨s', hs', hjk, rfl⟩
  obtain ⟨a1, a2, -, -⟩ := hp₁ s' hs' hjk kk d.i1 d.i2 hdat
  obtain ⟨b1, b2, -, -⟩ := hp₂ s' hs' hjk kk d.i1 d.i2 hdat
  have hsel : ∀ i : Fin 3, pk i (s'.2.1.1, s'.2.1.2, d.i1, d.i2)
      (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s' kk) = some t →
      ∃ i : Fin 3, ∃ q ∈ selQ (pk i) payT₁ payS₁ ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ), q.2 = t :=
    fun i hi => ⟨i, (s'.1, t), (mem_selQ _ _ _ _ _).2 ⟨_, hmem, by rw [a1, a2]; exact hi,
      by rw [a1]; exact l1, by rw [a1]; exact l2, rfl⟩, rfl⟩
  rcases hdis with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨hA, -, h2⟩ | ⟨hB, h1, -⟩
  · exact .inl (hsel 0 (by rw [h]; rfl))
  · exact .inl (hsel 1 (by rw [h]; rfl))
  · exact .inl (hsel 2 (by rw [h]; rfl))
  · refine .inr ⟨0, _, hmem, ?_⟩
    rw [b1, b2]
    simp only [ovIn]
    refine ⟨?_, l1, h2⟩
    unfold lvBits
    rw [hw]
    simp only [decide_eq_true_eq]
    exact hA
  · refine .inr ⟨1, _, hmem, ?_⟩
    rw [b1, b2]
    simp only [ovIn]
    refine ⟨?_, h1, l2⟩
    unfold lvBits
    rw [hw]
    simp only [decide_eq_true_eq]
    exact hB

/-- The ranges of the annuli of the list of a level end at most at `m`, read from the values. -/
theorem lv_rng_le (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (hp : LvPay hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ payT payS)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ}
    (hq : q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ) :
    (decT (payT q)).1 + 2 ≤ (decT (payT q)).2.1 ∧ (decT (payT q)).2.1 ≤ Cp.m := by
  have hle := (rngA_le (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hq).2
  obtain ⟨s, hs, hjk, rfl⟩ := ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_levelQ ℓ).1 hq
  obtain ⟨kk, i1, i2, hd, -⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
  rw [(hp s hs hjk kk i1 i2 hd).1]
  rw [rngA_sub _ ℓ hs] at hle
  exact ⟨hjk, hle⟩

/-- **The indices read by the rules are at most `m`.** -/
theorem lv_sel_le (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (hp : LvPay hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ payT payS)
    (i : Fin 3) {q : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ}
    (hq : q ∈ selQ (pk i) payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ)) :
    q.2 ≤ Cp.m := by
  obtain ⟨q₀, hq₀, -, -, h2, -⟩ := (mem_selQ _ _ _ _ _).1 hq
  have := (lv_rng_le hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS hp hq₀).2
  omega

/-- **The indices that pass the test of a side are at most `m`.** -/
theorem lv_ov_le (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (hp : LvPay hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ payT payS)
    (σ : Fin 2) {q : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ}
    (hq : q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ) {μ : ℕ}
    (h : ovIn σ (decT (payT q)) (decS (payS q)) μ) : μ ≤ Cp.m := by
  obtain ⟨h1, h2⟩ := lv_rng_le hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS hp hq
  match σ, h with
  | 0, h => obtain ⟨-, -, h⟩ := h; omega
  | 1, h => obtain ⟨-, -, h⟩ := h; omega

end RData

end RotSystem

end SsspFlow
