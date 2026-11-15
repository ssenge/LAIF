import SsspFlow.GHatLevelCState

/-!
# The ranges at the target corners of a level

The annulus of a subrun of a level determines the subrun, and so its range. At a corner the value
`lvV8` is the least code of the range of an annulus of the list of the level whose target corner it
is. These values, the bits of the corner states and the costs are the inputs of the run of a level,
and the values of the next level follow from the values of the broadcast runs at the corner and from
the indices `t` with `z = κ1(t)` in the top annulus.

* `RData.rngA`: the range of the subrun of a level with a given annulus.
* `RData.lvV8`: the least code of the range of an annulus of the list whose target corner is `z`.
* `RData.lvG4_eq` to `RData.lvG7_eq`: the inputs of the run of a level from the corner states.
* `RData.lvV8_succ`: the values of the next level from the values of the broadcast runs.
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


open Classical in
/-- The range of the subrun of level `ℓ` with annulus `A`. -/
noncomputable def rngA (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
    (A : Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') : ℕ × ℕ :=
  if h : ∃ s ∈ r.subs ℓ, s.1 = A then h.choose.2.1 else (0, 0)

/-- The least code of the range of an annulus of the list of level `ℓ` with target corner `z`. -/
noncomputable def lvV8 (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (z : N.G.Dart × Bool) : ℕ∞ :=
  ⨅ q ∈ r.levelQ ℓ, ⨅ (_ : z = qEnd 1 q), ((Nat.pair (rngA r ℓ q.1).1 (rngA r ℓ q.1).2 : ℕ) : ℕ∞)

theorem rngA_sub (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) {s : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ r.subs ℓ) : rngA r ℓ s.1 = s.2.1 := by
  have h : ∃ s' ∈ r.subs ℓ, s'.1 = s.1 := ⟨s, hs, rfl⟩
  unfold rngA
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨h1, h2⟩ := h.choose_spec
  rw [r.subs_eq_of_fst ℓ h1 hs h2]

/-- The ranges of the annuli of the list lie in the indices of the cut path. -/
theorem rngA_le (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) {q} (hq : q ∈ r.levelQ ℓ) :
    (rngA r ℓ q.1).1 ≤ Cp.m ∧ (rngA r ℓ q.1).2 ≤ Cp.m := by
  obtain ⟨s, hs, -, rfl⟩ := (r.mem_levelQ ℓ).1 hq
  rw [rngA_sub r ℓ hs]
  obtain ⟨h0, -, -, h3, -⟩ := s.2.2.bounds
  have := s.1.2.xb_le
  omega

open Classical in
theorem lvG4_eq (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) :
    (fun z => if (lvCSt r ℓ z).cA then (0 : ℕ∞) else ⊤) =
      fun z => if ∃ q ∈ r.levelQ ℓ, q.1.2.CornerA z then 0 else ⊤ := by
  funext z
  simp [lvCSt]

open Classical in
theorem lvG5_eq (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) :
    (fun z => if (lvCSt r ℓ z).cB then (0 : ℕ∞) else ⊤) =
      fun z => if ∃ q ∈ r.levelQ ℓ, q.1.2.CornerB z then 0 else ⊤ := by
  funext z
  simp [lvCSt]

open Classical in
theorem lvG6_eq (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) :
    (fun z => if (lvCSt r ℓ z).src then (0 : ℕ∞) else ⊤) =
      fun z => if ∃ q ∈ r.levelQ ℓ, z = qEnd 0 q then 0 else ⊤ := by
  funext z
  have e : (∃ t ∈ (r.levelQ ℓ).map Prod.snd, z = L₀.κ0 t) ↔ ∃ q ∈ r.levelQ ℓ, z = qEnd 0 q := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, by rw [qEnd_eq r ℓ hq]; rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, ⟨q, hq, rfl⟩, by rw [qEnd_eq r ℓ hq]; rfl⟩
  simp only [lvCSt, decide_eq_true_eq]
  exact if_congr e rfl rfl

open Classical in
theorem lvG7_eq (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) :
    (fun z => if (lvCSt r ℓ z).tgt then (0 : ℕ∞) else ⊤) =
      fun z => if ∃ q ∈ r.levelQ ℓ, z = qEnd 1 q then 0 else ⊤ := by
  funext z
  have e : (∃ t ∈ (r.levelQ ℓ).map Prod.snd, z = L₀.κ1 t) ↔ ∃ q ∈ r.levelQ ℓ, z = qEnd 1 q := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, by rw [qEnd_eq r ℓ hq]; rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, ⟨q, hq, rfl⟩, by rw [qEnd_eq r ℓ hq]; rfl⟩
  simp only [lvCSt, decide_eq_true_eq]
  exact if_congr e rfl rfl

variable (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ)

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
  (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
  (outT outS : N.G.Dart × Bool → ℕ∞) (M' : ℕ)
  (h_in : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → ∀ c,
    (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
      outT c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
  (h_guard : ∀ c, outT c < M' → outS c < M' →
    ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
      (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c ∧
      outT c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
  (h_pay : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
      decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
      decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) =
        lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk ∧
      payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M' ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M')
include hpick h_in h_guard h_pay

/-- **The ranges at the target corners of the next level.** At a corner `z`, the value of level
`ℓ + 1` is the least code of `kidRange` of the read data at `z` over the indices `t` with `z = κ1(t)`
in the top annulus that pass the test of the middles at `z`. -/
theorem lvV8_succ (z : N.G.Dart × Bool) :
    lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) z =
      ⨅ t, ⨅ (_ : z = L₀.κ1 t), ⨅ (_ : midTest M' (outT z) (outS z) t = true),
        ((Nat.pair (kidRange (decT (outT z).toNat).1 (decT (outT z).toNat).2.1 (decT (outT z).toNat).2.2.1
          (decT (outT z).toNat).2.2.2 (decS (outS z).toNat).1 t).1
          (kidRange (decT (outT z).toNat).1 (decT (outT z).toNat).2.1 (decT (outT z).toNat).2.2.1
          (decT (outT z).toNat).2.2.2 (decS (outS z).toNat).1 t).2 : ℕ) : ℕ∞) := by
  classical
  set rs := lvSeq hN modeL hostT hhost hE K D M r₀
  set F : ℕ∞ → ℕ∞ → ℕ → ℕ := fun vT vS t =>
    Nat.pair (kidRange (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1
      (decT vT.toNat).2.2.2 (decS vS.toNat).1 t).1
      (kidRange (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1
      (decT vT.toNat).2.2.2 (decS vS.toNat).1 t).2 with hF
  have hmid : ∀ t, t ∈ ((rs (ℓ + 1)).levelQ (ℓ + 1)).map Prod.snd ↔
      midTest M' (outT (L₀.κ1 t)) (outS (L₀.κ1 t)) t = true := fun t => by
    simpa using lv_mid_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS M' h_in h_guard
      h_pay 1 t
  have key : ∀ q ∈ (rs (ℓ + 1)).levelQ (ℓ + 1), qEnd 1 q = L₀.κ1 q.2 ∧
      Nat.pair (rngA (rs (ℓ + 1)) (ℓ + 1) q.1).1 (rngA (rs (ℓ + 1)) (ℓ + 1) q.1).2 =
        F (outT (L₀.κ1 q.2)) (outS (L₀.κ1 q.2)) q.2 := by
    intro q hq
    refine ⟨by rw [qEnd_eq _ _ hq]; rfl, ?_⟩
    obtain ⟨s', hs', hjk', rfl⟩ := ((rs (ℓ + 1)).mem_levelQ (ℓ + 1)).1 hq
    have e := next_range hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS (fun t => outT (L₀.κ1 t))
      (fun t => outS (L₀.κ1 t)) decT decS
      (fun s hs hjk t a b c d => by
        simpa using in_idx hN modeL hostT hhost hE K D M r₀ ℓ payT payS outT outS h_in 1 s hs hjk t a b c d)
      (fun s hs hjk kk i1 i2 hd => ⟨(h_pay s hs hjk kk i1 i2 hd).1, (h_pay s hs hjk kk i1 i2 hd).2.1⟩) hs' hjk'
    rw [rngA_sub _ _ hs', hF]
    dsimp only
    rw [e]
  unfold lvV8
  apply le_antisymm
  · refine le_iInf fun t => le_iInf fun hz => le_iInf fun hm => ?_
    subst hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ((hmid t).2 hm)
    obtain ⟨e1, e2⟩ := key q hq
    exact iInf₂_le_of_le q hq (iInf_le_of_le e1.symm (by rw [e2]))
  · refine le_iInf fun q => le_iInf fun hq => le_iInf fun hz => ?_
    obtain ⟨e1, e2⟩ := key q hq
    rw [e1] at hz
    subst hz
    have hm := (hmid q.2).1 (List.mem_map_of_mem hq)
    refine iInf_le_of_le q.2 (iInf_le_of_le rfl (iInf_le_of_le hm ?_))
    rw [e2]

end RData

end RotSystem

end SsspFlow
