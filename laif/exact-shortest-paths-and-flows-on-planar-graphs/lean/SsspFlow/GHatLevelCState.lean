import SsspFlow.GHatLevelState
import SsspFlow.GHatLevelRegion

/-!
# The state of the corners of a level

Every corner of the doubled dual carries the state of a level: whether it is a corner of the level,
whether it is a corner of a side of the side of `κ0(x_a)` or of `κ0(x_b)` of an annulus of the list of
the level, whether it is the source corner `κ0(t)` or the target corner `κ1(t)` of the top annulus at
the middle `t` of an annulus of the list, and at a target corner the range of that annulus. The state
of the next level at a corner is a function of its state, of the two values that the broadcast runs of
the level give its copy, of the bits of the new corners of the steps at it, and of whether it is a
digon corner of a dart of a step.

* `RData.qEnd_eq`: the sources and targets of the list of a level are the corners `κ0(t)`, `κ1(t)` of
  the top annulus at their middles.
* `RData.CSt`, `RData.lvCSt`: the state of a corner at a level.
* `RData.lvCSt_succ`: the state of the next level from the state, the values and the bits at the
  corner.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section QEnd

variable {n : ℕ} {N : Net (Fin n)} {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}

/-- **The sources and targets of a level are corners of the top annulus.** -/
theorem qEnd_eq (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) (τ : Fin 2) :
    qEnd τ q = if τ = 0 then L₀.κ0 q.2 else L₀.κ1 q.2 := by
  obtain ⟨s, hs, hjk, rfl⟩ := (r.mem_levelQ ℓ).1 hq
  obtain ⟨e0, e1⟩ := r.mid_corners ℓ hs hjk
  unfold qEnd
  split_ifs
  · exact e0
  · exact e1

end QEnd

/-- The state of a corner at a level. -/
structure CSt where
  /-- It is a corner of the level. -/
  inΓ : Bool
  /-- It is a corner of the side of `κ0(x_a)` of an annulus of the list. -/
  cA : Bool
  /-- It is a corner of the side of `κ0(x_b)` of an annulus of the list. -/
  cB : Bool
  /-- It is the source corner of an annulus of the list. -/
  src : Bool
  /-- It is the target corner of an annulus of the list. -/
  tgt : Bool
  /-- The range of that annulus, at a target corner. -/
  rng : ℕ × ℕ

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}

open Classical in
/-- **The state of a corner at level `ℓ`** of a run. -/
noncomputable def lvCSt (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (z : N.G.Dart × Bool) : CSt where
  inΓ := decide (z ∈ Γ₀ ∪ r.steps ℓ)
  cA := decide (∃ q ∈ r.levelQ ℓ, q.1.2.CornerA z)
  cB := decide (∃ q ∈ r.levelQ ℓ, q.1.2.CornerB z)
  src := decide (∃ t ∈ (r.levelQ ℓ).map Prod.snd, z = L₀.κ0 t)
  tgt := decide (∃ t ∈ (r.levelQ ℓ).map Prod.snd, z = L₀.κ1 t)
  rng := if h : ∃ s ∈ r.subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧ z = L₀.κ1 ((s.2.1.1 + s.2.1.2) / 2)
    then h.choose.2.1 else (0, 0)

/-- The test of an index at a corner from its two values. -/
def midTest (M' : ℕ) (vT vS : ℕ∞) (t : ℕ) : Bool :=
  decide (vT < M') && decide (vS < M') &&
    kidMid (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1 (decT vT.toNat).2.2.2
      (decS vS.toNat).1 (decS vS.toNat).2 t

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

/-- The middles of the next level from the values at the corners `κ0(t)` (`τ = 0`) or `κ1(t)`
(`τ = 1`) of the top annulus. -/
theorem lv_mid_succ (τ : Fin 2) (t : ℕ) :
    t ∈ ((lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1)).map Prod.snd ↔
      midTest M' (outT (if τ = 0 then L₀.κ0 t else L₀.κ1 t))
        (outS (if τ = 0 then L₀.κ0 t else L₀.κ1 t)) t = true := by
  have key := next_mid_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS
    (fun t => outT (if τ = 0 then L₀.κ0 t else L₀.κ1 t)) (fun t => outS (if τ = 0 then L₀.κ0 t else L₀.κ1 t))
    M' decT decS (fun s hs hjk t x1 x2 x3 x4 => h_in s hs hjk _ (by
      have hA : s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := by
        rw [CutPath.Run.nodes_eq_subs]
        exact List.mem_map_of_mem hs
      obtain ⟨-, -, -, -, e0, e1⟩ := (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).below_nodes ℓ s.1 hA
      split_ifs
      · rw [← e0 t x1 x2]
        exact s.1.2.gcomp_κ0 x1.le x2.le
      · rw [← e1 t x3 x4]
        exact s.1.2.gcomp_κ1 x3.le x4.le))
    (fun t h1 h2 => by
      obtain ⟨s, hs, hjk, -, e1, e2⟩ := h_guard _ h1 h2
      exact ⟨s, hs, hjk, e1, e2⟩)
    h_pay t
  rw [key]
  simp only [midTest, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

variable
  (gateA gateB : N.G.Dart × Bool → Bool)
  (h_gateA : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
    ∀ z, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) z →
      (gateA z = true ↔
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2 = false ∧
          i2 + 2 ≤ s.2.1.2))
  (h_gateB : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
    ∀ z, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) z →
      (gateB z = true ↔
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1 = false ∧
          s.2.1.1 + 2 ≤ i1))
include h_gateA h_gateB

open Classical in
/-- **The state of the next level at a corner.** Let `outT`, `outS` be the values of the broadcast
runs at the corners, `gateA`, `gateB` the bits at the darts of the steps, `newA' = lvNewA`,
`newB' = lvNewB` and `newΓ` whether the corner is a digon corner of a dart of a step. Then the state of
level `ℓ + 1` at a corner `z` is computed from its state of level `ℓ`, the two values and three bits at
`z`. -/
theorem lvCSt_succ (z : N.G.Dart × Bool) :
    (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) z).inΓ =
        ((lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z).inΓ ||
          decide (∃ z', lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z' ∧
            (z = (z'.1, false) ∨ z = (N.toRot.dual.rev z'.1, false)))) ∧
      (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) z).cA =
        (decide (outT z < M') && decide (outS z < M') &&
          kidA (decT (outT z).toNat).1 (decT (outT z).toNat).2.1 (decT (outT z).toNat).2.2.1
            (decT (outT z).toNat).2.2.2 (decS (outS z).toNat).1 (decS (outS z).toNat).2
            (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z).cA
            (decide (lvNewA hN modeL hostT hhost hE K D M r₀ ℓ gateA z))) ∧
      (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) z).cB =
        (decide (outT z < M') && decide (outS z < M') &&
          kidB (decT (outT z).toNat).1 (decT (outT z).toNat).2.1 (decT (outT z).toNat).2.2.1
            (decT (outT z).toNat).2.2.2 (decS (outS z).toNat).1 (decS (outS z).toNat).2
            (decide (lvNewB hN modeL hostT hhost hE K D M r₀ ℓ gateB z))
            (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z).cB) ∧
      ((lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) z).src = true ↔
        ∃ t, z = L₀.κ0 t ∧ midTest M' (outT z) (outS z) t = true) ∧
      ((lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) z).tgt = true ↔
        ∃ t, z = L₀.κ1 t ∧ midTest M' (outT z) (outS z) t = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [lvCSt]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
    rw [lv_steps_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick z]
    exact or_assoc.symm
  · rw [Bool.eq_iff_iff]
    simp only [lvCSt, decide_eq_true_eq, Bool.and_eq_true]
    rw [next_cornerA_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS M' decT decS
      h_in h_guard h_pay (fun c => decide (∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ,
        q.1.2.CornerA c)) (fun c => decide (lvNewA hN modeL hostT hhost hE K D M r₀ ℓ gateA c))
      (fun c => decide_eq_true_iff)
      (fun s hs hjk kk i1 i2 S hd ht hb hi c hreg => by
        rw [decide_eq_true_iff]
        exact lvNewA_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick gateA h_gateA hs hjk hd ht hb hi hreg) z]
    simp only [and_assoc]
  · rw [Bool.eq_iff_iff]
    simp only [lvCSt, decide_eq_true_eq, Bool.and_eq_true]
    rw [next_cornerB_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS M' decT decS
      h_in h_guard h_pay (fun c => decide (∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ,
        q.1.2.CornerB c)) (fun c => decide (lvNewB hN modeL hostT hhost hE K D M r₀ ℓ gateB c))
      (fun c => decide_eq_true_iff)
      (fun s hs hjk kk i1 i2 S hd ht hb hi c hreg => by
        rw [decide_eq_true_iff]
        exact lvNewB_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick gateB h_gateB hs hjk hd ht hb hi hreg) z]
    simp only [and_assoc]
  · simp only [lvCSt, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, rfl, by simpa using (lv_mid_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS
        M' h_in h_guard h_pay 0 t).1 ht⟩
    · rintro ⟨t, rfl, ht⟩
      exact ⟨t, (lv_mid_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS
        M' h_in h_guard h_pay 0 t).2 (by simpa using ht), rfl⟩
  · simp only [lvCSt, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, rfl, by simpa using (lv_mid_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS
        M' h_in h_guard h_pay 1 t).1 ht⟩
    · rintro ⟨t, rfl, ht⟩
      exact ⟨t, (lv_mid_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS
        M' h_in h_guard h_pay 1 t).2 (by simpa using ht), rfl⟩

end RData

end RotSystem

end SsspFlow
