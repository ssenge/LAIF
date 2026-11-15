import SsspFlow.GHatLevelTgt

/-!
# The state of a corner at the next level from local bits

The state of a corner at level `ℓ + 1` and its code of a range follow from its state at level `ℓ`, the
two values of the broadcast runs at it, five bits that the tests of the level give it, and the indices
`t` of the top annulus with `z = κ0(t)` or `z = κ1(t)`.

* `cstNext`: the update of the state of a corner.
* `RData.lvCSt_next`: with the bits of the tests, the update gives the state and the code of level
  `ℓ + 1`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

open Classical in
/-- The update of the state of a corner from the two values `vT`, `vS` of the broadcast runs, the
first parts `fA`, `fB` of the tests of the new corners, the bits `pA`, `pB` of the runs on the pieces,
the digon bit `dg` and the indices `k0`, `k1` of the top annulus at the corner. -/
noncomputable def cstNext (M : ℕ) (vT vS : ℕ∞) (cs : RData.CSt) (fA pA fB pB dg : Bool) (k0 k1 : ℕ → Bool) :
    RData.CSt × ℕ∞ :=
  ({ inΓ := cs.inΓ || dg
     cA := decide (vT < M) && decide (vS < M) &&
       kidA (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1 (decT vT.toNat).2.2.2
         (decS vS.toNat).1 (decS vS.toNat).2 cs.cA (fA || (cs.inΓ && pA))
     cB := decide (vT < M) && decide (vS < M) &&
       kidB (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1 (decT vT.toNat).2.2.2
         (decS vS.toNat).1 (decS vS.toNat).2 (fB || (cs.inΓ && pB)) cs.cB
     src := decide (∃ t, k0 t = true ∧ RData.midTest M vT vS t = true)
     tgt := decide (∃ t, k1 t = true ∧ RData.midTest M vT vS t = true) },
    ⨅ t, ⨅ (_ : k1 t = true), ⨅ (_ : RData.midTest M vT vS t = true),
      ((Nat.pair (kidRange (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1
        (decT vT.toNat).2.2.2 (decS vS.toNat).1 t).1
        (kidRange (decT vT.toNat).1 (decT vT.toNat).2.1 (decT vT.toNat).2.2.1
        (decT vT.toNat).2.2.2 (decS vS.toNat).1 t).2 : ℕ) : ℕ∞))

namespace RData

theorem CSt.ext' {x y : CSt} (h1 : x.inΓ = y.inΓ) (h2 : x.cA = y.cA) (h3 : x.cB = y.cB) (h4 : x.src = y.src)
    (h5 : x.tgt = y.tgt) : x = y := by
  cases x; cases y; simp_all

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}


/-- The corner `z` lies at a vertex of the cut path. -/
def CutAt (z : N.G.Dart × Bool) : Prop := ∃ (σ : Fin 2) (t : ℕ), t ≤ Cp.m ∧ Cp.cut.tail z = Cp.cut.tail (Cp.k σ t)

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


open Classical in
/-- **The state of a corner at the next level from local bits.** Let `fA`, `fB`, `pA`, `pB`, `dg` be
the bits of the tests of the level at a corner `c`, and `k0`, `k1` the indices of the top annulus at
`c`. Then the update of the state of level `ℓ` at `c` is the state and the code of level `ℓ + 1`. -/
theorem lvCSt_next (c : N.G.Dart × Bool) (fA pA fB pB dg : Bool) (k0 k1 : ℕ → Bool)
    (hfA : fA = true ↔ c.2 = false ∧ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ
      (N.toRot.dual.rev c.1, β) ∧
        gateOfA (outT (N.toRot.dual.rev c.1, β)) (outS (N.toRot.dual.rev c.1, β)) = true)
    (hfB : fB = true ↔ c.2 = false ∧ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (c.1, β) ∧
        gateOfB (outT (c.1, β)) (outS (c.1, β)) = true)
    (hpA : pA = true ↔ ∃ y, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt y =
        (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt c ∧
        lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ y ∧ CutAt (Cp := Cp) y)
    (hpB : pB = true ↔ ∃ y, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt y =
        (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt c ∧
        lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.double.rev y) ∧ CutAt (Cp := Cp) y)
    (hdg : dg = true ↔ c.2 = false ∧ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (c.1, β) ∨
        lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.rev c.1, β))
    (hk0 : ∀ t, k0 t = true ↔ c = L₀.κ0 t) (hk1 : ∀ t, k1 t = true ↔ c = L₀.κ1 t) :
    cstNext M' (outT c) (outS c) (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ c) fA pA fB pB dg k0 k1 =
      (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) c,
        lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) c) := by
  set rs := lvSeq hN modeL hostT hhost hE K D M r₀
  set S := lvS modeL hostT hhost (rs ℓ) ℓ
  have hΓ : S.Γ = Γ₀ ∪ (rs ℓ).steps ℓ := (rs ℓ).data_Γ ℓ modeL hostT _
  have htail : ∀ y, (N.toRot.dual.double.split (Γ₀ ∪ (rs ℓ).steps ℓ)).tail c =
      (N.toRot.dual.double.split (Γ₀ ∪ (rs ℓ).steps ℓ)).tail y ↔ S.pieceAt y = S.pieceAt c := fun y => by
    rw [← hΓ]
    change S.dualSplit.tail c = S.dualSplit.tail y ↔ _
    rw [← S.vertexEquiv_pieceAt c, ← S.vertexEquiv_pieceAt y, S.vertexEquiv.injective.eq_iff, eq_comm]
  have hin : (lvCSt (rs ℓ) ℓ c).inΓ = true ↔ c ∈ Γ₀ ∪ (rs ℓ).steps ℓ := by simp [lvCSt]
  have hrev : ∀ x : N.G.Dart, N.toRot.dual.rev (N.toRot.dual.rev x) = x := N.toRot.dual.rev_rev
  have eA : decide (lvNewA hN modeL hostT hhost hE K D M r₀ ℓ (fun y => gateOfA (outT y) (outS y)) c) =
      (fA || ((lvCSt (rs ℓ) ℓ c).inΓ && pA)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, Bool.and_eq_true, hfA, hpA, hin]
    unfold lvNewA
    refine or_congr ⟨?_, ?_⟩ (and_congr_right fun _ => ⟨?_, ?_⟩)
    · rintro ⟨z, hz, hg, rfl⟩
      exact ⟨rfl, z.2, by rw [hrev]; exact hz, by rw [hrev]; exact hg⟩
    · rintro ⟨h2, β, hz, hg⟩
      exact ⟨(N.toRot.dual.rev c.1, β), hz, hg, Prod.ext (hrev c.1).symm h2⟩
    · rintro ⟨z, hz, hcut, ht⟩
      exact ⟨z, (htail z).1 ht, hz, hcut⟩
    · rintro ⟨y, hy, hz, hcut⟩
      exact ⟨y, hz, hcut, (htail y).2 hy⟩
  have eB : decide (lvNewB hN modeL hostT hhost hE K D M r₀ ℓ (fun y => gateOfB (outT y) (outS y)) c) =
      (fB || ((lvCSt (rs ℓ) ℓ c).inΓ && pB)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, Bool.and_eq_true, hfB, hpB, hin]
    unfold lvNewB
    refine or_congr ⟨?_, ?_⟩ (and_congr_right fun _ => ⟨?_, ?_⟩)
    · rintro ⟨z, hz, hg, rfl⟩
      exact ⟨rfl, z.2, hz, hg⟩
    · rintro ⟨h2, β, hz, hg⟩
      exact ⟨(c.1, β), hz, hg, Prod.ext rfl h2⟩
    · rintro ⟨z, hz, hcut, ht⟩
      exact ⟨N.toRot.dual.double.rev z, (htail _).1 ht, by rw [N.toRot.dual.double.rev_rev]; exact hz, hcut⟩
    · rintro ⟨y, hy, hz, hcut⟩
      refine ⟨N.toRot.dual.double.rev y, hz, ?_, ?_⟩
      · rw [N.toRot.dual.double.rev_rev]; exact hcut
      · rw [N.toRot.dual.double.rev_rev]; exact (htail y).2 hy
  have eD : decide (∃ z', lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z' ∧
      (c = (z'.1, false) ∨ c = (N.toRot.dual.rev z'.1, false))) = dg := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hdg]
    constructor
    · rintro ⟨z, hz, rfl | rfl⟩
      · exact ⟨rfl, z.2, .inl hz⟩
      · exact ⟨rfl, z.2, .inr (by rw [hrev]; exact hz)⟩
    · rintro ⟨h2, β, hz | hz⟩
      · exact ⟨_, hz, .inl (Prod.ext rfl h2)⟩
      · exact ⟨_, hz, .inr (Prod.ext (hrev c.1).symm h2)⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := lvCSt_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS M'
    h_in h_guard h_pay c
  refine Prod.ext (CSt.ext' ?_ ?_ ?_ ?_ ?_) ?_
  · rw [h1, eD]; rfl
  · rw [h2, eA]; rfl
  · rw [h3, eB]; rfl
  · show decide _ = _
    rw [Bool.eq_iff_iff, decide_eq_true_iff, h4]
    exact exists_congr fun t => and_congr_left fun _ => hk0 t
  · show decide _ = _
    rw [Bool.eq_iff_iff, decide_eq_true_iff, h5]
    exact exists_congr fun t => and_congr_left fun _ => hk1 t
  · show _ = lvV8 _ _ c
    rw [lvV8_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS outT outS M' h_in h_guard h_pay c]
    exact iInf_congr fun t => (iInf_congr_Prop (hk1 t) fun _ => rfl)

end RData

end RotSystem

end SsspFlow
