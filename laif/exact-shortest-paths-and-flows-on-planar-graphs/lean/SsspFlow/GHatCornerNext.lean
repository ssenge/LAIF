import SsspFlow.GHatLevelCorners

/-!
# The corners of the sides of the next level from values at the corners

The corners of the sides of an annulus of a run lie in the component of the run, so the corners of the
sides of the annuli of level `ℓ + 1` lie in the component of their annulus of level `ℓ`. A corner
reads the range, the two indices and the two overlap bits of that annulus from two values at its copy,
and decides with its own bits whether it is a corner of a side at the next level.

* `CutPath.Run.boundary_gcomp`: a corner of a side of an annulus of a run lies in the component of the
  run.
* `RData.next_cornerA_iff`, `RData.next_cornerB_iff`: the corners of the sides of the next level from
  values at the corners.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace CutPath

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D} {C : R.CutPath} {g : D → ℝ≥0∞}
  {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

/-- **The corners of the sides of the annuli of a run lie in its component.** -/
theorem Run.boundary_gcomp {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (ℓ : ℕ) {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {c : D × Bool}
    (hc : A.2.CornerA c ∨ A.2.CornerB c) : (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) c :=
  have h := (r.inv ℓ).1 A hA
  connect_trans h.2.2 (RootedTree.gcomp_split_mono h.1
    (A.2.gcomp_bound (A.2.κ0_mem le_rfl A.2.le_x) (A.2.corner_mem hc)))

end CutPath

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ)

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)

/-- A corner in the component of a subrun of a level that is a corner of a side of an annulus of the
list of the level is a corner of that subrun. -/
theorem corner_of_region {s : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ) {c : N.G.Dart × Bool}
    (hreg : (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ}
    (hq : q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ)
    (hc : q.1.2.CornerA c ∨ q.1.2.CornerB c) : q.1 = s.1 := by
  have hsn : s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  exact ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).sep ℓ s.1 hsn q.1
    ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ_range ℓ q hq).1 c hreg
    (q.1.2.gcomp_bound (q.1.2.κ0_mem le_rfl q.1.2.le_x) (q.1.2.corner_mem hc))).symm

variable
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

open Classical in
/-- A corner that passes the test for a subrun of a level lies in its component. -/
theorem region_of_kidA {s : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ) (hjk : s.2.1.1 + 2 ≤ s.2.1.2)
    {kk i1 i2 : ℕ} {S : s.1.2.Step}
    (hd : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2)
    (ht : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk, S.darts))
    {c : N.G.Dart × Bool} (σ : Bool)
    (hk : (if σ then kidA s.2.1.1 s.2.1.2 i1 i2
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
        (decide (s.1.2.CornerA c)) (decide (s.1.2.newA S c))
      else kidB s.2.1.1 s.2.1.2 i1 i2
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
        (decide (s.1.2.newB S c)) (decide (s.1.2.CornerB c))) = true) :
    (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c := by
  classical
  obtain ⟨kk', i1', i2', S', hd', ht', hc⟩ := lv_corners hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
  obtain ⟨rfl, rfl, rfl, hS⟩ := lv_unique hN modeL hostT hhost hE K D M r₀ ℓ hpick hd' ht' hd ht
  have eA : decide (s.1.2.newA S' c) = decide (s.1.2.newA S c) :=
    decide_eq_decide.2 (CutPath.Live.newA_congr hS c)
  have eB : decide (s.1.2.newB S' c) = decide (s.1.2.newB S c) :=
    decide_eq_decide.2 (CutPath.Live.newB_congr hS c)
  have hex : ∃ s' ∈ (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
      (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).subs 1,
        s'.1.2.CornerA c ∨ s'.1.2.CornerB c := by
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [← eB] at hk
      obtain ⟨s', hs', -, h⟩ := ((hc c).2).2 hk
      exact ⟨s', hs', Or.inr h⟩
    · simp only [↓reduceIte] at hk
      rw [← eA] at hk
      obtain ⟨s', hs', -, h⟩ := ((hc c).1).2 hk
      exact ⟨s', hs', Or.inl h⟩
  obtain ⟨s', hs', hcs⟩ := hex
  have hn : s'.1 ∈ (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
      (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).nodes 1 := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs'
  exact CutPath.Run.boundary_gcomp _ 1 hn hcs

variable
  (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
  (outT outS : N.G.Dart × Bool → ℕ∞) (M' : ℕ) (decT : ℕ → ℕ × ℕ × ℕ × ℕ) (decS : ℕ → Bool × Bool)
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
include h_in h_guard h_pay

open Classical in
/-- **The corners of the sides of the next level from the values at the corners.** Let `outT c` and
`outS c` be values at a corner `c` that equal the values `payT` and `payS` of the annulus of level `ℓ`
in whose component `c` lies, and that are below `M'` only for such a corner. Let `decT` and `decS` read
the range, the two indices and the two overlap bits from these values. Let the bit `oldA c` tell whether
`c` is a corner of the side of `κ0(x_a)` of an annulus of level `ℓ`, and let `newA' c` tell, for `c` in
the component of an annulus of level `ℓ` whose child on the side of `κ0(x_b)` exists, whether it is a
new corner of the step of its node. Then `c` is a corner of the side of `κ0(x_a)` of an annulus of level `ℓ + 1` exactly when both values are below `M'`
and the read data and the two bits pass the test. -/
theorem next_cornerA_iff (oldA newA' : N.G.Dart × Bool → Bool)
    (h_old : ∀ c, oldA c = true ↔ ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, q.1.2.CornerA c)
    (h_new : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ (kk i1 i2 : ℕ) (S : s.1.2.Step),
        lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
        (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
          (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
            some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk,
              S.darts) →
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2 = false →
        i2 + 2 ≤ s.2.1.2 →
        ∀ c, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
          (newA' c = true ↔ s.1.2.newA S c))
    (c : N.G.Dart × Bool) :
    (∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerA c) ↔
      outT c < M' ∧ outS c < M' ∧
        kidA (decT (outT c).toNat).1 (decT (outT c).toNat).2.1 (decT (outT c).toNat).2.2.1
          (decT (outT c).toNat).2.2.2 (decS (outS c).toNat).1 (decS (outS c).toNat).2
          (oldA c) (newA' c) = true := by
  have hb : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
      oldA c = decide (s.1.2.CornerA c) := fun s hs hjk hreg => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, h_old]
    constructor
    · rintro ⟨q, hq, hc⟩
      exact corner_of_region hN modeL hostT hhost hE K D M r₀ ℓ hs hreg hq (Or.inl hc) ▸ hc
    · exact fun hc => ⟨(s.1, (s.2.1.1 + s.2.1.2) / 2),
        (CutPath.Run.mem_levelQ _ ℓ).2 ⟨s, hs, hjk, rfl⟩, hc⟩
  rw [cornerA_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick c]
  constructor
  · rintro ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, hk⟩
    have hreg := region_of_kidA hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk hd ht true
      (by simp only [↓reduceIte]; exact hk)
    obtain ⟨e1, e2⟩ := h_in s hs hjk c hreg
    obtain ⟨d1, d2, l1, l2⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1, d2, hb s hs hjk hreg,
      kidA_congr (fun h1 h2 => Bool.eq_iff_iff.2
        ((h_new s hs hjk kk i1 i2 S hd ht h1 h2 c hreg).trans decide_eq_true_iff.symm))]
    exact ⟨by exact_mod_cast l1, by exact_mod_cast l2, hk⟩
  · rintro ⟨h1, h2, hk⟩
    obtain ⟨s, hs, hjk, hreg, e1, e2⟩ := h_guard c h1 h2
    obtain ⟨kk, i1, i2, S, hd, ht, -⟩ := lv_corners hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    obtain ⟨d1, d2, -, -⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1, d2, hb s hs hjk hreg,
      kidA_congr (fun h1 h2 => Bool.eq_iff_iff.2
        ((h_new s hs hjk kk i1 i2 S hd ht h1 h2 c hreg).trans decide_eq_true_iff.symm))] at hk
    exact ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, hk⟩

open Classical in
/-- **The corners of the other sides of the next level from the values at the corners**, as
`next_cornerA_iff` for the side of `κ0(x_b)`. -/
theorem next_cornerB_iff (oldB newB' : N.G.Dart × Bool → Bool)
    (h_old : ∀ c, oldB c = true ↔ ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, q.1.2.CornerB c)
    (h_new : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ (kk i1 i2 : ℕ) (S : s.1.2.Step),
        lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
        (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
          (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
            some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk,
              S.darts) →
        (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1 = false →
        s.2.1.1 + 2 ≤ i1 →
        ∀ c, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
          (newB' c = true ↔ s.1.2.newB S c))
    (c : N.G.Dart × Bool) :
    (∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerB c) ↔
      outT c < M' ∧ outS c < M' ∧
        kidB (decT (outT c).toNat).1 (decT (outT c).toNat).2.1 (decT (outT c).toNat).2.2.1
          (decT (outT c).toNat).2.2.2 (decS (outS c).toNat).1 (decS (outS c).toNat).2
          (newB' c) (oldB c) = true := by
  have hb : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
      oldB c = decide (s.1.2.CornerB c) := fun s hs hjk hreg => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, h_old]
    constructor
    · rintro ⟨q, hq, hc⟩
      exact corner_of_region hN modeL hostT hhost hE K D M r₀ ℓ hs hreg hq (Or.inr hc) ▸ hc
    · exact fun hc => ⟨(s.1, (s.2.1.1 + s.2.1.2) / 2),
        (CutPath.Run.mem_levelQ _ ℓ).2 ⟨s, hs, hjk, rfl⟩, hc⟩
  rw [cornerB_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick c]
  constructor
  · rintro ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, hk⟩
    have hreg := region_of_kidA hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk hd ht false
      (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hk)
    obtain ⟨e1, e2⟩ := h_in s hs hjk c hreg
    obtain ⟨d1, d2, l1, l2⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1, d2, hb s hs hjk hreg,
      kidB_congr (fun h1 h2 => Bool.eq_iff_iff.2
        ((h_new s hs hjk kk i1 i2 S hd ht h1 h2 c hreg).trans decide_eq_true_iff.symm))]
    exact ⟨by exact_mod_cast l1, by exact_mod_cast l2, hk⟩
  · rintro ⟨h1, h2, hk⟩
    obtain ⟨s, hs, hjk, hreg, e1, e2⟩ := h_guard c h1 h2
    obtain ⟨kk, i1, i2, S, hd, ht, -⟩ := lv_corners hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    obtain ⟨d1, d2, -, -⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1, d2, hb s hs hjk hreg,
      kidB_congr (fun h1 h2 => Bool.eq_iff_iff.2
        ((h_new s hs hjk kk i1 i2 S hd ht h1 h2 c hreg).trans decide_eq_true_iff.symm))] at hk
    exact ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, hk⟩

end RData

end RotSystem

end SsspFlow
