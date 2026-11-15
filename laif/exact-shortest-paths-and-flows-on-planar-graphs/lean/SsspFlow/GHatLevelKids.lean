import SsspFlow.GHatLevelPick
import SsspFlow.RunKids
import SsspFlow.GHatLevelRoot
import SsspFlow.RunKappa

/-!
# The middle indices of the next level

An index `t` is the middle of a range at the next depth below a node with range `[j, k]`, least and
greatest index `i1`, `i2` and overlap bits `bA`, `bB` exactly when `kidMid j k i1 i2 bA bB t` holds,
a test on numbers. In the runs of the levels for the rule of a level, the middle indices of the annuli
of the list of level `ℓ + 1` are the indices that pass this test for an annulus of level `ℓ`, with the
walk of the chain of its target to the root and the indices and corners of that walk.

* `RotSystem.kidMid`: the test of an index.
* `CutPath.Live.kids_mid`: the test holds exactly for the middle indices of the ranges of the sides.
* `CutPath.Run.mem_levelQ_snd`: the indices of the list of a level are the middles of its ranges.
* `RData.lv_kids`: the ranges below a subrun of a level are those of its sides for the walk of its
  chain.
* `RData.mids_succ`: the middle indices of the next level.
* `RData.mid_inside`: such a middle lies strictly inside the ranges of its annulus of level `ℓ`.
* `RData.next_mid_iff`: the middle indices of the next level from values at the corners of the top
  annulus.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- **The test of an index.** `t` is the middle of `[j, i1]` when the side of `κ0(x_a)` is no overlap and
`j + 2 ≤ i1`, or the middle of `[i2, k]` when the side of `κ0(x_b)` is no overlap and `i2 + 2 ≤ k`. -/
def kidMid (j k i1 i2 : ℕ) (bA bB : Bool) (t : ℕ) : Bool :=
  (!bA && decide (j + 2 ≤ i1) && decide (t = (j + i1) / 2)) ||
    (!bB && decide (i2 + 2 ≤ k) && decide (t = (i2 + k) / 2))

namespace CutPath

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D} {C : R.CutPath} {g : D → ℝ≥0∞}

open Classical in
/-- **The middle indices of the sides.** -/
theorem Live.kids_mid {Γ : Finset (D × Bool)} (L : C.Live g Γ) (j k : ℕ) (q : List (D × Bool))
    (i1 i2 t : ℕ) :
    (∃ ab ∈ L.kids j k q i1 i2, ab.1 + 2 ≤ ab.2 ∧ t = (ab.1 + ab.2) / 2) ↔
      kidMid j k i1 i2 (decide (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c))
        (decide (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c)) t = true := by
  unfold Live.kids kidMid
  by_cases hA : ∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c <;>
  by_cases hB : ∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c <;>
  by_cases h1 : i1 < j <;> by_cases h2 : k < i2 <;>
  simp [hA, hB, h1, h2] <;> omega

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

/-- **The indices of the list of a level** are the middles of the ranges of length at least `2` of
its subruns. -/
theorem Run.mem_levelQ_snd {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ t : ℕ) :
    t ∈ (r.levelQ ℓ).map Prod.snd ↔
      ∃ ab ∈ (r.subs ℓ).map (fun s => s.2.1), ab.1 + 2 ≤ ab.2 ∧ t = (ab.1 + ab.2) / 2 := by
  simp only [List.mem_map, r.mem_levelQ]
  constructor
  · rintro ⟨q, ⟨s, hs, hjk, rfl⟩, rfl⟩
    exact ⟨s.2.1, ⟨s, hs, rfl⟩, hjk, rfl⟩
  · rintro ⟨ab, ⟨s, hs, rfl⟩, hjk, rfl⟩
    exact ⟨_, ⟨s, hs, hjk, rfl⟩, rfl⟩

/-- **The middles below a run lie inside its ranges.** For a subrun at depth `1` with a range `[a, b]`,
every index strictly between `a` and `b` lies strictly inside the ranges of the annulus of the run. -/
theorem Run.sub_one_inside {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) {s : Sub C hR hC hg} (hs : s ∈ r.subs 1) {t : ℕ} (h1 : s.2.1.1 < t)
    (h2 : t < s.2.1.2) : L.xa < t ∧ t < L.xb ∧ L.ya < t ∧ t < L.yb := by
  have hA : s.1 ∈ r.nodes 1 := by
    rw [Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  obtain ⟨b1, b2, b3, b4, -, -⟩ := r.below_nodes 1 s.1 hA
  obtain ⟨-, c1, c2, c3, c4⟩ := s.2.2.bounds
  omega

end CutPath

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ)

/-- The runs of the levels for the rule of a level. -/
noncomputable def lvSeq (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) : ℕ → CutPath.Run hR hC hgc Γ₀ L₀ j k :=
  r₀.seq hR hC hgc fun ℓ r => lvPof hN modeL hostT hhost hE K D M ℓ r

/-- The identifier of the target of a subrun in the network of a level. -/
noncomputable def lvV (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (s : CutPath.Sub Cp hR hC hgc) :
    Fin (n * (n * 21)) :=
  (lvS modeL hostT hhost r ℓ).levelPad hN |>.ι
    (.inl ((lvS modeL hostT hhost r ℓ).endV (s.1.2.κ1 ((s.2.1.1 + s.2.1.2) / 2))))

/-- The walk of `kk` parent steps of the chain of the target of a subrun. -/
noncomputable def lvWalk (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (s : CutPath.Sub Cp hR hC hgc)
    (kk : ℕ) : List (N.G.Dart × Bool) :=
  (lvS modeL hostT hhost r ℓ).chainDarts hN (lvR hN modeL hostT hhost hE K D M r ℓ)
    (lvV hN modeL hostT hhost r ℓ s) 0 kk

/-- The chain of the target of a subrun takes `kk` valid parent steps to a root, and `i1`, `i2` are the
least and the greatest index of the cut path on its walk. -/
def lvDat (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (s : CutPath.Sub Cp hR hC hgc) (kk i1 i2 : ℕ) :
    Prop :=
  Net.ParSteps (lvR hN modeL hostT hhost hE K D M r ℓ) (lvV hN modeL hostT hhost r ℓ s) kk ∧
    ((lvR hN modeL hostT hhost hE K D M r ℓ)
      ((Net.parOf (lvR hN modeL hostT hhost hE K D M r ℓ))^[kk] (lvV hN modeL hostT hhost r ℓ s))).2 =
        none ∧
    IsLeast (Cp.idx (s.1.2.κ0 ((s.2.1.1 + s.2.1.2) / 2)) (lvWalk hN modeL hostT hhost hE K D M r ℓ s kk)) i1 ∧
    IsGreatest (Cp.idx (s.1.2.κ0 ((s.2.1.1 + s.2.1.2) / 2)) (lvWalk hN modeL hostT hhost hE K D M r ℓ s kk)) i2

open Classical in
/-- Whether the walk of `kk` parent steps visits a corner of the side of `κ0(x_a)`, and of the side of
`κ0(x_b)`. -/
noncomputable def lvBits (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (s : CutPath.Sub Cp hR hC hgc)
    (kk : ℕ) : Bool × Bool :=
  (decide (∃ c, s.1.2.CornerA c ∧ s.1.2.Visits ((s.2.1.1 + s.2.1.2) / 2)
      (lvWalk hN modeL hostT hhost hE K D M r ℓ s kk) c),
    decide (∃ c, s.1.2.CornerB c ∧ s.1.2.Visits ((s.2.1.1 + s.2.1.2) / 2)
      (lvWalk hN modeL hostT hhost hE K D M r ℓ s kk) c))

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

/-- **The ranges below a subrun of a level**, in the run of the next level, are those of its sides for
the walk of its chain. -/
theorem lv_kids {s : CutPath.Sub Cp hR hC hgc} (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ)
    (hjk : s.2.1.1 + 2 ≤ s.2.1.2) :
    ∃ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 ∧
      ∀ kk' i1' i2', lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s
          kk' i1' i2' →
        ((CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
          (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).subs 1).map (fun s => s.2.1) =
          s.1.2.kids s.2.1.1 s.2.1.2 (lvWalk hN modeL hostT hhost hE K D M
            (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk') i1' i2' := by
  obtain ⟨q, sd, -, ⟨kk, rfl, hps, hnone, -⟩, ⟨i1, i2, h1, h2⟩, hkids⟩ :=
    CutPath.pickF_kids hR hC hgc _ s.2.2 (hpick s hs hjk)
  refine ⟨kk, i1, i2, ⟨hps, hnone, h1, h2⟩, fun kk' i1' i2' ⟨hps', hnone', h1', h2'⟩ => ?_⟩
  obtain rfl := Net.parSteps_root_unique hps hnone hps' hnone'
  exact hkids i1' i2' h1' h2'

/-- **The middle indices of the next level.** If every annulus of level `ℓ` that is not a leaf has node
data that satisfy the rule, an index is the middle of an annulus of the list of level `ℓ + 1` exactly
when it passes the test for an annulus of level `ℓ`, with the walk of the chain of its target to the
root, the least and greatest index of the cut path on it and whether it visits a corner of each
side. Such an index lies strictly inside the ranges of that annulus. -/
theorem mids_succ (t : ℕ) :
    t ∈ ((lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1)).map Prod.snd ↔
      ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
        ∃ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s
            kk i1 i2 ∧
          kidMid s.2.1.1 s.2.1.2 i1 i2
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
            t = true := by
  set rs := lvSeq hN modeL hostT hhost hE K D M r₀
  set P := lvPof hN modeL hostT hhost hE K D M ℓ (rs ℓ)
  rw [(rs (ℓ + 1)).mem_levelQ_snd (ℓ + 1) t]
  have hmap : ((rs (ℓ + 1)).subs (ℓ + 1)).map (fun s => s.2.1) =
      ((rs ℓ).subs ℓ).flatMap (fun s => ((CutPath.pickF hR hC hgc P s.2.2).subs 1).map (fun s => s.2.1)) := by
    have e := congrArg (List.map Prod.snd) (r₀.seq_kids hR hC hgc
      (fun ℓ r => lvPof hN modeL hostT hhost hE K D M ℓ r) ℓ)
    simp only [List.map_map, List.map_flatMap] at e
    exact e
  rw [hmap]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨ab, ⟨s, hs, hab⟩, h2, rfl⟩
    by_cases hjk : s.2.1.1 + 2 ≤ s.2.1.2
    · obtain ⟨kk, i1, i2, hd, hkids⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
      rw [hkids kk i1 i2 hd] at hab
      exact ⟨s, hs, hjk, kk, i1, i2, hd, (s.1.2.kids_mid _ _ _ i1 i2 _).1 ⟨ab, hab, h2, rfl⟩⟩
    · rw [CutPath.pickF_kids_leaf hR hC hgc P s.2.2 (by omega)] at hab
      exact absurd hab List.not_mem_nil
  · rintro ⟨s, hs, hjk, kk, i1, i2, hd, ht⟩
    obtain ⟨-, -, -, -, hkids⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    obtain ⟨ab, hab, hab2, rfl⟩ := (s.1.2.kids_mid _ _ _ i1 i2 _).2 ht
    exact ⟨ab, ⟨s, hs, by rw [hkids kk i1 i2 hd]; exact hab⟩, hab2, rfl⟩

/-- **A middle of the next level lies inside its annulus of level `ℓ`.** -/
theorem mid_inside {s : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ) (hjk : s.2.1.1 + 2 ≤ s.2.1.2)
    {kk i1 i2 t : ℕ}
    (hd : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2)
    (ht : kidMid s.2.1.1 s.2.1.2 i1 i2
      (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
      (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2 t = true) :
    s.1.2.xa < t ∧ t < s.1.2.xb ∧ s.1.2.ya < t ∧ t < s.1.2.yb := by
  obtain ⟨-, -, -, -, hkids⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
  obtain ⟨ab, hab, hab2, rfl⟩ := (s.1.2.kids_mid _ _ _ i1 i2 _).2 ht
  rw [← hkids kk i1 i2 hd] at hab
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hab
  exact (CutPath.pickF hR hC hgc _ s.2.2).sub_one_inside hs' (by omega) (by omega)

/-- **The middles of the next level from the values at the corners.** Let `outT t` and `outS t` be values
at the corner of index `t` that equal the values `payT` and `payS` of the annulus of level `ℓ` whose
ranges hold `t` strictly inside, and that are below `M'` only when they are the values of some annulus
of level `ℓ`. Let `decT` and `decS` read the range, the two indices and the two overlap bits from these
values, all below `M'`. Then `t` is the middle of an annulus of level `ℓ + 1` exactly when both values
are below `M'` and the read data pass the test. -/
theorem next_mid_iff (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (outT outS : ℕ → ℕ∞) (M' : ℕ) (decT : ℕ → ℕ × ℕ × ℕ × ℕ) (decS : ℕ → Bool × Bool)
    (h_in : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → ∀ t,
      s.1.2.xa < t → t < s.1.2.xb → s.1.2.ya < t → t < s.1.2.yb →
      outT t = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS t = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
    (h_guard : ∀ t, outT t < M' → outS t < M' →
      ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
        outT t = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS t = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
    (h_pay : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
        decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
        decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) =
          lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk ∧
        payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M' ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M')
    (t : ℕ) :
    t ∈ ((lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1)).map Prod.snd ↔
      outT t < M' ∧ outS t < M' ∧
        kidMid (decT (outT t).toNat).1 (decT (outT t).toNat).2.1 (decT (outT t).toNat).2.2.1
          (decT (outT t).toNat).2.2.2 (decS (outS t).toNat).1 (decS (outS t).toNat).2 t = true := by
  rw [mids_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick t]
  constructor
  · rintro ⟨s, hs, hjk, kk, i1, i2, hd, ht⟩
    obtain ⟨x1, x2, x3, x4⟩ := mid_inside hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk hd ht
    obtain ⟨e1, e2⟩ := h_in s hs hjk t x1 x2 x3 x4
    obtain ⟨d1, d2, l1, l2⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1, d2]
    exact ⟨by exact_mod_cast l1, by exact_mod_cast l2, ht⟩
  · rintro ⟨h1, h2, ht⟩
    obtain ⟨s, hs, hjk, e1, e2⟩ := h_guard t h1 h2
    obtain ⟨kk, i1, i2, hd, -⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    obtain ⟨d1, d2, -, -⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1, d2] at ht
    exact ⟨s, hs, hjk, kk, i1, i2, hd, ht⟩

end RData

end RotSystem

end SsspFlow
