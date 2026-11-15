import SsspFlow.GHatLevelKids
import SsspFlow.RunCornerKids

/-!
# The corners of the sides at the next level

In the runs of the levels for the rule of a level, a corner is a corner of a side of an annulus of the
list of level `ℓ + 1` exactly when it passes the test `kidA` (or `kidB`) for an annulus of level `ℓ`,
with the indices and overlap bits of the walk of the chain of its target, whether it is a corner of
that side of the annulus of level `ℓ`, and whether it is a new corner of the step of the node.

* `RData.lv_corners`: the corners of the sides below a subrun of a level.
* `RData.cornerA_succ`, `RData.cornerB_succ`: the corners of the sides of the annuli of the next level.
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

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

open Classical in
/-- **The corners of the sides below a subrun of a level.** -/
theorem lv_corners {s : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ) (hjk : s.2.1.1 + 2 ≤ s.2.1.2) :
    ∃ (kk i1 i2 : ℕ) (S : s.1.2.Step),
      lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 ∧
      (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
          some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk,
            S.darts) ∧
      ∀ c, ((∃ s' ∈ (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
          (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).subs 1,
            s'.2.1.1 + 2 ≤ s'.2.1.2 ∧ s'.1.2.CornerA c) ↔
          kidA s.2.1.1 s.2.1.2 i1 i2
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
            (decide (s.1.2.CornerA c)) (decide (s.1.2.newA S c)) = true) ∧
        ((∃ s' ∈ (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
          (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).subs 1,
            s'.2.1.1 + 2 ≤ s'.2.1.2 ∧ s'.1.2.CornerB c) ↔
          kidB s.2.1.1 s.2.1.2 i1 i2
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
            (decide (s.1.2.newB S c)) (decide (s.1.2.CornerB c)) = true) := by
  obtain ⟨q, S, i1, i2, htop, ⟨kk, rfl, hps, hnone, -⟩, h1, h2, hc⟩ :=
    CutPath.pickF_corners hR hC hgc _ s.2.2 (hpick s hs hjk)
  exact ⟨kk, i1, i2, S, ⟨hps, hnone, h1, h2⟩, htop, hc⟩

/-- **The data of a subrun of a level are unique.** -/
theorem lv_unique {s : CutPath.Sub Cp hR hC hgc} {kk i1 i2 kk' i1' i2' : ℕ} {S S' : s.1.2.Step}
    (hd : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2)
    (ht : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk, S.darts))
    (hd' : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk' i1' i2')
    (ht' : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk', S'.darts)) :
    kk = kk' ∧ i1 = i1' ∧ i2 = i2' ∧ S.darts = S'.darts := by
  obtain ⟨h1, h2, h3, h4⟩ := hd
  obtain ⟨h1', h2', h3', h4'⟩ := hd'
  obtain rfl := Net.parSteps_root_unique h1 h2 h1' h2'
  refine ⟨rfl, h3.unique h3', h4.unique h4', ?_⟩
  rw [ht] at ht'
  exact (Prod.mk.inj (Option.some_injective _ ht')).2

open Classical in
/-- **The corners of the sides of the annuli of the next level.** A corner is a corner of the side of
`κ0(x_a)` of an annulus of the list of level `ℓ + 1` exactly when it passes the test for an annulus of
level `ℓ` with the data of its node. -/
theorem cornerA_succ (c : N.G.Dart × Bool) :
    (∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerA c) ↔
      ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
        ∃ (kk i1 i2 : ℕ) (S : s.1.2.Step),
          lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 ∧
          (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
            (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
              some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk,
                S.darts) ∧
          kidA s.2.1.1 s.2.1.2 i1 i2
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
            (decide (s.1.2.CornerA c)) (decide (s.1.2.newA S c)) = true := by
  set rs := lvSeq hN modeL hostT hhost hE K D M r₀
  set P := lvPof hN modeL hostT hhost hE K D M ℓ (rs ℓ)
  have hmap := r₀.seq_kids hR hC hgc (fun ℓ r => lvPof hN modeL hostT hhost hE K D M ℓ r) ℓ
  have key : (∃ q ∈ (rs (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerA c) ↔
      ∃ s ∈ (rs ℓ).subs ℓ, ∃ s' ∈ (CutPath.pickF hR hC hgc P s.2.2).subs 1,
        s'.2.1.1 + 2 ≤ s'.2.1.2 ∧ s'.1.2.CornerA c := by
    have e1 : (∃ q ∈ (rs (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerA c) ↔
        ∃ x ∈ ((rs (ℓ + 1)).subs (ℓ + 1)).map (fun s => (s.1, s.2.1)), x.2.1 + 2 ≤ x.2.2 ∧ x.1.2.CornerA c := by
      simp only [(rs (ℓ + 1)).mem_levelQ, List.mem_map]
      constructor
      · rintro ⟨_, ⟨s, hs, hjk, rfl⟩, hc⟩
        exact ⟨_, ⟨s, hs, rfl⟩, hjk, hc⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, hjk, hc⟩
        exact ⟨_, ⟨s, hs, hjk, rfl⟩, hc⟩
    rw [e1]
    erw [hmap]
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨s, hs, s', hs', rfl⟩, hjk, hc⟩
      exact ⟨s, hs, s', hs', hjk, hc⟩
    · rintro ⟨s, hs, s', hs', hjk, hc⟩
      exact ⟨_, ⟨s, hs, s', hs', rfl⟩, hjk, hc⟩
  rw [key]
  refine exists_congr fun s => and_congr_right fun hs => ?_
  by_cases hjk : s.2.1.1 + 2 ≤ s.2.1.2
  · obtain ⟨kk, i1, i2, S, hd, ht, hc⟩ := lv_corners hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    rw [(hc c).1]
    constructor
    · exact fun h => ⟨hjk, kk, i1, i2, S, hd, ht, h⟩
    · rintro ⟨-, kk', i1', i2', S', hd', ht', h⟩
      obtain ⟨rfl, rfl, rfl, hS⟩ := lv_unique hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht'
      have e : decide (s.1.2.newA S c) = decide (s.1.2.newA S' c) :=
        decide_eq_decide.2 (CutPath.Live.newA_congr hS c)
      rwa [e]
  · rw [CutPath.pickF_kids_leaf hR hC hgc P s.2.2 (by omega)]
    simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
    exact fun h => absurd h hjk

open Classical in
/-- **The corners of the other sides of the annuli of the next level.** A corner is a corner of the side
of `κ0(x_b)` of an annulus of the list of level `ℓ + 1` exactly when it passes the test for an annulus of
level `ℓ` with the data of its node. -/
theorem cornerB_succ (c : N.G.Dart × Bool) :
    (∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerB c) ↔
      ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
        ∃ (kk i1 i2 : ℕ) (S : s.1.2.Step),
          lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 ∧
          (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
            (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
              some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk,
                S.darts) ∧
          kidB s.2.1.1 s.2.1.2 i1 i2
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
            (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
            (decide (s.1.2.newB S c)) (decide (s.1.2.CornerB c)) = true := by
  set rs := lvSeq hN modeL hostT hhost hE K D M r₀
  set P := lvPof hN modeL hostT hhost hE K D M ℓ (rs ℓ)
  have hmap := r₀.seq_kids hR hC hgc (fun ℓ r => lvPof hN modeL hostT hhost hE K D M ℓ r) ℓ
  have key : (∃ q ∈ (rs (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerB c) ↔
      ∃ s ∈ (rs ℓ).subs ℓ, ∃ s' ∈ (CutPath.pickF hR hC hgc P s.2.2).subs 1,
        s'.2.1.1 + 2 ≤ s'.2.1.2 ∧ s'.1.2.CornerB c := by
    have e1 : (∃ q ∈ (rs (ℓ + 1)).levelQ (ℓ + 1), q.1.2.CornerB c) ↔
        ∃ x ∈ ((rs (ℓ + 1)).subs (ℓ + 1)).map (fun s => (s.1, s.2.1)), x.2.1 + 2 ≤ x.2.2 ∧ x.1.2.CornerB c := by
      simp only [(rs (ℓ + 1)).mem_levelQ, List.mem_map]
      constructor
      · rintro ⟨_, ⟨s, hs, hjk, rfl⟩, hc⟩
        exact ⟨_, ⟨s, hs, rfl⟩, hjk, hc⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, hjk, hc⟩
        exact ⟨_, ⟨s, hs, hjk, rfl⟩, hc⟩
    rw [e1]
    erw [hmap]
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨s, hs, s', hs', rfl⟩, hjk, hc⟩
      exact ⟨s, hs, s', hs', hjk, hc⟩
    · rintro ⟨s, hs, s', hs', hjk, hc⟩
      exact ⟨_, ⟨s, hs, s', hs', rfl⟩, hjk, hc⟩
  rw [key]
  refine exists_congr fun s => and_congr_right fun hs => ?_
  by_cases hjk : s.2.1.1 + 2 ≤ s.2.1.2
  · obtain ⟨kk, i1, i2, S, hd, ht, hc⟩ := lv_corners hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    rw [(hc c).2]
    constructor
    · exact fun h => ⟨hjk, kk, i1, i2, S, hd, ht, h⟩
    · rintro ⟨-, kk', i1', i2', S', hd', ht', h⟩
      obtain ⟨rfl, rfl, rfl, hS⟩ := lv_unique hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht'
      have e : decide (s.1.2.newB S c) = decide (s.1.2.newB S' c) :=
        decide_eq_decide.2 (CutPath.Live.newB_congr hS c)
      rwa [e]
  · rw [CutPath.pickF_kids_leaf hR hC hgc P s.2.2 (by omega)]
    simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
    exact fun h => absurd h hjk

end RData

end RotSystem

end SsspFlow
