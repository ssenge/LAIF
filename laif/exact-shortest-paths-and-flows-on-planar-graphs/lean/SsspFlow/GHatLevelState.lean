import SsspFlow.GHatStepCorners

/-!
# The state of the next level

The corners of the next level are those of the level and the digon corners of the darts of the steps
of the level. The range of an annulus of the next level is read at its middle from the range, the two
indices and the two overlap bits of its annulus of the level: it is the range of the side of `κ0(x_a)`
when that side passes the test for the middle, and the range of the other side otherwise. The range,
the two indices and the two bits travel as one number each, by the pairing function of the natural
numbers.

* `CutPath.pickF_top_leaf`: a range below `2` has no step.
* `RData.lv_steps_succ`: the corners of the next level.
* `RotSystem.kidRange`, `RData.next_range`: the range of an annulus of the next level from the values
  at its middle.
* `RotSystem.encT`, `RotSystem.decT`, `RotSystem.encS`, `RotSystem.decS`: the encoding of the range and
  the indices, and of the bits, with `decT_encT`, `decS_encS` and the bounds `encT_lt`, `encS_lt`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- The range of the annulus of the next level with middle `t`: the side of `κ0(x_a)` when it passes
the test for `t`, the other side otherwise. -/
def kidRange (j k i1 i2 : ℕ) (bA : Bool) (t : ℕ) : ℕ × ℕ :=
  if (!bA && decide (j + 2 ≤ i1) && decide (t = (j + i1) / 2)) = true then (j, i1) else (i2, k)

/-- The range and the two indices as one number. -/
def encT (a : ℕ × ℕ × ℕ × ℕ) : ℕ := Nat.pair a.1 (Nat.pair a.2.1 (Nat.pair a.2.2.1 a.2.2.2))

/-- The range and the two indices from one number. -/
def decT (v : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (v.unpair.1, v.unpair.2.unpair.1, v.unpair.2.unpair.2.unpair.1, v.unpair.2.unpair.2.unpair.2)

/-- The two overlap bits as one number. -/
def encS (b : Bool × Bool) : ℕ := Nat.pair b.1.toNat b.2.toNat

/-- The two overlap bits from one number. -/
def decS (v : ℕ) : Bool × Bool := (decide (v.unpair.1 = 1), decide (v.unpair.2 = 1))

@[simp] theorem decT_encT (a : ℕ × ℕ × ℕ × ℕ) : decT (encT a) = a := by
  simp [encT, decT]

@[simp] theorem decS_encS (b : Bool × Bool) : decS (encS b) = b := by
  obtain ⟨b1, b2⟩ := b
  cases b1 <;> cases b2 <;> simp [encS, decS]

theorem pair_lt_sq {a b Y : ℕ} (ha : a + 1 ≤ Y) (hb : b + 1 ≤ Y) : Nat.pair a b < Y ^ 2 :=
  (Nat.pair_lt_max_add_one_sq a b).trans_le (Nat.pow_le_pow_left (by omega) 2)

/-- **The bound of the encoding of the range and the indices.** -/
theorem encT_lt {B : ℕ} {a : ℕ × ℕ × ℕ × ℕ} (h1 : a.1 ≤ B) (h2 : a.2.1 ≤ B) (h3 : a.2.2.1 ≤ B)
    (h4 : a.2.2.2 ≤ B) : encT a < (B + 2) ^ 8 := by
  have hY : B + 2 ≤ (B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : (B + 2) ^ 2 ≤ (B + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e1 := pair_lt_sq (a := a.2.2.1) (b := a.2.2.2) (Y := B + 2) (by omega) (by omega)
  have e2 := pair_lt_sq (a := a.2.1) (b := Nat.pair a.2.2.1 a.2.2.2) (Y := (B + 2) ^ 2) (by omega) (by omega)
  have e3 := pair_lt_sq (a := a.1) (b := Nat.pair a.2.1 (Nat.pair a.2.2.1 a.2.2.2)) (Y := (B + 2) ^ 4)
    (by omega) (by rw [show (B + 2) ^ 4 = ((B + 2) ^ 2) ^ 2 by ring]; omega)
  unfold encT
  calc _ < ((B + 2) ^ 4) ^ 2 := e3
    _ = (B + 2) ^ 8 := by ring

/-- **The bound of the encoding of the bits.** -/
theorem encS_lt (b : Bool × Bool) : encS b < 4 := by
  obtain ⟨b1, b2⟩ := b
  cases b1 <;> cases b2 <;> decide

namespace CutPath

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D} {C : R.CutPath} {g₀ : D → ℕ}
  (hR : R.Planar) (hC : R.Connected)
  (hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x)
  (P : (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ → List (D × Bool) →
    List (D × Bool) → Prop)

/-- **A range below `2` has no step.** -/
theorem pickF_top_leaf {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k) (hk : k < j + 2) : (pickF hR hC hgc P r).top = none := by
  unfold pickF
  split_ifs with h
  · exact absurd (Classical.choice h).1.hjk (by omega)
  · cases r with
    | leaf => rfl
    | node hjk => omega

end CutPath

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

/-- **The corners of the next level** are those of the level and the digon corners of the darts of the
steps of the level. -/
theorem lv_steps_succ (x : N.G.Dart × Bool) :
    x ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).steps (ℓ + 1) ↔
      x ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ ∨
        ∃ z, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ∧
          (x = (z.1, false) ∨ x = (N.toRot.dual.rev z.1, false)) := by
  show x ∈ ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).graft _ ℓ).steps (ℓ + 1) ↔ _
  rw [CutPath.Run.mem_steps_graft_succ, CutPath.Run.subs_graft_self]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨x', hx', q, sd, ht, z, hz, hx⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx'
    replace ht : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top = some (q, sd) := ht
    by_cases hjk : s.2.1.1 + 2 ≤ s.2.1.2
    · obtain ⟨kk, i1, i2, S, hd, ht', -⟩ := lv_corners hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
      rw [ht'] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ht)
      exact ⟨z, ⟨s, hs, hjk, kk, i1, i2, S, hd, ht', hz⟩, hx⟩
    · rw [CutPath.pickF_top_leaf hR hC hgc _ s.2.2 (by omega)] at ht
      exact absurd ht (by simp)
  · rintro ⟨z, ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, hz⟩, hx⟩
    exact ⟨_, List.mem_map.2 ⟨s, hs, rfl⟩, _, _, ht, z, hz, hx⟩

/-- **The range of an annulus of the next level from the values at its middle.** With the values
`outT t` and `outS t` of `RData.next_mid_iff`, the range of an annulus of level `ℓ + 1` with middle `t`
is `kidRange` of the read data at `t`. -/
theorem next_range (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (outT outS : ℕ → ℕ∞) (decT' : ℕ → ℕ × ℕ × ℕ × ℕ) (decS' : ℕ → Bool × Bool)
    (h_in : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → ∀ t,
      s.1.2.xa < t → t < s.1.2.xb → s.1.2.ya < t → t < s.1.2.yb →
      outT t = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS t = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
    (h_pay : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
        decT' (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
        decS' (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) =
          lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk)
    {s' : CutPath.Sub Cp hR hC hgc} (hs' : s' ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).subs (ℓ + 1))
    (hjk' : s'.2.1.1 + 2 ≤ s'.2.1.2) :
    kidRange (decT' (outT ((s'.2.1.1 + s'.2.1.2) / 2)).toNat).1
      (decT' (outT ((s'.2.1.1 + s'.2.1.2) / 2)).toNat).2.1
      (decT' (outT ((s'.2.1.1 + s'.2.1.2) / 2)).toNat).2.2.1
      (decT' (outT ((s'.2.1.1 + s'.2.1.2) / 2)).toNat).2.2.2
      (decS' (outS ((s'.2.1.1 + s'.2.1.2) / 2)).toNat).1 ((s'.2.1.1 + s'.2.1.2) / 2) = s'.2.1 := by
  classical
  have hm : (s'.1, s'.2.1) ∈ ((lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).subs (ℓ + 1)).map
      (fun s => (s.1, s.2.1)) := List.mem_map_of_mem hs'
  have hk : ((lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)).subs (ℓ + 1)).map (fun s => (s.1, s.2.1)) =
      ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ).flatMap
        (fun s => ((CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
          (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).subs 1).map (fun s => (s.1, s.2.1))) :=
    r₀.seq_kids hR hC hgc (fun ℓ r => lvPof hN modeL hostT hhost hE K D M ℓ r) ℓ
  rw [hk] at hm
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.1 hm
  obtain ⟨s'', hs'', e⟩ := List.mem_map.1 hm
  have hab : s'.2.1 ∈ ((CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
      (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).subs 1).map (fun s => s.2.1) :=
    List.mem_map.2 ⟨s'', hs'', (Prod.mk.inj e).2⟩
  have hjk : s.2.1.1 + 2 ≤ s.2.1.2 := by
    by_contra h
    rw [CutPath.pickF_kids_leaf hR hC hgc _ s.2.2 (by omega)] at hab
    exact absurd hab List.not_mem_nil
  obtain ⟨kk, i1, i2, hd, hkids⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
  rw [hkids kk i1 i2 hd] at hab
  have ht : kidMid s.2.1.1 s.2.1.2 i1 i2
      (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1
      (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2
      ((s'.2.1.1 + s'.2.1.2) / 2) = true :=
    (s.1.2.kids_mid _ _ _ i1 i2 _).1 ⟨s'.2.1, hab, hjk', rfl⟩
  obtain ⟨x1, x2, x3, x4⟩ := mid_inside hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk hd ht
  obtain ⟨e1, e2⟩ := h_in s hs hjk _ x1 x2 x3 x4
  obtain ⟨d1, d2⟩ := h_pay s hs hjk kk i1 i2 hd
  rw [e1, e2, ENat.toNat_natCast, ENat.toNat_natCast, d1, d2]
  have hle : i1 ≤ i2 := hd.2.2.2.2 hd.2.2.1.1
  unfold CutPath.Live.kids at hab
  unfold kidRange lvBits
  simp only [List.mem_append] at hab
  rcases hab with hab | hab
  · split_ifs at hab with hA
    · exact absurd hab List.not_mem_nil
    · rw [List.mem_singleton] at hab
      have hnA := fun h => hA (Or.inl h)
      rw [hab] at hjk' ⊢
      rw [ite_eq_left_of_eq_true _ _ (by rw [decide_eq_false hnA]; simp [hjk'])]
  · split_ifs at hab with hB
    · exact absurd hab List.not_mem_nil
    · rw [List.mem_singleton] at hab
      rw [hab] at hjk' ⊢
      rw [ite_eq_right_of_eq_false]
      apply eq_false
      intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨-, h1⟩, h2⟩ := hc
      omega

end RData

end RotSystem

end SsspFlow
