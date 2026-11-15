import SsspFlow.GHatLevelPayRun
import SsspFlow.GHatLevelTests
import SsspFlow.GHatLevelUpd

/-!
# The run of a level and the tests of its new corners, as one algorithm

Every node stores the state of a level: its input of the level, the number `m`, the base values of
the corners of the darts at it, the indices of the top annulus at the corners of the darts into it,
and the states and codes of the corners of the darts at it. From these the inputs of the run of the
level follow, and after the run every node has its tests of the corners, the bits of the corners of
the darts into it and the cut bits. One more algorithm gives the tests of the new corners.

* `LvX`, `gsOf`, `valsOf`: the stored state of a level and the inputs of the run of the level.
* `RData.stepLoc_congr`: the test `stepLoc` reads the outputs only at copies hosted at the node.
* `RData.levelPT_local`: the run of the level and the tests of the new corners as one algorithm, with
  the values and bits that `RData.lvCSt_next` takes.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- The stored state of a level at a node: its input of the level, the number `m`, the base values of
the corners, the indices `t` of the top annulus with `z = κ0(t)` and `z = κ1(t)` at the corners of the
darts into it, and the states and codes of the corners of the darts from it and into it. -/
abbrev LvX (n : ℕ) := LevelIn n × ℕ × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) ×
  (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)) ×
  ((Fin n → Bool → RData.CSt × ℕ∞) × (Fin n → Bool → RData.CSt × ℕ∞))

/-- The input `k ≥ 4` of the run of a level from the state and the code of a corner. -/
def gsOf (k : ℕ) (c : RData.CSt × ℕ∞) : ℕ∞ :=
  if k = 4 then (if c.1.cA then 0 else ⊤) else if k = 5 then (if c.1.cB then 0 else ⊤)
  else if k = 6 then (if c.1.src then 0 else ⊤) else if k = 7 then (if c.1.tgt then 0 else ⊤) else c.2

/-- The inputs of the run of a level from the stored state. -/
def valsOf {n : ℕ} (x : LvX n) (k : ℕ) : (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞) :=
  if k ≤ 3 then x.2.2.1 k else (fun u b => gsOf k (x.2.2.2.2.1 u b), fun u b => gsOf k (x.2.2.2.2.2 u b))

namespace RData

theorem stepLoc_congr {n : ℕ} (lin : LevelIn n) (w : Fin n)
    (R r₂ r₃ R' r₂' r₃' : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl fl' : Fin (n * (n * 21)) → Bool × Bool × Bool)
    (h : ∀ y, hostOf y = w → R y = R' y ∧ r₂ y = r₂' y ∧ r₃ y = r₃' y ∧ fl y = fl' y)
    (p : Fin n × Fin n × Bool) : stepLoc lin w R r₂ r₃ fl p = stepLoc lin w R' r₂' r₃' fl' p := by
  unfold stepLoc
  refine decide_eq_decide.2 (exists_congr fun y => ⟨?_, ?_⟩)
  · rintro ⟨hy, h1, h2, h3, h4, h5⟩
    obtain ⟨e1, e2, e3, e4⟩ := h y hy
    refine ⟨hy, e1 ▸ h1, e2 ▸ h2, e4 ▸ h3, e3 ▸ h4, ?_⟩
    rw [Net.parOf, ← e1]
    exact h5
  · rintro ⟨hy, h1, h2, h3, h4, h5⟩
    obtain ⟨e1, e2, e3, e4⟩ := h y hy
    refine ⟨hy, e1 ▸ h1, e2 ▸ h2, e4 ▸ h3, e3 ▸ h4, ?_⟩
    rw [Net.parOf, e1]
    exact h5

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}

/-- The base inputs `0` to `3` of the run of a level: the least index and the least distance to the
end of the cut path at a corner, and the flags of the two sides of the cut path. -/
noncomputable def gsBase (C : N.toRot.dual.CutPath) (k : ℕ) (z : N.G.Dart × Bool) : ℕ∞ :=
  if k = 0 then ⨅ r ∈ cornerIdx C z, (r : ℕ∞) else if k = 1 then ⨅ r ∈ cornerIdx C z, ((C.m - r : ℕ) : ℕ∞)
  else if k = 2 then flagVal C 0 z else flagVal C 1 z

/-- A corner lies at a vertex of the cut path exactly when one of its two flags is `0`. -/
theorem flag_cut (z : N.G.Dart × Bool) : (flagVal Cp 0 z = 0 ∨ flagVal Cp 1 z = 0) ↔ CutAt (Cp := Cp) z := by
  unfold flagVal CutAt
  constructor
  · rintro (h | h)
    · split_ifs at h with h'
      · exact ⟨0, h'⟩
      · exact absurd h ENat.top_ne_zero
    · split_ifs at h with h'
      · exact ⟨1, h'⟩
      · exact absurd h ENat.top_ne_zero
  · rintro ⟨σ, h⟩
    fin_cases σ
    · exact .inl (ite_eq_left h)
    · exact .inr (ite_eq_left h)

variable (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ) (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)

open Classical in
/-- The clauses of the run of a level on the payloads, in the form of the update of the corners. -/
theorem lvPay_bridge (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hRl : R = (lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ))
    (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (outT outS : N.G.Dart × Bool → ℕ∞)
    (hA : ∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, payT q < M ∧ payS q < M ∧ ∀ kk i1 i2,
      Net.ParSteps R ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) kk → (R ((Net.parOf R)^[kk] ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))))).2 = none →
      IsLeast (Cp.idx (q.1.2.κ0 q.2) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).chainDarts hN R ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) 0 kk)) i1 →
      IsGreatest (Cp.idx (q.1.2.κ0 q.2) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).chainDarts hN R ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) 0 kk)) i2 →
      decT (payT q) = ((rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1, (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2, i1, i2) ∧
      decS (payS q) = (decide (∃ c, q.1.2.CornerA c ∧ q.1.2.Visits q.2 ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).chainDarts hN R ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) 0 kk) c),
        decide (∃ c, q.1.2.CornerB c ∧ q.1.2.Visits q.2 ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).chainDarts hN R ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) 0 kk) c)))
    (hB : ∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, ∀ z, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z → outT z = payT q ∧ outS z = payS q)
    (hC : ∀ z, outT z < M → ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z ∧ outT z = payT q) :
    (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → ∀ c, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
      outT c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) ∧
    (∀ c, outT c < M → outS c < M →
      ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧ (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c ∧
        outT c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ outS c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) ∧
    (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
        decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
        decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) = lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk ∧
        payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M) := by
  subst hRl
  have hmem : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → (s.1, (s.2.1.1 + s.2.1.2) / 2) ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ :=
    fun s hs hjk => ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_levelQ ℓ).2 ⟨s, hs, hjk, rfl⟩
  refine ⟨fun s hs hjk c hc => hB _ (hmem s hs hjk) c hc, fun c hT hS => ?_, fun s hs hjk kk i1 i2 hd => ?_⟩
  · obtain ⟨q, hq, hg, he⟩ := hC c hT
    obtain ⟨s, hs, hjk, rfl⟩ := ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_levelQ ℓ).1 hq
    exact ⟨s, hs, hjk, hg, he, (hB _ hq c hg).2⟩
  · obtain ⟨h1, h2, h3⟩ := hA _ (hmem s hs hjk)
    obtain ⟨d1, d2, d3, d4⟩ := hd
    obtain ⟨e1, e2⟩ := h3 kk i1 i2 d1 d2 d3 d4
    refine ⟨?_, e2, h1, h2⟩
    rw [e1, rngA_sub (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hs]

end RData

namespace RData

open Cslib.Congest.Algorithm

open Classical in
/-- **The run of a level and the tests of its new corners as one algorithm.** Every node starts
with its stored state of level `ℓ`. After the run, every node holds, at the corners of the darts into
it, the values of the run of the level and the bits of the tests of the new corners, in the form that
`lvCSt_next` takes, and at the darts from it the bits of the darts of the steps. It also keeps its
stored state. -/
theorem levelPT_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (oT oS : Fin n → σ → Fin n → Bool → ℕ∞) (fA fB pA pB dg : Fin n → σ → Fin n → Bool → Bool)
      (F : Fin n → σ → Fin n → Bool) (xO : Fin n → σ → LvX n),
    T ≤ 31 + 19 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
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
      (∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M) → (Cp.m + 2) ^ 8 ≤ M →
      (∀ w, (X w).1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w) → (∀ w, (X w).2.1 = Cp.m) →
      (∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((X d.fst).2.2.1 k).1 d.snd b = gsBase Cp k (d, b) ∧
        ((X d.snd).2.2.1 k).2 d.fst b = gsBase Cp k (d, b)) →
      (∀ (d : N.G.Dart) b, (X d.fst).2.2.2.2.1 d.snd b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b)) ∧
        (X d.snd).2.2.2.2.2 d.fst b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b))) →
      let st := A.run N.G X T
      let oTc : N.G.Dart × Bool → ℕ∞ := fun z => oT z.1.snd (st z.1.snd) z.1.fst z.2
      let oSc : N.G.Dart × Bool → ℕ∞ := fun z => oS z.1.snd (st z.1.snd) z.1.fst z.2
      (∃ payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ,
        (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → ∀ c, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
          oTc c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ oSc c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) ∧
        (∀ c, oTc c < M → oSc c < M →
          ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧ (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c ∧
            oTc c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ oSc c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) ∧
        (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
          ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
            decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
            decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) = lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk ∧
            payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M)) ∧
      (∀ (d : N.G.Dart) (b : Bool),
        (fA d.snd (st d.snd) d.fst b = true ↔ b = false ∧ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.rev d, β) ∧
          gateOfA (oTc (N.toRot.dual.rev d, β)) (oSc (N.toRot.dual.rev d, β)) = true) ∧
        (fB d.snd (st d.snd) d.fst b = true ↔ b = false ∧ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (d, β) ∧
          gateOfB (oTc (d, β)) (oSc (d, β)) = true) ∧
        (pA d.snd (st d.snd) d.fst b = true ↔
          ∃ y, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt y = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt (d, b) ∧ lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ y ∧ CutAt (Cp := Cp) y) ∧
        (pB d.snd (st d.snd) d.fst b = true ↔
          ∃ y, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt y = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).pieceAt (d, b) ∧ lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.double.rev y) ∧ CutAt (Cp := Cp) y) ∧
        (dg d.snd (st d.snd) d.fst b = true ↔ b = false ∧ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (d, β) ∨ lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.rev d, β)) ∧
        (F d.fst (st d.fst) d.snd = true ↔ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (d, β) ∨ lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.rev d, β))) ∧
      ∀ w, xO w (st w) = X w := by
  obtain ⟨C₁, c₁, hPy⟩ := levelPay_local hE K
  obtain ⟨C₂, c₂, hTs⟩ := levelTests_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, rr, r₂, r₃, rA, rB, o1, o2, offO, flgO, cflO, outT, outS, hT₁, hA₁⟩ := hPy n D
  obtain ⟨σ₂, A₂, fA, fB, pA, pB, dg, F, hA₂⟩ := hTs n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  set W := 4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) with hW
  have w₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤ W := by omega
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤ W := by omega
  set T₂ := 1 + ((1 + (1 + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16))) + (1 + (1 + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16))))
    with hT₂
  let J := LvX n
  let oT1 : Fin n → J × σ₁ → Fin n → Bool → ℕ∞ := fun w y u b =>
    outT (idEquiv (cornerName y.1.1.rot y.1.1.own w u b)) y.2
  let oS1 : Fin n → J × σ₁ → Fin n → Bool → ℕ∞ := fun w y u b =>
    outS (idEquiv (cornerName y.1.1.rot y.1.1.own w u b)) y.2
  let tIn : Fin n → J × σ₁ → TestIn n := fun w y =>
    (y.1.1, fun p => stepLoc y.1.1 w (fun a => rr a y.2) (fun a => r₂ a y.2) (fun a => r₃ a y.2) (fun a => flgO a y.2) p,
      fun u b => (gateOfA (oT1 w y u b) (oS1 w y u b), gateOfB (oT1 w y u b) (oS1 w y u b)),
      (fun u b => decide ((y.1.2.2.1 2).1 u b = 0 ∨ (y.1.2.2.1 3).1 u b = 0),
        fun u b => decide ((y.1.2.2.1 2).2 u b = 0 ∨ (y.1.2.2.1 3).2 u b = 0)))
  let B₁ := (A₁.widen w₁).keep (fun _ (x : J) => (x.1, x.2.1, valsOf x))
  let B₂ := (A₂.widen w₂).keep tIn
  let fin : ∀ {β : Type}, (ℕ × (J × σ₁) → β) → ((J × σ₁) × σ₂ → β) → ((ℕ × (J × σ₁)) ⊕ ((J × σ₁) × σ₂)) → β :=
    fun d G => Sum.elim d G
  refine ⟨_, B₁.seq T₁ (fun _ s => s) B₂, T₁ + T₂,
    fun w s u b => fin (fun _ => ⊤) (fun q => oT1 w q.1 u b) s, fun w s u b => fin (fun _ => ⊤) (fun q => oS1 w q.1 u b) s,
    fun w s u b => fin (fun _ => false) (fun q => fA w q.2 u b) s, fun w s u b => fin (fun _ => false) (fun q => fB w q.2 u b) s,
    fun w s u b => fin (fun _ => false) (fun q => pA w q.2 u b) s, fun w s u b => fin (fun _ => false) (fun q => pB w q.2 u b) s,
    fun w s u b => fin (fun _ => false) (fun q => dg w q.2 u b) s, fun w s u => fin (fun _ => false) (fun q => F w q.2 u) s,
    fun w s => fin (fun p => p.2.1) (fun q => q.1.1) s, ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ ℓ X u₀ hpick hP hc hS hcut hD hc1 hcr hcb hM hQM hM8
    hX1 hX2 hXb hXc
  have hm2 : Cp.m + 2 ≤ (Cp.m + 2) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hM1 : 1 ≤ M := by omega
  have hmM : Cp.m < M := by omega
  have hin1 : (fun w => ((X w).1, (X w).2.1, valsOf (X w))) = fun w => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w, Cp.m, valsOf (X w)) :=
    funext fun w => by rw [hX1 w, hX2 w]
  set st₁ := A₁.run N.G (fun w => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w, Cp.m, valsOf (X w))) T₁ with hst₁
  set st₂ := A₂.run N.G (fun w => tIn w (X w, st₁ w)) T₂ with hst₂
  have hrun : (B₁.seq T₁ (fun _ s => s) B₂).run N.G X (T₁ + T₂) = fun w => .inr ((X w, st₁ w), st₂ w) := by
    funext w
    simp only [B₁, B₂, run_seq, run_keep, run_widen]
    rw [hin1]
  let gs : ℕ → N.G.Dart × Bool → ℕ∞ := fun k z =>
    if k ≤ 3 then gsBase Cp k z else gsOf k (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z, lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z)
  have hmB : Cp.m ≤ (n * (n * 21) + 2) ^ K := by omega
  have hgs : ∀ k z, gs k z = ⊤ ∨ gs k z ≤ (n * (n * 21) + 2) ^ K := by
    intro k z
    simp only [gs]
    split_ifs with hk
    · unfold gsBase
      split_ifs
      · exact ENat.iInf_top_or_le fun r => ENat.iInf_top_or_le fun hr => .inr (by exact_mod_cast hr.1.trans hmB)
      · exact ENat.iInf_top_or_le fun r => ENat.iInf_top_or_le fun _ =>
          .inr (by exact_mod_cast (Nat.sub_le _ _).trans hmB)
      · unfold flagVal; split_ifs <;> simp
      · unfold flagVal; split_ifs <;> simp
    · unfold gsOf
      split_ifs <;> try simp
      unfold lvV8
      refine ENat.iInf_top_or_le fun q => ENat.iInf_top_or_le fun hq => ENat.iInf_top_or_le fun _ => .inr ?_
      obtain ⟨e1, e2⟩ := rngA_le (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hq
      have e3 := pair_lt_sq (a := (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1) (b := (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2) (Y := Cp.m + 1) (by omega) (by omega)
      have e4 : (Cp.m + 1) ^ 2 ≤ (Cp.m + 2) ^ 8 :=
        (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have e5 : Nat.pair (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1 (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2 ≤ (n * (n * 21) + 2) ^ K := by omega
      exact_mod_cast e5
  have hvo : ∀ k (d : N.G.Dart) b, (valsOf (X d.fst) k).1 d.snd b = gs k (d, b) := by
    intro k d b
    simp only [valsOf, gs]
    split_ifs with hk
    · exact (hXb k hk d b).1
    · show gsOf k ((X d.fst).2.2.2.2.1 d.snd b) = _
      rw [(hXc d b).1]
  have hvi : ∀ k (d : N.G.Dart) b, (valsOf (X d.snd) k).2 d.fst b = gs k (d, b) := by
    intro k d b
    simp only [valsOf, gs]
    split_ifs with hk
    · exact (hXb k hk d b).2
    · show gsOf k ((X d.snd).2.2.2.2.2 d.fst b) = _
      rw [(hXc d b).2]
  have h0 : gs 0 = fun z => ⨅ r ∈ cornerIdx Cp z, (r : ℕ∞) := funext fun z => by simp [gs, gsBase]
  have h1 : gs 1 = fun z => ⨅ r ∈ cornerIdx Cp z, ((Cp.m - r : ℕ) : ℕ∞) := funext fun z => by simp [gs, gsBase]
  have h2 : gs 2 = flagVal Cp 0 := funext fun z => by simp [gs, gsBase]
  have h3 : gs 3 = flagVal Cp 1 := funext fun z => by simp [gs, gsBase]
  have h4 : gs 4 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, q.1.2.CornerA z then 0 else ⊤ := by
    rw [← lvG4_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h5 : gs 5 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, q.1.2.CornerB z then 0 else ⊤ := by
    rw [← lvG5_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h6 : gs 6 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, z = qEnd 0 q then 0 else ⊤ := by
    rw [← lvG6_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h7 : gs 7 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, z = qEnd 1 q then 0 else ⊤ := by
    rw [← lvG7_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h8 : gs 8 = fun z => ⨅ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, ⨅ (_ : z = qEnd 1 q),
      ((Nat.pair (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1 (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2 : ℕ) : ℕ∞) := funext fun z => by
    simp only [gs, gsOf, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte]
    rfl
  have hPay := hA₁ N (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) hN (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M cc u₀ (fun w => valsOf (X w)) gs (fun q => rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1) hP hc hS hcut
    hD (fun x => hcb x.1.1) hM hc1 hcr (fun _ => rfl) (fun _ => rfl) ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).data_Γ ℓ modeL hostT _) hQM hM1 hmM hgs
    hvo hvi h0 h1 h2 h3 h4 h5 h6 h7 h8 (fun q hq => rngA_le (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hq) hM8
  obtain ⟨⟨payT, payS, hpA, hpB, hpC, -⟩, hloc, hex, hRe, h₂, h₃, -⟩ := hPay
  have hRl : (fun a => rr a (st₁ (hostOf a))) = lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ := hRe
  have hoT : ∀ z : N.G.Dart × Bool, oT1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2 =
      outT (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV z))) (st₁ z.1.snd) := fun z => by
    show outT (idEquiv (cornerName (X z.1.snd).1.rot (X z.1.snd).1.own z.1.snd z.1.fst z.2)) _ = _
    rw [hX1]
    exact congrArg (outT · _) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cornerName_eq hN z.1 z.2)
  have hoS : ∀ z : N.G.Dart × Bool, oS1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2 =
      outS (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV z))) (st₁ z.1.snd) := fun z => by
    show outS (idEquiv (cornerName (X z.1.snd).1.rot (X z.1.snd).1.own z.1.snd z.1.fst z.2)) _ = _
    rw [hX1]
    exact congrArg (outS · _) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cornerName_eq hN z.1 z.2)
  have hbr := lvPay_bridge hN modeL hostT hhost hE K D M r₀ ℓ _ hRl payT payS
    (fun z => oT1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2) (fun z => oS1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2)
    hpA (fun q hq z hz => by simp only [hoT, hoS]; exact hpB q hq z hz)
    (fun z hz => by simp only [hoT] at hz ⊢; exact hpC z hz)
  have hin2 : (fun w => tIn w (X w, st₁ w)) = fun w => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w, (tIn w (X w, st₁ w)).2.1,
      (tIn w (X w, st₁ w)).2.2.1, ((tIn w (X w, st₁ w)).2.2.2.1, (tIn w (X w, st₁ w)).2.2.2.2)) :=
    funext fun w => Prod.ext (hX1 w) rfl
  rw [hRl] at hex h₂ h₃
  have hSD : ∀ z : N.G.Dart × Bool, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ↔
      ∃ w, (w = z.1.fst ∨ w = z.1.snd) ∧ (tIn w (X w, st₁ w)).2.1 (z.1.fst, z.1.snd, z.2) = true := fun z => by
    rw [lvStepDart_loc hN modeL hostT hhost hE K D M r₀ ℓ hpick hex (fun a => r₂ a (st₁ (hostOf a)))
      (fun a => r₃ a (st₁ (hostOf a))) h₂ h₃ (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ z]
    refine exists_congr fun w => and_congr_right fun _ => ?_
    have hcg : ∀ y, hostOf y = w → lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ y = rr y (st₁ w) ∧
        r₂ y (st₁ (hostOf y)) = r₂ y (st₁ w) ∧ r₃ y (st₁ (hostOf y)) = r₃ y (st₁ w) ∧
        lvFl hN modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ y = flgO y (st₁ w) := fun y hy => by
      subst hy
      exact ⟨(congrFun hRl y).symm, rfl, rfl, ((hloc y).2.1).symm⟩
    show _ ↔ stepLoc (X w).1 w _ _ _ _ _ = true
    rw [hX1 w, stepLoc_congr _ w _ _ _ (fun a => rr a (st₁ w)) (fun a => r₂ a (st₁ w)) (fun a => r₃ a (st₁ w)) _
      (fun a => flgO a (st₁ w)) hcg]
  have hcf : ∀ (d : N.G.Dart) b, ((tIn d.fst (X d.fst, st₁ d.fst)).2.2.2.1 d.snd b = true ↔ CutAt (Cp := Cp) (d, b)) ∧
      ((tIn d.snd (X d.snd, st₁ d.snd)).2.2.2.2 d.fst b = true ↔ CutAt (Cp := Cp) (d, b)) := fun d b => by
    have g2 : ∀ z, gsBase Cp 2 z = flagVal Cp 0 z := fun z => by simp [gsBase]
    have g3 : ∀ z, gsBase Cp 3 z = flagVal Cp 1 z := fun z => by simp [gsBase]
    refine ⟨?_, ?_⟩
    · show decide (_ ∨ _) = true ↔ _
      rw [decide_eq_true_iff, (hXb 2 (by omega) d b).1, (hXb 3 (by omega) d b).1, g2, g3]
      exact flag_cut (d, b)
    · show decide (_ ∨ _) = true ↔ _
      rw [decide_eq_true_iff, (hXb 2 (by omega) d b).2, (hXb 3 (by omega) d b).2, g2, g3]
      exact flag_cut (d, b)
  have hTst := hA₂ N (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ (fun w => (tIn w (X w, st₁ w)).2.1) (fun w => (tIn w (X w, st₁ w)).2.2.1)
    (fun w => (tIn w (X w, st₁ w)).2.2.2.1) (fun w => (tIn w (X w, st₁ w)).2.2.2.2) (lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ)
    (fun z => gateOfA (oT1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2) (oS1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2))
    (fun z => gateOfB (oT1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2) (oS1 z.1.snd (X z.1.snd, st₁ z.1.snd) z.1.fst z.2))
    (CutAt (Cp := Cp)) hP hc hS hcut hD (fun x => hcb x.1.1) hM1 hM hSD (fun _ _ => rfl) hcf
  rw [← hin2] at hTst
  dsimp only
  rw [hrun]
  simp only [fin, Sum.elim_inr]
  exact ⟨⟨payT, payS, hbr⟩, fun d b => hTst d b, fun _ => trivial⟩

end RData

end RotSystem

end SsspFlow
