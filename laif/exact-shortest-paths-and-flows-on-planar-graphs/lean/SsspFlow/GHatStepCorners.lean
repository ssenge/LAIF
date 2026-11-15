import SsspFlow.GHatCornerNext
import SsspFlow.GHatRegion

/-!
# The new corners of the steps from the darts of the steps

The new corners of the side of `κ0(x_a)` of the child of a step are the corner `κ0(x)` of its first
end and the digon corners at the heads of its darts; those of the side of `κ0(x_b)` are the corner
`κ1(y)` of its last end and the digon corners at the tails of its darts. Only the first dart of a step
starts at a vertex of the cut path, and only the last one ends there. So a corner of the level tells
from the darts of all steps of the level and from one bit per dart whether it is a new corner of the
step of the annulus in whose component it lies: it is the digon corner of a dart of a step whose bit
is set, or it is a corner of the level at the vertex of the cut along the corners of the level where
the first dart starts (or the last dart ends).

* `CutPath.Live.Step.first_of_cut`, `CutPath.Live.Step.last_of_cut`: only the first dart starts and
  only the last dart ends at a vertex of the cut path.
* `CutPath.Run.fconnect_level_iff`: in the component of an annulus of a level, the vertices of the cut
  along the corners of the level are those of the cut along the corners of the annulus.
* `RData.lvNewA_iff`, `RData.lvNewB_iff`: the new corners of the steps of a level from the darts of
  the steps.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace CutPath

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D} {C : R.CutPath} {g : D → ℝ≥0∞}

namespace Live

variable {Γ : Finset (D × Bool)} {L : C.Live g Γ}

/-- **Only the first dart of a step starts at a vertex of the cut path.** -/
theorem Step.first_of_cut (S : L.Step) {i : ℕ} (hi : i < S.n) {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m)
    (h : C.cut.tail (S.q i) = C.cut.tail (C.k σ t)) : i = 0 := by
  by_contra h0
  have e := C.tail_fst_of_cut h
  rw [C.tail_k ht] at e
  exact S.inner i (Nat.pos_of_ne_zero h0) hi t ht e

/-- **Only the last dart of a step ends at a vertex of the cut path.** -/
theorem Step.last_of_cut (S : L.Step) {i : ℕ} (hi : i < S.n) {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m)
    (h : C.cut.tail (R.double.rev (S.q i)) = C.cut.tail (C.k σ t)) : i = S.n - 1 := by
  by_contra h0
  have e := C.tail_fst_of_cut h
  rw [C.tail_k ht] at e
  have e2 : R.tail (R.double.rev (S.q i)).1 = R.tail (S.q (i + 1)).1 :=
    C.tail_fst_of_cut ((C.cut.tail_eq_iff _ _).2
      (fconnect_of_split_subset L.sub (S.walk i (by omega))))
  exact S.inner (i + 1) (by omega) (by omega) t ht (e2.symm.trans e)

/-- The first dart of a step starts at the vertex of the cut of `κ0(x)`. -/
theorem Step.cut_first (S : L.Step) : C.cut.tail (S.q 0) = C.cut.tail (C.k 0 S.x) :=
  (C.cut.tail_eq_iff _ _).2
    (connect_trans (fconnect_of_split_subset L.sub S.start) (L.piece0 S.x S.hxa S.hxb))

/-- The last dart of a step ends at the vertex of the cut of `κ1(y)`. -/
theorem Step.cut_last (S : L.Step) :
    C.cut.tail (R.double.rev (S.q (S.n - 1))) = C.cut.tail (C.k 1 S.y) :=
  (C.cut.tail_eq_iff _ _).2
    (connect_trans (fconnect_of_split_subset L.sub S.stop) (L.piece1 S.y S.hya S.hyb))

/-- The darts of a step and their reverses lie in the component of the annulus. -/
theorem Step.gcomp_q (S : L.Step) {i : ℕ} (hi : i < S.n) :
    (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (S.q i) ∧
      (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (R.double.rev (S.q i)) := by
  have h := gcomp_walk (M := R.double.split Γ) S.start S.walk i hi
  have h0 := L.gcomp_κ0 S.hxa S.hxb
  exact ⟨connect_trans h0 h.1, connect_trans h0 h.2⟩

end Live

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}
  {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}

/-- **The vertices of the level in the component of an annulus.** In the component of an annulus at
depth `ℓ`, two darts lie at one vertex of the cut along the corners of the level exactly when they lie
at one vertex of the cut along the corners of the annulus. -/
theorem Run.fconnect_level_iff (r : Run hR hC hg Γ L j k) (ℓ : ℕ)
    {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {a b : D × Bool}
    (ha : (R.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) a) :
    fconnect (R.double.split (Γ ∪ r.steps ℓ)).rot a b ↔ fconnect (R.double.split A.1).rot a b :=
  R.double.fconnect_split_split_iff (r.subset_level ℓ hA) fun w hw hwA h => by
    obtain ⟨p, hp⟩ := exists_walk_of_gcomp
      (connect_trans ha ((R.double.split A.1).toHypermap.gcomp_of_cnode h))
    exact r.unreach_level ℓ hA hw hwA le_rfl A.2.le_x p hp

/-- A corner of the level in the component of an annulus at depth `ℓ` is a corner of the annulus. -/
theorem Run.mem_of_level (r : Run hR hC hg Γ L j k) (ℓ : ℕ)
    {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {c : D × Bool}
    (hc : c ∈ Γ ∪ r.steps ℓ) (hreg : (R.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) c) :
    c ∈ A.1 := by
  by_contra h
  obtain ⟨p, hp⟩ := exists_walk_of_gcomp hreg
  exact r.unreach_level ℓ hA hc h le_rfl A.2.le_x p hp

end CutPath

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ)

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)

/-- The darts of the steps of the annuli of level `ℓ`. -/
def lvStepDart (z : N.G.Dart × Bool) : Prop :=
  ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
    ∃ (kk i1 i2 : ℕ) (S : s.1.2.Step),
      lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 ∧
      (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
          some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk,
            S.darts) ∧ z ∈ S.darts

/-- The local test for a new corner of the side of `κ0(x_a)`: the digon corner at the head of a dart
of a step whose bit is set, or a corner of the level at the vertex where a dart of a step starts at a
vertex of the cut path. -/
def lvNewA (gate : N.G.Dart × Bool → Bool) (c : N.G.Dart × Bool) : Prop :=
  (∃ z, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ∧ gate z = true ∧
      c = (N.toRot.dual.rev z.1, false)) ∨
    (c ∈ Γ₀ ∪ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ ∧
      ∃ z, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ∧
        (∃ (σ : Fin 2) (t : ℕ), t ≤ Cp.m ∧ Cp.cut.tail z = Cp.cut.tail (Cp.k σ t)) ∧
        (N.toRot.dual.double.split (Γ₀ ∪ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ)).tail c =
          (N.toRot.dual.double.split (Γ₀ ∪ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ)).tail z)

/-- The local test for a new corner of the side of `κ0(x_b)`: the digon corner at the tail of a dart
of a step whose bit is set, or a corner of the level at the vertex where a dart of a step ends at a
vertex of the cut path. -/
def lvNewB (gate : N.G.Dart × Bool → Bool) (c : N.G.Dart × Bool) : Prop :=
  (∃ z, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ∧ gate z = true ∧ c = (z.1, false)) ∨
    (c ∈ Γ₀ ∪ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ ∧
      ∃ z, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ z ∧
        (∃ (σ : Fin 2) (t : ℕ), t ≤ Cp.m ∧
          Cp.cut.tail (N.toRot.dual.double.rev z) = Cp.cut.tail (Cp.k σ t)) ∧
        (N.toRot.dual.double.split (Γ₀ ∪ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ)).tail c =
          (N.toRot.dual.double.split (Γ₀ ∪ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).steps ℓ)).tail
            (N.toRot.dual.double.rev z))

variable
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

omit hpick in
/-- Two subruns of a level whose components share a dart are equal. -/
theorem lv_same {s s' : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ)
    (hs' : s' ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ) {y : N.G.Dart × Bool}
    (hy : (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) y)
    (hy' : (N.toRot.dual.double.split s'.1.1).toHypermap.gcomp (s'.1.2.κ0 s'.1.2.xa) y) : s = s' := by
  have hn : ∀ {s : CutPath.Sub Cp hR hC hgc}, s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ →
      s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := fun h => by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem h
  exact (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs_eq_of_fst ℓ hs hs'
    ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).sep ℓ s.1 (hn hs) s'.1 (hn hs') y hy hy')

/-- The darts of the step of a subrun of a level, with the data of its chain. -/
theorem lv_darts {s : CutPath.Sub Cp hR hC hgc} {kk i1 i2 kk' i1' i2' : ℕ} {S S' : s.1.2.Step}
    (hd : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2)
    (ht : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk, S.darts))
    (hd' : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk' i1' i2')
    (ht' : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk', S'.darts))
    {z : N.G.Dart × Bool} (hz : z ∈ S'.darts) : ∃ i, i < S.n ∧ z = S.q i := by
  obtain ⟨-, -, -, hS⟩ := lv_unique hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht'
  rw [← hS] at hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
  exact ⟨i, List.mem_range.1 hi, rfl⟩

variable (gate : N.G.Dart × Bool → Bool)

open Classical in
/-- **The new corners of the side of `κ0(x_a)` from the darts of the steps.** Let the bit `gate z`
tell, for a dart `z` in the component of an annulus of level `ℓ`, whether the child of the annulus on
the side of `κ0(x_b)` exists. For an annulus with that child, a corner in its component passes the
local test `lvNewA` exactly when it is a new corner of the side of `κ0(x_a)` of the step. -/
theorem lvNewA_iff
    (h_gate : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
      ∀ z, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) z →
        (gate z = true ↔
          (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2 = false ∧
            i2 + 2 ≤ s.2.1.2))
    {s : CutPath.Sub Cp hR hC hgc} (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ)
    (hjk : s.2.1.1 + 2 ≤ s.2.1.2) {kk i1 i2 : ℕ} {S : s.1.2.Step}
    (hd : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2)
    (ht : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk, S.darts))
    (hb : (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).2 = false)
    (hi2 : i2 + 2 ≤ s.2.1.2) {c : N.G.Dart × Bool}
    (hreg : (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c) :
    lvNewA hN modeL hostT hhost hE K D M r₀ ℓ gate c ↔ s.1.2.newA S c := by
  have hsn : s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  constructor
  · rintro (⟨z, ⟨s', hs', hjk', kk', i1', i2', S', hd', ht', hz⟩, hgz, rfl⟩ |
      ⟨hcΓ, z, ⟨s', hs', hjk', kk', i1', i2', S', hd', ht', hz⟩, ⟨σ, t, htm, hcut⟩, htl⟩)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      have hi := List.mem_range.1 hi
      obtain ⟨hb', hi2'⟩ := (h_gate s' hs' hjk' kk' i1' i2' hd' _ (S'.gcomp_q hi).1).1 hgz
      have hnew : s'.1.2.newA S' (N.toRot.dual.rev (S'.q i).1, false) := Or.inr ⟨i, hi, rfl⟩
      have hreg' := region_of_kidA hN modeL hostT hhost hE K D M r₀ ℓ hpick hs' hjk' hd' ht' true
        (c := (N.toRot.dual.rev (S'.q i).1, false)) (by
          unfold kidA; rw [hb', decide_eq_true hi2', decide_eq_true hnew]; simp)
      obtain rfl := lv_same hN modeL hostT hhost hE K D M r₀ ℓ hs hs' hreg hreg'
      exact (CutPath.Live.newA_congr
        (lv_unique hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht').2.2.2 _).2 hnew
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      have hi := List.mem_range.1 hi
      have hcz : fconnect (N.toRot.dual.double.split s.1.1).rot c (S'.q i) :=
        ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).fconnect_level_iff ℓ hsn hreg).1 (((N.toRot.dual.double.split _).tail_eq_iff _ _).1 htl)
      have hreg' : (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) (S'.q i) :=
        connect_trans hreg ((N.toRot.dual.double.split s.1.1).toHypermap.gcomp_of_cnode hcz)
      obtain rfl := lv_same hN modeL hostT hhost hE K D M r₀ ℓ hs hs' hreg' (S'.gcomp_q hi).1
      obtain ⟨i', hi', e⟩ := lv_darts hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht'
        (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      rw [e] at hcut hcz
      obtain rfl := S.first_of_cut hi' htm hcut
      refine Or.inl (N.toRot.dual.double.eq_of_fconnect_split ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_of_level ℓ hsn hcΓ hreg)
        (s.1.2.bound.sub _ (s.1.2.κ0_mem S.hxa S.hxb)) (connect_trans hcz S.start))
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · refine Or.inr ⟨(lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subset_level ℓ hsn (s.1.2.bound.sub _ (s.1.2.κ0_mem S.hxa S.hxb)), S.q 0,
        ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, List.mem_map.2 ⟨0, List.mem_range.2 S.pos, rfl⟩⟩,
        ⟨0, S.x, S.hxb.trans s.1.2.xb_le, S.cut_first⟩, ?_⟩
      exact ((N.toRot.dual.double.split _).tail_eq_iff _ _).2
        (((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).fconnect_level_iff ℓ hsn (s.1.2.gcomp_κ0 S.hxa S.hxb)).2 (fconnect_symm S.start))
    · exact Or.inl ⟨S.q i, ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩,
        (h_gate s hs hjk kk i1 i2 hd _ (S.gcomp_q hi).1).2 ⟨hb, hi2⟩, rfl⟩

open Classical in
/-- **The new corners of the side of `κ0(x_b)` from the darts of the steps**, as `lvNewA_iff` for the
child on the side of `κ0(x_a)`. -/
theorem lvNewB_iff
    (h_gate : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
      ∀ z, (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) z →
        (gate z = true ↔
          (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1 = false ∧
            s.2.1.1 + 2 ≤ i1))
    {s : CutPath.Sub Cp hR hC hgc} (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ)
    (hjk : s.2.1.1 + 2 ≤ s.2.1.2) {kk i1 i2 : ℕ} {S : s.1.2.Step}
    (hd : lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2)
    (ht : (CutPath.pickF hR hC hgc (lvPof hN modeL hostT hhost hE K D M ℓ
        (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ)) s.2.2).top =
      some (lvWalk hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk, S.darts))
    (hb : (lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk).1 = false)
    (hi1 : s.2.1.1 + 2 ≤ i1) {c : N.G.Dart × Bool}
    (hreg : (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c) :
    lvNewB hN modeL hostT hhost hE K D M r₀ ℓ gate c ↔ s.1.2.newB S c := by
  have hsn : s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  constructor
  · rintro (⟨z, ⟨s', hs', hjk', kk', i1', i2', S', hd', ht', hz⟩, hgz, rfl⟩ |
      ⟨hcΓ, z, ⟨s', hs', hjk', kk', i1', i2', S', hd', ht', hz⟩, ⟨σ, t, htm, hcut⟩, htl⟩)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      have hi := List.mem_range.1 hi
      obtain ⟨hb', hi1'⟩ := (h_gate s' hs' hjk' kk' i1' i2' hd' _ (S'.gcomp_q hi).1).1 hgz
      have hnew : s'.1.2.newB S' ((S'.q i).1, false) := Or.inr ⟨i, hi, rfl⟩
      have hreg' := region_of_kidA hN modeL hostT hhost hE K D M r₀ ℓ hpick hs' hjk' hd' ht' false
        (c := ((S'.q i).1, false)) (by
          unfold kidB; rw [hb', decide_eq_true hi1', decide_eq_true hnew]; simp)
      obtain rfl := lv_same hN modeL hostT hhost hE K D M r₀ ℓ hs hs' hreg hreg'
      exact (CutPath.Live.newB_congr
        (lv_unique hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht').2.2.2 _).2 hnew
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      have hi := List.mem_range.1 hi
      have hcz : fconnect (N.toRot.dual.double.split s.1.1).rot c (N.toRot.dual.double.rev (S'.q i)) :=
        ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).fconnect_level_iff ℓ hsn hreg).1 (((N.toRot.dual.double.split _).tail_eq_iff _ _).1 htl)
      have hreg' : (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa)
          (N.toRot.dual.double.rev (S'.q i)) :=
        connect_trans hreg ((N.toRot.dual.double.split s.1.1).toHypermap.gcomp_of_cnode hcz)
      obtain rfl := lv_same hN modeL hostT hhost hE K D M r₀ ℓ hs hs' hreg' (S'.gcomp_q hi).2
      obtain ⟨i', hi', e⟩ := lv_darts hN modeL hostT hhost hE K D M r₀ ℓ hpick hd ht hd' ht'
        (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      rw [e] at hcut hcz
      obtain rfl := S.last_of_cut hi' htm hcut
      refine Or.inl (N.toRot.dual.double.eq_of_fconnect_split ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_of_level ℓ hsn hcΓ hreg)
        (s.1.2.bound.sub _ (s.1.2.κ1_mem S.hya S.hyb)) (connect_trans hcz S.stop))
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · refine Or.inr ⟨(lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subset_level ℓ hsn (s.1.2.bound.sub _ (s.1.2.κ1_mem S.hya S.hyb)),
        S.q (S.n - 1), ⟨s, hs, hjk, kk, i1, i2, S, hd, ht,
          List.mem_map.2 ⟨S.n - 1, List.mem_range.2 (by have := S.pos; omega), rfl⟩⟩,
        ⟨1, S.y, S.hyb.trans s.1.2.yb_le, S.cut_last⟩, ?_⟩
      exact ((N.toRot.dual.double.split _).tail_eq_iff _ _).2
        (((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).fconnect_level_iff ℓ hsn (s.1.2.gcomp_κ1 S.hya S.hyb)).2 (fconnect_symm S.stop))
    · exact Or.inl ⟨S.q i, ⟨s, hs, hjk, kk, i1, i2, S, hd, ht, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩,
        (h_gate s hs hjk kk i1 i2 hd _ (S.gcomp_q hi).1).2 ⟨hb, hi1⟩, rfl⟩

end RData

end RotSystem

end SsspFlow
