import SsspFlow.RunKids

/-!
# The corners of the sides of the subruns below a node

The step of a node starts at `κ0(x)` and ends at `κ1(y)`, so `x` and `y` are the indices of the path
vertices at the tail of its first dart and at the head of its last dart. The side of `κ1(y)` of the
cut along the step keeps the corners `κ0(x_a)`, `L_a`, `κ1(y_a)` of the side of `κ0(x_a)` and gets the
tail corners `((q j).1, false)` of the darts of the step and `κ1(y)` as the corners of its other side.
The side of `κ0(x)` keeps the corners of the side of `κ0(x_b)` and gets `κ0(x)` and the head corners
`(rev (q j).1, false)` of the darts of the step. So whether a corner is a corner of a side of an
annulus with a range of length at least `2` at the next depth is a test on the range, the two indices,
the two overlap bits and two bits of the corner.

* `CutPath.Live.Step.tail_first`, `CutPath.Live.Step.tail_last`: the ends of a step on the path.
* `CutPath.Live.lo_cornerA`, `lo_cornerB`, `hi_cornerA`, `hi_cornerB`: the corners of the sides of
  the two sides of the cut along a step.
* `RotSystem.kidA`, `RotSystem.kidB`: the tests of a corner.
* `CutPath.pickF_corners`: below a picked node, the corners of the sides of the subruns with a range
  of length at least `2` are those that pass the tests.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

/-- **The test of a corner of the side of `κ0(x_a)`** below a node with range `[j, k]`, indices `i1`,
`i2` and overlap bits `bA`, `bB`: a corner of that side of the node below the side of `κ0(x_a)`, or a
new corner of the side of `κ0(x_b)` below that side. -/
def kidA (j k i1 i2 : ℕ) (bA bB oldA newA : Bool) : Bool :=
  (!bA && decide (j + 2 ≤ i1) && oldA) || (!bB && decide (i2 + 2 ≤ k) && newA)

/-- **The test of a corner of the side of `κ0(x_b)`** below a node. -/
def kidB (j k i1 i2 : ℕ) (bA bB newB oldB : Bool) : Bool :=
  (!bA && decide (j + 2 ≤ i1) && newB) || (!bB && decide (i2 + 2 ≤ k) && oldB)

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace WalkCut

variable {Γ : Finset (D × Bool)} (W : R.WalkCut Γ)

/-- The first corner of `r_n, …, r_1` is `r_n`. -/
theorem mem_rs_iff' {c : D × Bool} : c ∈ W.rs ↔ c = W.rc (W.n - 1) ∨ c ∈ W.rs.tail := by
  have hne : W.rs ≠ [] := by
    simp only [rs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    exact W.pos.ne'
  have hh : W.rs.head hne = W.rc (W.n - 1) := by
    rw [List.head_eq_getElem]
    simp only [rs, List.getElem_map, List.getElem_range, Nat.sub_zero]
    obtain ⟨n', hn⟩ : ∃ n', W.n = n' + 1 := ⟨W.n - 1, by have := W.pos; omega⟩
    rw [hn]
    rfl
  conv_lhs => rw [← List.cons_head_tail hne, hh]
  exact List.mem_cons

end WalkCut

namespace CutPath

variable {C : R.CutPath}

namespace Live

variable {g : D → ℝ≥0∞} {Γ : Finset (D × Bool)} {L : C.Live g Γ}

/-- The tail of the first dart of a step is the vertex `p_x` of the path. -/
theorem Step.tail_first (S : L.Step) : R.tail (S.q 0).1 = C.v S.x :=
  (DiskChord.tail_fst S.start).trans (L.tail_κ0 S.hxa S.hxb)

/-- The head of the last dart of a step is the vertex `p_y` of the path. -/
theorem Step.tail_last (S : L.Step) : R.tail (R.rev (S.q (S.n - 1)).1) = C.v S.y :=
  (DiskChord.tail_fst S.stop).trans (L.tail_κ1 S.hya S.hyb)

variable (L)

/-- The new corners of the side of `κ0(x_a)` of the side of `κ0(x)`: `κ0(x)` and the head corners of
the darts of the step. -/
def newA (S : L.Step) (c : D × Bool) : Prop :=
  c = L.κ0 S.x ∨ ∃ i, i < S.n ∧ c = (R.rev (S.q i).1, false)

/-- The new corners of the side of `κ0(x_b)` of the side of `κ1(y)`: `κ1(y)` and the tail corners of
the darts of the step. -/
def newB (S : L.Step) (c : D × Bool) : Prop :=
  c = L.κ1 S.y ∨ ∃ i, i < S.n ∧ c = ((S.q i).1, false)

variable (hR : R.Planar) (hC : R.Connected) (S : L.Step) (hg : ∀ x, g (R.rev x) = g x)

section Lo

variable (noA : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.La, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
  (hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ)

/-- **The side of `κ0(x_a)` of the side of `κ1(y)`** has the corners of the side of `κ0(x_a)`. -/
theorem lo_cornerA (h : S.x ≠ L.xa) (c : D × Bool) :
    (L.lo hR hC S noA hdeg hg).CornerA c ↔ L.CornerA c := by
  have e : L.loκ0 hR hC S noA hdeg L.xa = L.κ0 L.xa := by
    unfold loκ0
    exact ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h))
  show c = L.loκ0 hR hC S noA hdeg L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya ↔ _
  rw [e]
  rfl

/-- **The side of `κ0(x_b)` of the side of `κ1(y)`** has the new corners `κ1(y)` and the tail corners of
the darts of the step. -/
theorem lo_cornerB (c : D × Bool) : (L.lo hR hC S noA hdeg hg).CornerB c ↔ L.newB S c := by
  have e : L.loκ0 hR hC S noA hdeg S.x = (L.loCut hR hC S noA hdeg).rc (S.n - 1) := by
    unfold loκ0
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  show c = L.loκ0 hR hC S noA hdeg S.x ∨ c ∈ (L.loCut hR hC S noA hdeg).rs.tail ∨ c = L.κ1 S.y ↔ _
  have hm := (L.loCut hR hC S noA hdeg).mem_rs_iff' (c := c)
  rw [loCut_n] at hm
  rw [e, ← or_assoc, ← hm, WalkCut.mem_rs, newB, or_comm]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨m, hm', rfl⟩
    refine ⟨S.n - 1 - m, by have : m < S.n := hm'; omega, ?_⟩
    show (R.rev (R.rev (S.q (S.n - 1 - m)).1), false) = _
    rw [R.rev_rev]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨S.n - 1 - i, by simp; omega, ?_⟩
    show _ = (R.rev (R.rev (S.q (S.n - 1 - (S.n - 1 - i))).1), false)
    rw [R.rev_rev, show S.n - 1 - (S.n - 1 - i) = i by omega]

end Lo

section Hi

variable (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
  (hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ)

/-- **The side of `κ0(x_a)` of the side of `κ0(x)`** has the new corners `κ0(x)` and the head corners of
the darts of the step. -/
theorem hi_cornerA (c : D × Bool) : (L.hi hR hC S noB hdeg hg).CornerA c ↔ L.newA S c := by
  have e : L.hiκ1 hR hC S noB hdeg S.y = (L.hiCut hR hC S noB hdeg).rc (S.n - 1) := by
    unfold hiκ1
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  show c = L.κ0 S.x ∨ c ∈ (L.hiCut hR hC S noB hdeg).rs.tail ∨ c = L.hiκ1 hR hC S noB hdeg S.y ↔ _
  have hm := (L.hiCut hR hC S noB hdeg).mem_rs_iff' (c := c)
  rw [hiCut_n] at hm
  rw [e, or_comm (a := c ∈ _), ← hm, WalkCut.mem_rs, newA]
  rfl

/-- **The side of `κ0(x_b)` of the side of `κ0(x)`** has the corners of the side of `κ0(x_b)`. -/
theorem hi_cornerB (h : S.y ≠ L.yb) (c : D × Bool) :
    (L.hi hR hC S noB hdeg hg).CornerB c ↔ L.CornerB c := by
  have e : L.hiκ1 hR hC S noB hdeg L.yb = L.κ1 L.yb := by
    unfold hiκ1
    exact ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h))
  show c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.hiκ1 hR hC S noB hdeg L.yb ↔ _
  rw [e]
  rfl

end Hi

end Live

section Pick

variable {g₀ : D → ℕ} (hR : R.Planar) (hC : R.Connected)
  (hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x)

namespace Live

variable {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ) {j k : ℕ} (hjk : j + 2 ≤ k)
  (hxa : L.xa ≤ j) (hya : L.ya ≤ j) (hxb : k ≤ L.xb) (hyb : k ≤ L.yb)
  {q : List (D × Bool)} (hq : L.Shortest ((j + k) / 2) q) {i1 i2 : ℕ}
  (hI1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1) (hI2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2)
  (S : L.Step) (hsub : ∃ p₁ p₃, q = p₁ ++ (List.range S.n).map S.q ++ p₃)

open Classical in
/-- **The corners of the sides below a node with given data.** -/
theorem pickNode_corners (c : D × Bool) :
    ((∃ s ∈ (L.pickNode hR hC hgc hjk hxa hya hxb hyb hq hI1 hI2 S hsub).subs 1,
        s.2.1.1 + 2 ≤ s.2.1.2 ∧ s.1.2.CornerA c) ↔
      kidA j k i1 i2 (decide (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c))
        (decide (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c)) (decide (L.CornerA c))
        (decide (L.newA S c)) = true) ∧
    ((∃ s ∈ (L.pickNode hR hC hgc hjk hxa hya hxb hyb hq hI1 hI2 S hsub).subs 1,
        s.2.1.1 + 2 ≤ s.2.1.2 ∧ s.1.2.CornerB c) ↔
      kidB j k i1 i2 (decide (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c))
        (decide (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c)) (decide (L.newB S c))
        (decide (L.CornerB c)) = true) := by
  have hf := L.pick_facts hjk hxa hxb hq hI1 hI2 S hsub
  have vy : L.Visits ((j + k) / 2) q (L.κ1 S.y) :=
    Or.inr ⟨S.q (S.n - 1), hf.1 _ (by have := S.pos; omega),
      ((R.double.split Γ).tail_eq_iff _ _).2 S.stop⟩
  have hex : ∀ (l₁ l₂ : List (Sub C hR hC hgc)) (P : Sub C hR hC hgc → Prop),
      (∃ x ∈ l₁ ++ l₂, P x) ↔ (∃ x ∈ l₁, P x) ∨ ∃ x ∈ l₂, P x := fun l₁ l₂ P => by
    simp only [List.mem_append, or_and_right, exists_or]
  have eA : ∀ x : {s : SideA hR hC hgc Γ L q ((j + k) / 2) S j i1 // s.IsOverlap hR hC hgc},
      x.1.subs 0 = [] := fun x => SideA.subs_of_isOverlap hR hC hgc x.2 0
  have eB : ∀ x : {s : SideB hR hC hgc Γ L q ((j + k) / 2) S i2 k // s.IsOverlap hR hC hgc},
      x.1.subs 0 = [] := fun x => SideB.subs_of_isOverlap hR hC hgc x.2 0
  have loA : ∀ noA hdeg, ¬ (∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧
      L.Visits ((j + k) / 2) q c) → ∀ c, (L.lo hR hC S noA hdeg hgc).CornerA c ↔ L.CornerA c :=
    fun noA hdeg hA c => L.lo_cornerA hR hC S hgc noA hdeg (fun e => hA ⟨_, Or.inl rfl, e ▸ hf.2.1⟩) c
  have hiB : ∀ noB hdeg, ¬ (∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧
      L.Visits ((j + k) / 2) q c) → ∀ c, (L.hi hR hC S noB hdeg hgc).CornerB c ↔ L.CornerB c :=
    fun noB hdeg hB c => L.hi_cornerB hR hC S hgc noB hdeg
      (fun e => hB ⟨_, Or.inr (Or.inr rfl), e ▸ vy⟩) c
  have dA : decide (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c) =
      decide (∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧ L.Visits ((j + k) / 2) q c) :=
    decide_eq_decide.2 Iff.rfl
  have dB : decide (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c) =
      decide (∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧ L.Visits ((j + k) / 2) q c) :=
    decide_eq_decide.2 Iff.rfl
  have a1 : ¬ j ≤ i1 → ¬ j + 2 ≤ i1 := fun h h' => h (by omega)
  have a2 : ¬ i2 ≤ k → ¬ i2 + 2 ≤ k := fun h h' => h (by omega)
  unfold pickNode kidA kidB
  rw [dA, dB]
  simp only [Run.subs, hex]
  by_cases hA : ∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧ L.Visits ((j + k) / 2) q c <;>
  by_cases hB : ∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧ L.Visits ((j + k) / 2) q c <;>
  by_cases hj : j ≤ i1 <;> by_cases hk : i2 ≤ k <;>
  simp only [hA, hB, hj, hk, dite_true, dite_false, decide_true, decide_false, eA, eB, SideA.subs,
    SideB.subs, Run.subs_zero, List.not_mem_nil, false_and, exists_false, List.mem_singleton,
    exists_eq_left, false_or, or_false, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_and,
    Bool.false_and, true_and, false_iff, iff_false, not_or, not_and]
  all_goals
    (try simp only [loA _ _ hA]); (try simp only [hiB _ _ hB])
    (try simp only [L.lo_cornerB hR hC S hgc]); (try simp only [L.hi_cornerA hR hC S hgc])
    (try simp only [a1 hj, a2 hk, false_and, or_false, false_or, false_implies, and_self, iff_self])
    (try simp only [a1 hj, false_and, or_false, false_or, false_implies, and_self, iff_self])
    (try simp only [a2 hk, false_and, or_false, false_or, false_implies, and_self, iff_self])
    (try exact ⟨trivial, trivial⟩)

end Live

namespace Live

variable {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ}

/-- The darts of a step at its indices are the members of its list of darts. -/
theorem Step.exists_darts (S : L.Step) (Q : D × Bool → Prop) :
    (∃ i, i < S.n ∧ Q (S.q i)) ↔ ∃ z ∈ S.darts, Q z := by
  simp only [Step.darts, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨i, hi, h⟩

/-- Two steps with the same darts have the same ends. -/
theorem Step.xy_eq_of_darts {S S' : L.Step} (h : S.darts = S'.darts) : S.x = S'.x ∧ S.y = S'.y := by
  have hn : S.n = S'.n := by simpa [Step.darts] using congrArg List.length h
  have hq : ∀ i, i < S.n → S.q i = S'.q i := fun i hi => by
    have := congrArg (fun l => l[i]?) h
    simpa [Step.darts, List.getElem?_map, List.getElem?_range, hi, hn ▸ hi] using this
  constructor
  · refine C.inj _ _ (S.hxb.trans L.xb_le) (S'.hxb.trans L.xb_le) ?_
    rw [← S.tail_first, ← S'.tail_first, hq 0 S.pos]
  · refine C.inj _ _ (S.hyb.trans L.yb_le) (S'.hyb.trans L.yb_le) ?_
    rw [← S.tail_last, ← S'.tail_last, hq _ (by have := S.pos; omega), hn]

theorem newA_congr {S S' : L.Step} (h : S.darts = S'.darts) (c : D × Bool) :
    L.newA S c ↔ L.newA S' c := by
  unfold newA
  rw [(Step.xy_eq_of_darts h).1, S.exists_darts (fun z => c = (R.rev z.1, false)),
    S'.exists_darts (fun z => c = (R.rev z.1, false)), h]

theorem newB_congr {S S' : L.Step} (h : S.darts = S'.darts) (c : D × Bool) :
    L.newB S c ↔ L.newB S' c := by
  unfold newB
  rw [(Step.xy_eq_of_darts h).2, S.exists_darts (fun z => c = (z.1, false)),
    S'.exists_darts (fun z => c = (z.1, false)), h]

end Live

variable (P : (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ → List (D × Bool) →
  List (D × Bool) → Prop)

open Classical in
/-- **The corners of the sides below a picked node.** If there are data whose walk and step darts
satisfy `P`, the picking graft gives a node with such a walk and step, least and greatest index of the
cut path on the walk, and the corners of the sides of its subruns with a range of length at least `2`
are those that pass the tests. -/
theorem pickF_corners {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k)
    (h : Nonempty {d : NodeData L j k // P ⟨Γ, L⟩ ((j + k) / 2) d.q d.S.darts}) :
    ∃ (q : List (D × Bool)) (S : L.Step) (i1 i2 : ℕ),
      (pickF hR hC hgc P r).top = some (q, S.darts) ∧ P ⟨Γ, L⟩ ((j + k) / 2) q S.darts ∧
      IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1 ∧ IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2 ∧
      ∀ c, ((∃ s ∈ (pickF hR hC hgc P r).subs 1, s.2.1.1 + 2 ≤ s.2.1.2 ∧ s.1.2.CornerA c) ↔
          kidA j k i1 i2 (decide (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c))
            (decide (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c)) (decide (L.CornerA c))
            (decide (L.newA S c)) = true) ∧
        ((∃ s ∈ (pickF hR hC hgc P r).subs 1, s.2.1.1 + 2 ≤ s.2.1.2 ∧ s.1.2.CornerB c) ↔
          kidB j k i1 i2 (decide (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c))
            (decide (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c)) (decide (L.newB S c))
            (decide (L.CornerB c)) = true) := by
  unfold pickF
  rw [dif_pos h]
  exact ⟨_, _, _, _, rfl, (Classical.choice h).2, (Classical.choice h).1.hI1, (Classical.choice h).1.hI2,
    fun c => L.pickNode_corners hR hC hgc _ _ _ _ _ _ _ _ _ _ c⟩

end Pick

end CutPath

end RotSystem

end SsspFlow
