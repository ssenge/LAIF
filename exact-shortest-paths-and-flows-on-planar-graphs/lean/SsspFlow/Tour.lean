import SsspFlow.Chord

/-!
# Tours of a spanning forest

For a rotation system `R` and a set `F` of darts closed under `rev`, the permutation
`tour F := revOn F * rot` walks around the forest `F`: from a corner it passes the next dart, and it
crosses that dart if the dart lies in `F`. If `F` is a spanning forest (`SpanForest`), the cycles of
`tour F` are the components of `R`.

The theorems say how the edges off the forest and the corners of one face lie on a cycle of the tour,
and they are all consequences of Euler's formula through the transposition lemma: the inverse of the
face permutation is the tour times one swap per edge off the forest, and there are as many faces as
the count allows only if every swap splits a cycle.

* `SpanForest.fconnect_tour_iff`: the cycles of the tour are the components.
* `SpanForest.fconnect_swap_of_erase`: the cycles of the tour of the forest minus one edge are the
  components of that forest.
* `SpanForest.fconnect_swap_of_face`, `SpanForest.fconnect_swap_rev`: two corners of one face, and
  the two darts of an edge off the forest, stay in one cycle after the swap of any edge off the forest.
* `pos`, `InArc`, `mass`: positions on a cycle, the arc `(x, y]`, and the number of marked darts in it.
* `inArc_iff_of_swap`: a pair of elements that a swap separates does not cross the arc between two
  elements that the swap keeps together.
* `SpanForest.walk_step`, `SpanForest.walk_strict`: the corners of a face appear on the tour in the
  order of the face.
* `SpanForest.exists_crossing`, `SpanForest.exists_balanced`: two corners of one face that cut the
  forest darts of a cycle in a balanced way.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

section Swaps

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- `a` is a product of `k` swaps. -/
inductive ProdSwaps : ℕ → Equiv.Perm D → Prop
  | one : ProdSwaps 0 1
  | swap (x y : D) {k : ℕ} {a : Equiv.Perm D} (h : ProdSwaps k a) :
      ProdSwaps (k + 1) (Equiv.swap x y * a)

/-- A swap raises the number of orbits by at most one. -/
theorem orb_swap_mul_le (x y : D) (g : Equiv.Perm D) : orb (Equiv.swap x y * g) ≤ orb g + 1 := by
  by_cases hxy : x = y
  · rw [hxy, Equiv.swap_self]
    exact Nat.le_succ _
  by_cases h : fconnect g x y
  · exact (orb_swap_mul_of_fconnect g hxy h).le
  · have := orb_swap_mul_of_not_fconnect g h
    omega

theorem ProdSwaps.orb_mul_le {k : ℕ} {a : Equiv.Perm D} (h : ProdSwaps k a) (g : Equiv.Perm D) :
    orb (a * g) ≤ orb g + k := by
  induction h with
  | one => rw [one_mul]; exact Nat.le_add_right _ _
  | swap x y _ ih =>
    rw [mul_assoc]
    exact (orb_swap_mul_le x y _).trans (by omega)

/-- A conjugate of a product of `k` swaps is a product of `k` swaps. -/
theorem ProdSwaps.conj {k : ℕ} {a : Equiv.Perm D} (h : ProdSwaps k a) (c : Equiv.Perm D) :
    ProdSwaps k (c * a * c⁻¹) := by
  induction h with
  | one => rw [mul_one, mul_inv_cancel]; exact ProdSwaps.one
  | @swap x y k' a' _ ih =>
    have e : c * (Equiv.swap x y * a') * c⁻¹ = Equiv.swap (c x) (c y) * (c * a' * c⁻¹) := by
      rw [Equiv.swap_apply_apply]
      simp [mul_assoc]
    rw [e]
    exact ProdSwaps.swap _ _ ih

end Swaps

/-! ### Positions on a cycle -/

section Positions

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The number of steps of `f` from `x` to `z`. -/
noncomputable def pos (f : Equiv.Perm D) (x z : D) : ℕ := sInf {k | f^[k] x = z}

/-- `z` lies in the arc `(x, y]` of the cycle of `f` through `x`. The arc is empty if `y = x`, and if
`y` is not on the cycle. -/
def InArc (f : Equiv.Perm D) (x y z : D) : Prop :=
  fconnect f x z ∧ z ≠ x ∧ pos f x z ≤ pos f x y

open Classical in
/-- The number of elements of `T` in the arc `(x, y]`. -/
noncomputable def mass (f : Equiv.Perm D) (T : Finset D) (x y : D) : ℕ :=
  (T.filter (InArc f x y)).card

open Classical in
/-- The number of elements of `T` on the cycle of `x`. -/
noncomputable def cycMass (f : Equiv.Perm D) (T : Finset D) (x : D) : ℕ :=
  (T.filter (fconnect f x)).card

variable {f : Equiv.Perm D} {x y z u : D}

theorem pos_spec (h : fconnect f x z) : f^[pos f x z] x = z :=
  Nat.sInf_mem (s := {k | f^[k] x = z}) (fconnect_iff_iterate.1 h)

theorem pos_le {k : ℕ} (h : f^[k] x = z) : pos f x z ≤ k := Nat.sInf_le h

@[simp] theorem pos_self : pos f x x = 0 := Nat.le_zero.1 (pos_le rfl)

theorem pos_of_not_fconnect (h : ¬ fconnect f x z) : pos f x z = 0 :=
  Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_of_forall_notMem fun k hk =>
    h (fconnect_iff_iterate.2 ⟨k, hk⟩)))

theorem pos_inj {z' : D} (h : fconnect f x z) (h' : fconnect f x z')
    (he : pos f x z = pos f x z') : z = z' := by
  rw [← pos_spec h, ← pos_spec h', he]

theorem pos_pos (h : fconnect f x z) (hne : z ≠ x) : 0 < pos f x z := by
  refine Nat.pos_of_ne_zero fun h0 => hne ?_
  have := pos_spec h
  rw [h0] at this
  exact this.symm

theorem fconnect_apply (h : fconnect f x z) : fconnect f x (f z) :=
  connect_trans h (fconnect1 _ _)

theorem fconnect_of_apply (h : fconnect f x (f z)) : fconnect f x z :=
  connect_trans h ((fconnect_comm f.injective).1 (fconnect1 _ _))

theorem fconnect_symm (h : fconnect f x z) : fconnect f z x := (fconnect_comm f.injective).1 h

/-- One more step, one more position, unless the cycle closes. -/
theorem pos_apply (h : fconnect f x z) (hne : f z ≠ x) : pos f x (f z) = pos f x z + 1 := by
  apply le_antisymm
  · apply pos_le
    rw [Function.iterate_succ_apply', pos_spec h]
  · have hs := pos_spec (fconnect_apply h)
    cases hk : pos f x (f z) with
    | zero =>
      rw [hk] at hs
      exact (hne hs.symm).elim
    | succ k =>
      rw [hk, Function.iterate_succ_apply'] at hs
      have := pos_le (f.injective hs)
      omega

/-- If `f y = x`, then `y` is the last element of the cycle of `x`. -/
theorem pos_le_of_last (hy : f y = x) (hxy : fconnect f x y) (z : D) :
    pos f x z ≤ pos f x y := by
  by_cases hz : fconnect f x z
  · by_contra hlt
    have e : pos f x z = (pos f x z - pos f x y - 1) + (pos f x y + 1) := by omega
    have hs := pos_spec hz
    rw [e, Function.iterate_add_apply, Function.iterate_succ_apply', pos_spec hxy, hy] at hs
    have := pos_le hs
    omega
  · rw [pos_of_not_fconnect hz]
    exact Nat.zero_le _

/-- A second start on the cycle subtracts its position. -/
theorem pos_shift (hu : fconnect f x u) (hz : fconnect f x z) (h : pos f x u ≤ pos f x z) :
    pos f u z = pos f x z - pos f x u := by
  have e : pos f x z = (pos f x z - pos f x u) + pos f x u := by omega
  apply le_antisymm
  · apply pos_le
    have hs := pos_spec hz
    rw [e, Function.iterate_add_apply, pos_spec hu] at hs
    exact hs
  · have hs := pos_spec (connect_trans (fconnect_symm hu) hz)
    have h2 : f^[pos f u z + pos f x u] x = z := by
      rw [Function.iterate_add_apply, pos_spec hu, hs]
    have := pos_le h2
    omega

/-- The cycle does not close before the position of any of its elements. -/
theorem iterate_ne_start (hz : fconnect f x z) {p : ℕ} (h0 : 0 < p) (hp : p ≤ pos f x z) :
    f^[p] x ≠ x := by
  intro he
  have e : pos f x z = (pos f x z - p) + p := by omega
  have hs := pos_spec hz
  rw [e, Function.iterate_add_apply, he] at hs
  have := pos_le hs
  omega

theorem not_inArc_start : ¬ InArc f x y x := fun h => h.2.1 rfl

theorem not_inArc_empty : ¬ InArc f x x z := fun h => by
  have := pos_pos h.1 h.2.1
  have h2 := h.2.2
  rw [pos_self] at h2
  omega

theorem inArc_end (hy : fconnect f x y) (hne : y ≠ x) : InArc f x y y := ⟨hy, hne, le_rfl⟩

theorem InArc.mono {y' : D} (h : InArc f x y z) (hle : pos f x y ≤ pos f x y') : InArc f x y' z :=
  ⟨h.1, h.2.1, h.2.2.trans hle⟩

theorem InArc.pos_lt (h : InArc f x y z) (hne : z ≠ y) : pos f x z < pos f x y := by
  by_cases hy : fconnect f x y
  · exact lt_of_le_of_ne h.2.2 fun e => hne (pos_inj h.1 hy e)
  · have := pos_pos h.1 h.2.1
    have h2 := h.2.2
    rw [pos_of_not_fconnect hy] at h2
    omega

/-- The arc grows by one element with every step. -/
theorem inArc_succ (hy : fconnect f x y) (hne : f y ≠ x) (w : D) :
    InArc f x (f y) w ↔ InArc f x y w ∨ w = f y := by
  have hp := pos_apply hy hne
  constructor
  · rintro ⟨hw, hwx, hle⟩
    by_cases h : pos f x w ≤ pos f x y
    · exact Or.inl ⟨hw, hwx, h⟩
    · exact Or.inr (pos_inj hw (fconnect_apply hy) (by omega))
  · rintro (⟨hw, hwx, hle⟩ | rfl)
    · exact ⟨hw, hwx, by omega⟩
    · exact ⟨fconnect_apply hy, hne, le_rfl⟩

/-- Away from its two ends, the arc is invariant under a step. -/
theorem inArc_apply_iff (hux : u ≠ x) (huy : u ≠ y) : InArc f x y (f u) ↔ InArc f x y u := by
  by_cases hc : fconnect f x u
  · by_cases hl : f u = x
    · refine ⟨fun h => (h.2.1 hl).elim, fun h => ?_⟩
      have h1 := h.pos_lt huy
      have h2 := pos_le_of_last hl hc y
      omega
    · have hp := pos_apply hc hl
      constructor
      · rintro ⟨_, _, hle⟩
        exact ⟨hc, hux, by omega⟩
      · intro h
        have := h.pos_lt huy
        exact ⟨fconnect_apply hc, hl, by omega⟩
  · exact ⟨fun h => (hc (fconnect_of_apply h.1)).elim, fun h => (hc h.1).elim⟩

theorem fconnect_ne_apply (hxy : fconnect f x y) (hne : x ≠ y) : f x ≠ x := fun e =>
  hne (eq_of_fconnect_of_fixed e hxy).symm

/-- The first step from `x` lies in `(x, y]` and not in `(y, x]`. -/
theorem inArc_apply_start (hxy : fconnect f x y) (hne : x ≠ y) :
    InArc f x y (f x) ∧ ¬ InArc f y x (f x) := by
  have hfx := fconnect_ne_apply hxy hne
  constructor
  · refine ⟨fconnect1 _ _, hfx, ?_⟩
    rw [pos_apply (connect_refl x) hfx, pos_self]
    have := pos_pos hxy hne.symm
    omega
  · rintro ⟨_, h2, h3⟩
    rw [pos_apply (fconnect_symm hxy) h2] at h3
    omega

/-- On the cycle, `(x, y]` is the complement of `(y, x]`. -/
theorem inArc_compl (hxy : fconnect f x y) (hne : x ≠ y) (hz : fconnect f x z) :
    InArc f x y z ↔ ¬ InArc f y x z := by
  induction hz with
  | refl => exact iff_of_false not_inArc_start (not_not.2 ⟨fconnect_symm hxy, hne, le_rfl⟩)
  | @tail b c _ hbc ih =>
    obtain rfl : f b = c := hbc
    by_cases hbx : b = x
    · rw [hbx]
      have := inArc_apply_start hxy hne
      exact iff_of_true this.1 this.2
    by_cases hby : b = y
    · rw [hby]
      have := inArc_apply_start (fconnect_symm hxy) hne.symm
      exact iff_of_false this.2 (not_not.2 this.1)
    rw [inArc_apply_iff hbx hby, inArc_apply_iff hby hbx]
    exact ih

/-- The arcs `(x, y]` and `(y, x]` split the marks of a cycle. -/
theorem mass_add_mass (T : Finset D) (hxy : fconnect f x y) (hne : x ≠ y) :
    mass f T x y + mass f T y x = cycMass f T x := by
  classical
  unfold mass cycMass
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hw, h⟩ | ⟨hw, h⟩)
      · exact ⟨hw, h.1⟩
      · exact ⟨hw, connect_trans hxy h.1⟩
    · rintro ⟨hw, hc⟩
      by_cases h : InArc f x y w
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, not_not.1 (mt (inArc_compl hxy hne hc).2 h)⟩
  · refine Finset.disjoint_left.2 fun w hw hw' => ?_
    rw [Finset.mem_filter] at hw hw'
    exact (inArc_compl hxy hne hw.2.1).1 hw.2 hw'.2

theorem cycMass_congr (T : Finset D) (h : fconnect f x y) : cycMass f T x = cycMass f T y := by
  classical
  unfold cycMass
  congr 1
  ext w
  simp only [Finset.mem_filter, and_congr_right_iff]
  exact fun _ => ⟨connect_trans (fconnect_symm h), connect_trans h⟩

theorem mass_mono {T : Finset D} {x' y' : D} (h : ∀ w ∈ T, InArc f x y w → InArc f x' y' w) :
    mass f T x y ≤ mass f T x' y' := by
  classical
  unfold mass
  refine Finset.card_le_card fun w hw => ?_
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, h w hw.1 hw.2⟩

@[simp] theorem mass_self (T : Finset D) : mass f T x x = 0 := by
  classical
  unfold mass
  rw [Finset.card_eq_zero]
  exact Finset.filter_eq_empty_iff.2 fun _ _ => not_inArc_empty

/-- One step adds at most one mark. -/
theorem mass_succ_le (T : Finset D) (hy : fconnect f x y) (hne : f y ≠ x) :
    mass f T x (f y) ≤ mass f T x y + 1 := by
  classical
  unfold mass
  refine (Finset.card_le_card (t := insert (f y) (T.filter (InArc f x y))) fun w hw => ?_).trans
    (Finset.card_insert_le _ _)
  rw [Finset.mem_filter] at hw
  rw [Finset.mem_insert, Finset.mem_filter]
  rcases (inArc_succ hy hne w).1 hw.2 with h | h
  · exact Or.inr ⟨hw.1, h⟩
  · exact Or.inl h

/-- A step to an element without a mark adds no mark. -/
theorem mass_succ_of_not_mem {T : Finset D} (hy : fconnect f x y) (hne : f y ≠ x) (hT : f y ∉ T) :
    mass f T x (f y) = mass f T x y := by
  apply le_antisymm
  · refine mass_mono fun w hw h => ?_
    rcases (inArc_succ hy hne w).1 h with h | h
    · exact h
    · exact (hT (h ▸ hw)).elim
  · exact mass_mono fun w _ h => (inArc_succ hy hne w).2 (Or.inl h)

/-- The cycle has at most one mark outside `(x, y]` if `f y = x`. -/
theorem cycMass_le_of_last (T : Finset D) (hy : f y = x) (hxy : fconnect f x y) :
    cycMass f T x ≤ mass f T x y + 1 := by
  classical
  unfold mass cycMass
  refine (Finset.card_le_card (t := insert x (T.filter (InArc f x y))) fun w hw => ?_).trans
    (Finset.card_insert_le _ _)
  rw [Finset.mem_filter] at hw
  rw [Finset.mem_insert, Finset.mem_filter]
  by_cases hwx : w = x
  · exact Or.inl hwx
  · exact Or.inr ⟨hw.1, hw.2, hwx, pos_le_of_last hy hxy w⟩

/-- An arc that starts inside `(x, y]` lies in `(x, y]`. -/
theorem InArc.of_shift (hu : fconnect f x u) (hux : u ≠ x) (hy : fconnect f x y)
    (hle : pos f x u ≤ pos f x y) (h : InArc f u y z) : InArc f x y z := by
  have hk := pos_shift hu hy hle
  have hz : f^[pos f u z + pos f x u] x = z := by
    rw [Function.iterate_add_apply, pos_spec hu, pos_spec h.1]
  have h2 := h.2.2
  have h0 := pos_pos hu hux
  refine ⟨connect_trans hu h.1, fun e => ?_, ?_⟩
  · rw [e] at hz h2
    exact iterate_ne_start hy (by omega) (by omega) hz
  · have := pos_le hz
    omega

/-- A jump across an element without a mark: the marks of `(x, r]` are those of `(x, z]` and those of
`(f z, r]`. -/
theorem mass_jump {T : Finset D} {r : D} (hz : fconnect f x z) (hne : f z ≠ x) (hT : f z ∉ T)
    (hr : fconnect f x r) (hle : pos f x (f z) ≤ pos f x r) :
    mass f T x r ≤ mass f T x z + mass f T (f z) r := by
  classical
  unfold mass
  refine (Finset.card_le_card fun w hw => ?_).trans (Finset.card_union_le _ _)
  rw [Finset.mem_filter] at hw
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  obtain ⟨hwT, hw1, hw2, hw3⟩ := hw
  have hp := pos_apply hz hne
  by_cases h1 : pos f x w ≤ pos f x z
  · exact Or.inl ⟨hwT, hw1, hw2, h1⟩
  · have hwz : w ≠ f z := fun e => hT (e ▸ hwT)
    have hc := fconnect_apply hz
    have hne' : pos f x w ≠ pos f x (f z) := fun e => hwz (pos_inj hw1 hc e)
    refine Or.inr ⟨hwT, connect_trans (fconnect_symm hc) hw1, hwz, ?_⟩
    rw [pos_shift hc hw1 (by omega), pos_shift hc hr hle]
    omega

/-- **Non-crossing.** If `a` and `b` lie on one cycle of `f`, and `x` and `y` lie on one cycle after
the swap of `a` and `b`, then the arc `(x, y]` contains both of `a` and `b` or neither. -/
theorem inArc_iff_of_swap {a b : D} (hab : fconnect f a b)
    (hxy : fconnect (⇑(Equiv.swap a b * f)) x y) : InArc f x y a ↔ InArc f x y b := by
  have jump : ∀ {a b y : D}, fconnect f a b → fconnect f x y → f y = a →
      (InArc f x y a ↔ InArc f x y b) → (InArc f x b a ↔ InArc f x b b) := by
    intro a b y hab hc hy hQ
    by_cases hbx : b = x
    · rw [hbx]
      exact iff_of_false not_inArc_empty not_inArc_empty
    have hca : fconnect f x a := hy ▸ fconnect_apply hc
    have hxb : fconnect f x b := connect_trans hca hab
    by_cases hax : a = x
    · have h1 : InArc f x y b := ⟨hxb, hbx, pos_le_of_last (hy.trans hax) hc b⟩
      exact ((hQ.2 h1).2.1 hax).elim
    · have hp : pos f x a = pos f x y + 1 := by
        rw [← hy]
        exact pos_apply hc (hy ▸ hax)
      have hna : ¬ InArc f x y a := fun h => by
        have := h.2.2
        omega
      have hlt : pos f x y < pos f x b := by
        by_contra hle
        exact hna (hQ.2 ⟨hxb, hbx, by omega⟩)
      exact iff_of_true ⟨hca, hax, by omega⟩ (inArc_end hxb hbx)
  have main : fconnect f x y ∧ (InArc f x y a ↔ InArc f x y b) := by
    induction hxy with
    | refl => exact ⟨connect_refl x, iff_of_false not_inArc_empty not_inArc_empty⟩
    | @tail y c _ hyc ih =>
      obtain rfl : (Equiv.swap a b * f) y = c := hyc
      obtain ⟨hc, hQ⟩ := ih
      rw [Equiv.Perm.mul_apply]
      by_cases h1 : f y = a
      · rw [h1, Equiv.swap_apply_left]
        exact ⟨connect_trans (h1 ▸ fconnect_apply hc) hab, jump hab hc h1 hQ⟩
      by_cases h2 : f y = b
      · rw [h2, Equiv.swap_apply_right]
        refine ⟨connect_trans (h2 ▸ fconnect_apply hc) (fconnect_symm hab), ?_⟩
        exact (jump (fconnect_symm hab) hc h2 hQ.symm).symm
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      refine ⟨fconnect_apply hc, ?_⟩
      by_cases hl : f y = x
      · rw [hl]
        exact iff_of_false not_inArc_empty not_inArc_empty
      rw [inArc_succ hc hl, inArc_succ hc hl]
      have ha : a ≠ f y := fun e => h1 e.symm
      have hb : b ≠ f y := fun e => h2 e.symm
      simpa [ha, hb] using hQ
  exact main.2

end Positions

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-! ### The involution of a set of darts -/

/-- `rev` on the darts of `F` whose reverse lies in `F`, and the identity elsewhere. -/
def revOn (F : Finset D) : Equiv.Perm D :=
  Function.Involutive.toPerm (fun z => if z ∈ F ∧ R.rev z ∈ F then R.rev z else z) (by
    intro z
    by_cases h : z ∈ F ∧ R.rev z ∈ F
    · have h' : R.rev z ∈ F ∧ R.rev (R.rev z) ∈ F := ⟨h.2, by rw [R.rev_rev]; exact h.1⟩
      beta_reduce
      rw [ite_eq_left h, ite_eq_left h', R.rev_rev]
    · beta_reduce
      rw [ite_eq_right h, ite_eq_right h])

variable {R}

theorem revOn_of_mem {F : Finset D} (hF : R.RevClosed F) {z : D} (hz : z ∈ F) :
    R.revOn F z = R.rev z :=
  ite_eq_left ⟨hz, hF z hz⟩

theorem revOn_of_not_mem {F : Finset D} {z : D} (hz : z ∉ F) : R.revOn F z = z :=
  ite_eq_right fun h => hz h.1

variable (R)

theorem revOn_empty : R.revOn ∅ = 1 := Equiv.ext fun _ => revOn_of_not_mem (by simp)

theorem revOn_inv (F : Finset D) : (R.revOn F)⁻¹ = R.revOn F := by
  rw [inv_eq_iff_mul_eq_one]
  exact Equiv.ext fun z => Function.Involutive.toPerm_involutive _ z

variable {R}

theorem revClosed_erase {F : Finset D} (hF : R.RevClosed F) (z : D) :
    R.RevClosed ((F.erase z).erase (R.rev z)) := by
  intro w hw
  simp only [Finset.mem_erase] at hw ⊢
  refine ⟨fun e => hw.2.1 (R.rev_injective e), fun e => hw.1 ?_, hF w hw.2.2⟩
  rw [← e, R.rev_rev]

theorem revClosed_compl {F : Finset D} (hF : R.RevClosed F) : R.RevClosed Fᶜ := by
  intro w hw
  simp only [Finset.mem_compl] at hw ⊢
  exact fun h => hw (by simpa [R.rev_rev] using hF _ h)

theorem card_erase_rev {F : Finset D} {z : D} (hz : z ∈ F) (hF : R.RevClosed F) :
    ((F.erase z).erase (R.rev z)).card + 2 = F.card := by
  have h1 : R.rev z ∈ F.erase z := Finset.mem_erase.2 ⟨R.rev_ne z, hF z hz⟩
  have h2 := Finset.card_erase_add_one h1
  have h3 := Finset.card_erase_add_one hz
  omega

/-- Taking one edge out of the set takes one swap out of the involution. -/
theorem revOn_eq_swap_mul {F : Finset D} (hF : R.RevClosed F) {z : D} (hz : z ∈ F) :
    R.revOn F = Equiv.swap z (R.rev z) * R.revOn ((F.erase z).erase (R.rev z)) := by
  have hF' := revClosed_erase hF z
  set B := (F.erase z).erase (R.rev z) with hB
  have hzB : z ∉ B := by simp [hB]
  have hrB : R.rev z ∉ B := by simp [hB]
  refine Equiv.ext fun w => ?_
  rw [Equiv.Perm.mul_apply]
  by_cases hwz : w = z
  · rw [hwz, revOn_of_not_mem hzB, Equiv.swap_apply_left, revOn_of_mem hF hz]
  by_cases hwr : w = R.rev z
  · rw [hwr, revOn_of_not_mem hrB, Equiv.swap_apply_right, revOn_of_mem hF (hF z hz), R.rev_rev]
  by_cases hw : w ∈ F
  · have hw' : w ∈ B := by simp [hB, hw, hwz, hwr]
    rw [revOn_of_mem hF' hw', revOn_of_mem hF hw, Equiv.swap_apply_of_ne_of_ne]
    · exact fun e => hwr (by rw [← e, R.rev_rev])
    · exact fun e => hwz (R.rev_injective e)
  · have hw' : w ∉ B := by simp [hB, hw]
    rw [revOn_of_not_mem hw', revOn_of_not_mem hw, Equiv.swap_apply_of_ne_of_ne hwz hwr]

/-- The swap of an edge commutes with the involution of the rest. -/
theorem revOn_eq_mul_swap {F : Finset D} (hF : R.RevClosed F) {z : D} (hz : z ∈ F) :
    R.revOn F = R.revOn ((F.erase z).erase (R.rev z)) * Equiv.swap z (R.rev z) := by
  have h := congrArg (·⁻¹) (revOn_eq_swap_mul hF hz)
  simpa only [revOn_inv, mul_inv_rev, Equiv.swap_inv] using h

/-- The involution of a closed set is a product of half as many swaps as it has darts, the set has an
even number of darts, and the involution has one orbit less per swap. -/
theorem revOn_data {F : Finset D} (hF : R.RevClosed F) :
    ProdSwaps (F.card / 2) (R.revOn F) ∧ 2 * (F.card / 2) = F.card ∧
      orb (R.revOn F) + F.card / 2 = Fintype.card D := by
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    rcases F.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · subst hn
      simp only [Finset.card_empty, Nat.zero_div, mul_zero, add_zero, true_and, revOn_empty, orb_one]
      exact ⟨ProdSwaps.one, trivial⟩
    · have hc := card_erase_rev hz hF
      obtain ⟨h1, h2, h3⟩ := ih _ (by omega) (revClosed_erase hF z) rfl
      have hd : n / 2 = ((F.erase z).erase (R.rev z)).card / 2 + 1 := by omega
      rw [hd, revOn_eq_swap_mul hF hz]
      refine ⟨ProdSwaps.swap _ _ h1, by omega, ?_⟩
      have hfix : R.revOn ((F.erase z).erase (R.rev z)) z = z := revOn_of_not_mem (by simp)
      have hnc : ¬ fconnect (R.revOn ((F.erase z).erase (R.rev z))) z (R.rev z) := fun h =>
        R.rev_ne z (eq_of_fconnect_of_fixed hfix h)
      have := orb_swap_mul_of_not_fconnect _ hnc
      omega

variable (R)

/-! ### The tour -/

/-- The tour of `F`: from a corner to the next dart, across that dart if it lies in `F`. -/
def tour (F : Finset D) : Equiv.Perm D := R.revOn F * R.rot

/-- The hypermap whose vertices are those of `R`, whose edges are the edges in `F`, and whose faces
are the cycles of the tour. -/
def tourMap (F : Finset D) : Hypermap D := permMap R.rot (R.rot⁻¹ * R.revOn F)

theorem tour_apply (F : Finset D) (z : D) : R.tour F z = R.revOn F (R.rot z) := rfl

theorem face_inv_apply (z : D) : R.facePerm⁻¹ z = R.rev (R.rot z) := rfl

variable {R}

theorem tour_of_mem {F : Finset D} (hF : R.RevClosed F) {z : D} (h : R.rot z ∈ F) :
    R.tour F z = R.rev (R.rot z) :=
  revOn_of_mem hF h

theorem tour_of_not_mem {F : Finset D} {z : D} (h : R.rot z ∉ F) : R.tour F z = R.rot z :=
  revOn_of_not_mem h

theorem tour_mem_iff {F : Finset D} (hF : R.RevClosed F) (z : D) :
    R.tour F z ∈ F ↔ R.rot z ∈ F := by
  by_cases h : R.rot z ∈ F
  · rw [tour_of_mem hF h]
    exact iff_of_true (hF _ h) h
  · rw [tour_of_not_mem h]

/-- On a forest dart, the tour takes the step of the face. -/
theorem face_inv_of_mem {F : Finset D} (hF : R.RevClosed F) {z : D} (h : R.tour F z ∈ F) :
    R.facePerm⁻¹ z = R.tour F z := by
  rw [tour_of_mem hF ((tour_mem_iff hF z).1 h), R.face_inv_apply]

/-- Off the forest, the face crosses the dart that the tour passes. -/
theorem face_inv_of_not_mem {F : Finset D} (hF : R.RevClosed F) {z : D} (h : R.tour F z ∉ F) :
    R.facePerm⁻¹ z = R.rev (R.tour F z) := by
  rw [tour_of_not_mem (mt (tour_mem_iff hF z).2 h), R.face_inv_apply]

variable (R)

theorem tourMap_face_inv (F : Finset D) : (R.rot⁻¹ * R.revOn F)⁻¹ = R.tour F := by
  rw [mul_inv_rev, revOn_inv, inv_inv]
  rfl

theorem tourMap_edge_inv (F : Finset D) : (R.rot * (R.rot⁻¹ * R.revOn F))⁻¹ = R.revOn F := by
  rw [mul_inv_cancel_left, revOn_inv]

variable {R}

/-- Euler's count for the hypermap of a tour. -/
theorem tour_count {F : Finset D} (hF : R.RevClosed F) :
    2 * nComp (R.tourMap F).glink Set.univ + F.card / 2 =
      2 * (R.tourMap F).genus + R.numVertices + orb (R.tour F) := by
  have h := (R.tourMap F).evenGenus
  unfold Hypermap.EvenGenus Hypermap.eulerLhs Hypermap.eulerRhs at h
  have he : fcard (R.tourMap F).edge Set.univ = orb (R.revOn F) := by
    show fcard (⇑(R.rot * (R.rot⁻¹ * R.revOn F))⁻¹) Set.univ = _
    rw [R.tourMap_edge_inv]
    rfl
  have hn : fcard (R.tourMap F).node Set.univ = R.numVertices := rfl
  have hf : fcard (R.tourMap F).face Set.univ = orb (R.tour F) := by
    show orb (R.rot⁻¹ * R.revOn F) = _
    rw [← orb_inv, R.tourMap_face_inv]
  have hc := (revOn_data hF).2.2
  omega

/-- The cycles of the tour lie in the components of its hypermap. -/
theorem gcomp_of_fconnect_tour {F : Finset D} {x y : D} (h : fconnect (R.tour F) x y) :
    (R.tourMap F).gcomp x y := by
  have h' : fconnect (⇑(R.tour F)⁻¹) x y := (fconnect_inv_iff _).2 h
  rw [show (R.tour F)⁻¹ = R.rot⁻¹ * R.revOn F by rw [← R.tourMap_face_inv, inv_inv]] at h'
  exact connect_mono (fun a b hab => Or.inr (Or.inr hab)) h'

theorem nComp_le_orb (F : Finset D) :
    nComp (R.tourMap F).glink Set.univ ≤ orb (R.tour F) :=
  nComp_le_of_imp (fun _ _ h => gcomp_of_fconnect_tour h) _

/-- If the number of vertices is the number of components of a set of edges plus half the number of
its darts, the set is a forest, and the cycles of its tour are the components of the forest. -/
theorem forest_tour {F : Finset D} (hF : R.RevClosed F)
    (hc : R.numVertices = nComp (R.tourMap F).glink Set.univ + F.card / 2) :
    orb (R.tour F) = nComp (R.tourMap F).glink Set.univ ∧ (R.tourMap F).genus = 0 ∧
      ∀ x y, (R.tourMap F).gcomp x y → fconnect (R.tour F) x y := by
  have h1 := tour_count hF
  have h2 := nComp_le_orb (R := R) F
  have h3 : orb (R.tour F) = nComp (R.tourMap F).glink Set.univ := by omega
  refine ⟨h3, by omega, fun x y h => ?_⟩
  exact connect_of_nComp_eq (fconnect_sym (R.tour F).injective) (R.tourMap F).glinkC
    (fun _ _ h => gcomp_of_fconnect_tour h) h3.symm (Set.mem_univ x) (Set.mem_univ y) h

/-! ### Spanning forests -/

variable (R) in
/-- `F` is a spanning forest: closed under `rev`, the ends of every edge are joined by `F`, and the
count of a forest holds. -/
structure SpanForest (F : Finset D) : Prop where
  rev_closed : R.RevClosed F
  count : R.numVertices = R.numComponents + F.card / 2
  span : ∀ x, (R.tourMap F).gcomp x (R.rev x)

namespace SpanForest

variable {F : Finset D} (hS : R.SpanForest F)

include hS

/-- The hypermap of the tour has the components of `R`. -/
theorem gcomp_iff (x y : D) : (R.tourMap F).gcomp x y ↔ R.toHypermap.gcomp x y := by
  have hsym := (R.tourMap F).glinkC
  constructor
  · refine connect_sub fun a b hab => ?_
    rcases hab with hab | hab | hab
    · have hab' : (R.rot * (R.rot⁻¹ * R.revOn F))⁻¹ a = b := hab
      rw [R.tourMap_edge_inv] at hab'
      rw [← hab']
      by_cases ha : a ∈ F
      · rw [revOn_of_mem hS.rev_closed ha]
        exact connect_of_rel (Or.inl rfl)
      · rw [revOn_of_not_mem ha]
    · exact connect_of_rel (Or.inr (Or.inl hab))
    · have hab' : (R.rot⁻¹ * R.revOn F) a = b := hab
      rw [Equiv.Perm.mul_apply] at hab'
      have hr : R.toHypermap.gcomp (R.revOn F a) a := by
        by_cases ha : a ∈ F
        · rw [revOn_of_mem hS.rev_closed ha]
          exact R.toHypermap.glinkC _ _ (connect_of_rel (Or.inl rfl))
        · rw [revOn_of_not_mem ha]
      have hb : R.toHypermap.gcomp b (R.revOn F a) := by
        rw [← hab']
        exact connect_of_rel (Or.inr (Or.inl (Equiv.apply_symm_apply R.rot _)))
      exact R.toHypermap.glinkC _ _ (connect_trans hb hr)
  · refine connect_sub fun a b hab => ?_
    rcases hab with hab | hab | hab
    · rw [show b = R.rev a from hab.symm]
      exact hS.span a
    · exact connect_of_rel (Or.inr (Or.inl hab))
    · have hab' : R.rot.symm (R.rev a) = b := hab
      have h1 := hS.span a
      have h2 : (R.tourMap F).gcomp b (R.rev a) := by
        rw [← hab']
        exact connect_of_rel (Or.inr (Or.inl (Equiv.apply_symm_apply R.rot _)))
      exact connect_trans h1 (hsym _ _ h2)

theorem nComp_eq : nComp (R.tourMap F).glink Set.univ = R.numComponents :=
  nComp_congr hS.gcomp_iff Set.univ

theorem orb_tour : orb (R.tour F) = R.numComponents := by
  have h := (forest_tour hS.rev_closed (by rw [hS.nComp_eq]; exact hS.count)).1
  rw [h, hS.nComp_eq]

/-- **The cycles of the tour are the components.** -/
theorem fconnect_tour_iff (x y : D) : fconnect (R.tour F) x y ↔ R.toHypermap.gcomp x y := by
  rw [← hS.gcomp_iff]
  exact ⟨gcomp_of_fconnect_tour,
    (forest_tour hS.rev_closed (by rw [hS.nComp_eq]; exact hS.count)).2.2 x y⟩

theorem fconnect_tour_rev (x : D) : fconnect (R.tour F) x (R.rev x) :=
  (hS.fconnect_tour_iff _ _).2 (connect_of_rel (Or.inl rfl))

/-- A cycle of the inverse face permutation lies on one cycle of the tour. -/
theorem fconnect_tour_of_face {x y : D} (h : fconnect (⇑R.facePerm⁻¹) x y) :
    fconnect (R.tour F) x y := by
  refine (hS.fconnect_tour_iff _ _).2 ?_
  exact connect_mono (fun a b hab => Or.inr (Or.inr hab)) ((fconnect_inv_iff _).1 h)

/-- The tour of the forest minus one edge is the tour with one swap. -/
theorem tour_erase {u : D} (hu : u ∈ F) :
    R.tour ((F.erase u).erase (R.rev u)) = Equiv.swap u (R.rev u) * R.tour F := by
  unfold tour
  rw [revOn_eq_swap_mul hS.rev_closed hu, ← mul_assoc, ← mul_assoc, Equiv.swap_mul_self, one_mul]

theorem orb_swap_tour (u : D) :
    orb (Equiv.swap u (R.rev u) * R.tour F) = R.numComponents + 1 := by
  rw [orb_swap_mul_of_fconnect _ (R.rev_ne u).symm (hS.fconnect_tour_rev u), hS.orb_tour]

/-- **The tour of the forest minus one edge.** Darts joined by the forest minus the edge of `u` lie in
one cycle of the tour with the swap of `u`. -/
theorem fconnect_swap_of_erase {u : D} (hu : u ∈ F) {x y : D}
    (h : (R.tourMap ((F.erase u).erase (R.rev u))).gcomp x y) :
    fconnect (⇑(Equiv.swap u (R.rev u) * R.tour F)) x y := by
  have hF' := revClosed_erase hS.rev_closed u
  have hc := card_erase_rev hu hS.rev_closed
  have he := (revOn_data hS.rev_closed).2.1
  have he' := (revOn_data hF').2.1
  have ht := hS.tour_erase hu
  have h1 := tour_count hF'
  rw [ht, hS.orb_swap_tour] at h1
  have h2 := nComp_le_orb (R := R) ((F.erase u).erase (R.rev u))
  rw [ht, hS.orb_swap_tour] at h2
  have hcount := hS.count
  have h3 : nComp (R.tourMap ((F.erase u).erase (R.rev u))).glink Set.univ =
      R.numComponents + 1 := by
    omega
  have h4 := (forest_tour hF' (by omega)).2.2 x y h
  rwa [ht] at h4

/-! ### Faces -/

theorem revOn_compl_mul_tour : R.revOn Fᶜ * R.tour F = R.facePerm⁻¹ := by
  refine Equiv.ext fun z => ?_
  rw [R.face_inv_apply, Equiv.Perm.mul_apply, tour_apply]
  by_cases h : R.rot z ∈ F
  · rw [revOn_of_mem hS.rev_closed h, revOn_of_not_mem]
    simpa using hS.rev_closed _ h
  · rw [revOn_of_not_mem h, revOn_of_mem (revClosed_compl hS.rev_closed) (by simpa using h)]

/-- The faces of a planar map with a spanning forest: one per component and one per edge off the
forest. -/
theorem orb_face (hP : R.Planar) : orb R.facePerm⁻¹ = R.numComponents + Fᶜ.card / 2 := by
  have h := R.euler_components hP
  have hc := hS.count
  have h1 := (revOn_data hS.rev_closed).2.1
  have h2 := (revOn_data (revClosed_compl hS.rev_closed)).2.1
  have h3 := R.card_eq
  have h4 : F.card + Fᶜ.card = Fintype.card D := Finset.card_add_card_compl F
  have hf : R.numFaces = orb R.facePerm⁻¹ := (R.numFaces_eq_orb).trans (orb_inv _).symm
  omega

/-- The inverse face permutation with the swap of one edge off the forest taken out. -/
theorem face_inv_eq {u : D} (hu : u ∉ F) :
    R.facePerm⁻¹ = R.revOn ((Fᶜ.erase u).erase (R.rev u)) *
      (Equiv.swap u (R.rev u) * R.tour F) := by
  rw [← hS.revOn_compl_mul_tour, revOn_eq_mul_swap (revClosed_compl hS.rev_closed)
    (by simpa using hu : u ∈ Fᶜ), mul_assoc]

/-- **Two corners of one face stay in one cycle** after the swap of an edge off the forest. -/
theorem fconnect_swap_of_face (hP : R.Planar) {u x y : D} (hu : u ∉ F) (hxy : x ≠ y)
    (hf : fconnect (⇑R.facePerm⁻¹) x y) :
    fconnect (⇑(Equiv.swap u (R.rev u) * R.tour F)) x y := by
  have hC := revClosed_compl hS.rev_closed
  have huC : u ∈ Fᶜ := by simpa using hu
  have hBc := card_erase_rev huC hC
  have hd := (revOn_data hC).2.1
  have hd' := revOn_data (revClosed_erase hC u)
  have hφ := hS.face_inv_eq hu
  have h1 : orb (Equiv.swap x y * R.facePerm⁻¹) = orb R.facePerm⁻¹ + 1 :=
    orb_swap_mul_of_fconnect _ hxy hf
  have hconj : Equiv.swap x y * R.facePerm⁻¹ =
      (Equiv.swap x y * R.revOn ((Fᶜ.erase u).erase (R.rev u)) * (Equiv.swap x y)⁻¹) *
        (Equiv.swap x y * (Equiv.swap u (R.rev u) * R.tour F)) := by
    rw [hφ]
    simp [mul_assoc]
  have h2 := (hd'.1.conj (Equiv.swap x y)).orb_mul_le
    (Equiv.swap x y * (Equiv.swap u (R.rev u) * R.tour F))
  rw [← hconj, h1, hS.orb_face hP] at h2
  by_contra hn
  have h3 := orb_swap_mul_of_not_fconnect _ hn
  rw [hS.orb_swap_tour] at h3
  omega

/-- **The two darts of an edge off the forest stay in one cycle** after the swap of another edge off
the forest. -/
theorem fconnect_swap_rev (hP : R.Planar) {u v : D} (hu : u ∉ F) (hv : v ∉ F) (h1 : v ≠ u)
    (h2 : v ≠ R.rev u) : fconnect (⇑(Equiv.swap u (R.rev u) * R.tour F)) v (R.rev v) := by
  have hC := revClosed_compl hS.rev_closed
  have huC : u ∈ Fᶜ := by simpa using hu
  have hC1 := revClosed_erase hC u
  have hvC : v ∈ (Fᶜ.erase u).erase (R.rev u) := by simp [hv, h1, h2]
  have hBc := card_erase_rev huC hC
  have hBc' := card_erase_rev hvC hC1
  have hd := (revOn_data hC).2.1
  have hd1 := (revOn_data hC1).2.1
  have hd2 := revOn_data (revClosed_erase hC1 v)
  have hφ : R.facePerm⁻¹ = R.revOn (((Fᶜ.erase u).erase (R.rev u)).erase v |>.erase (R.rev v)) *
      (Equiv.swap v (R.rev v) * (Equiv.swap u (R.rev u) * R.tour F)) := by
    rw [hS.face_inv_eq hu, revOn_eq_mul_swap hC1 hvC, mul_assoc]
  have h3 := hd2.1.orb_mul_le (Equiv.swap v (R.rev v) * (Equiv.swap u (R.rev u) * R.tour F))
  rw [← hφ, hS.orb_face hP] at h3
  by_contra hn
  have h4 := orb_swap_mul_of_not_fconnect _ hn
  rw [hS.orb_swap_tour] at h4
  omega

/-! ### Walking along a face -/

variable (R F) in
/-- The arc `(a, z]` of the tour contains the reverse of every dart off the forest in it. -/
def ArcClosed (a z : D) : Prop :=
  ∀ h, InArc (R.tour F) a z h → h ∉ F → InArc (R.tour F) a z (R.rev h)

omit hS in
theorem arcClosed_start (a : D) : ArcClosed R F a a := fun _ h _ => (not_inArc_empty h).elim

/-- A dart off the forest behind `z`: it is not the start, and its reverse comes later. -/
theorem walk_jump {a z : D} (hz : fconnect (R.tour F) a z) (hc : ArcClosed R F a z)
    (hw : R.tour F z ∉ F) (hra : R.rev (R.tour F z) ≠ a) :
    R.tour F z ≠ a ∧ pos (R.tour F) a (R.tour F z) < pos (R.tour F) a (R.rev (R.tour F z)) := by
  have hrF : ∀ {h : D}, h ∉ F → R.rev h ∉ F := fun {h} hh hr => hh (by
    simpa [R.rev_rev] using hS.rev_closed _ hr)
  have hwa : R.tour F z ≠ a := by
    intro hwa
    have h1 : InArc (R.tour F) a z (R.rev a) :=
      ⟨hS.fconnect_tour_rev a, R.rev_ne a, pos_le_of_last hwa hz _⟩
    have h2 := hc _ h1 (hrF (hwa ▸ hw))
    rw [R.rev_rev] at h2
    exact not_inArc_start h2
  refine ⟨hwa, ?_⟩
  have hpw := pos_apply hz hwa
  have hcw := fconnect_apply hz
  have hcr := connect_trans hcw (hS.fconnect_tour_rev (R.tour F z))
  by_contra hle
  have hne : pos (R.tour F) a (R.rev (R.tour F z)) ≠ pos (R.tour F) a (R.tour F z) :=
    fun e => R.rev_ne _ (pos_inj hcr hcw e)
  have h2 := hc _ ⟨hcr, hra, by omega⟩ (hrF hw)
  rw [R.rev_rev] at h2
  have := h2.2.2
  omega

/-- **One step along a face.** The inverse face permutation either closes the face or moves forward
on the tour, and the arc from the start stays closed. -/
theorem walk_step (hP : R.Planar) {a z : D} (hz : fconnect (R.tour F) a z)
    (hc : ArcClosed R F a z) :
    R.facePerm⁻¹ z = a ∨ (pos (R.tour F) a z < pos (R.tour F) a (R.facePerm⁻¹ z) ∧
      ArcClosed R F a (R.facePerm⁻¹ z)) := by
  by_cases hw : R.tour F z ∈ F
  · rw [face_inv_of_mem hS.rev_closed hw]
    by_cases hwa : R.tour F z = a
    · exact Or.inl hwa
    · have hp := pos_apply hz hwa
      refine Or.inr ⟨by omega, fun h hh hhF => ?_⟩
      rcases (inArc_succ hz hwa h).1 hh with h1 | h1
      · exact (hc h h1 hhF).mono (by omega)
      · exact (hhF (h1 ▸ hw)).elim
  · rw [face_inv_of_not_mem hS.rev_closed hw]
    by_cases hra : R.rev (R.tour F z) = a
    · exact Or.inl hra
    right
    obtain ⟨hwa, hgt⟩ := hS.walk_jump hz hc hw hra
    have hp := pos_apply hz hwa
    have hcw := fconnect_apply hz
    have hcr := connect_trans hcw (hS.fconnect_tour_rev (R.tour F z))
    refine ⟨by omega, fun h hh hhF => ?_⟩
    by_cases h1 : pos (R.tour F) a h ≤ pos (R.tour F) a z
    · exact (hc h ⟨hh.1, hh.2.1, h1⟩ hhF).mono (by omega)
    by_cases h2 : h = R.tour F z
    · rw [h2]
      exact inArc_end hcr hra
    by_cases h3 : h = R.rev (R.tour F z)
    · rw [h3, R.rev_rev]
      exact ⟨hcw, hwa, by omega⟩
    have hne : pos (R.tour F) a h ≠ pos (R.tour F) a (R.tour F z) := fun e => h2 (pos_inj hh.1 hcw e)
    have hle := hh.2.2
    have hin : InArc (R.tour F) (R.tour F z) (R.rev (R.tour F z)) h := by
      refine ⟨connect_trans (fconnect_symm hcw) hh.1, h2, ?_⟩
      rw [pos_shift hcw hh.1 (by omega), pos_shift hcw hcr (by omega)]
      omega
    have hnc := hS.fconnect_swap_rev hP hhF hw (Ne.symm h2)
      (fun e => h3 (by rw [e, R.rev_rev]))
    have hiff := inArc_iff_of_swap (hS.fconnect_tour_rev h) hnc
    exact (hiff.1 hin).of_shift hcw hwa hcr (by omega)

/-- **The corners of a face appear on the tour in the order of the face.** -/
theorem walk_strict (hP : R.Planar) (a : D) {n : ℕ}
    (hn : ∀ i, 0 < i → i ≤ n → (⇑R.facePerm⁻¹)^[i] a ≠ a) :
    ArcClosed R F a ((⇑R.facePerm⁻¹)^[n] a) ∧
      ∀ i, i < n → pos (R.tour F) a ((⇑R.facePerm⁻¹)^[i] a) <
        pos (R.tour F) a ((⇑R.facePerm⁻¹)^[i + 1] a) := by
  induction n with
  | zero => exact ⟨arcClosed_start a, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
    obtain ⟨hc, hlt⟩ := ih fun i h0 hi => hn i h0 (by omega)
    have hz : fconnect (R.tour F) a ((⇑R.facePerm⁻¹)^[n] a) :=
      hS.fconnect_tour_of_face (fconnect_iterate _ _ _)
    have hs := hS.walk_step hP hz hc
    rw [← Function.iterate_succ_apply' (⇑R.facePerm⁻¹) n a] at hs
    rcases hs with hs | ⟨hs1, hs2⟩
    · exact (hn (n + 1) (Nat.succ_pos _) le_rfl hs).elim
    · refine ⟨hs2, fun i hi => ?_⟩
      by_cases hin : i < n
      · exact hlt i hin
      · obtain rfl : i = n := by omega
        exact hs1

/-! ### Balance -/

variable (R F) in
/-- The arc `(w, rev w]` has about three quarters of the forest darts of the cycle, or more. -/
def Heavy (w : D) : Prop :=
  3 * cycMass (R.tour F) F w < 4 * mass (R.tour F) F w (R.rev w) + 2

variable (R F) in
/-- A start of a walk along a face that cuts the cycle in a balanced way: either a dart off the forest
that is heavy and spans the least positions among the heavy darts of its cycle, or any dart of a cycle
without a dart off the forest. -/
def GoodStart (a : D) : Prop :=
  (a ∉ F ∧ Heavy R F a ∧ ∀ w, fconnect (R.tour F) a w → w ∉ F →
      pos (R.tour F) w (R.rev w) < pos (R.tour F) a (R.rev a) → ¬ Heavy R F w) ∨
    ∀ w, fconnect (R.tour F) a w → w ∈ F

variable (R F) in
/-- Every dart off the forest on the cycle of `a` is heavy, or its reverse is. -/
def NoBalanced (a : D) : Prop :=
  ∀ w, fconnect (R.tour F) a w → w ∉ F → Heavy R F w ∨ Heavy R F (R.rev w)

/-- While the mass from a good start is small, a step along the face does not close the face and does
not pass the balance. -/
theorem mass_walk (hP : R.Planar) {a z : D} (ht : 4 ≤ cycMass (R.tour F) F a)
    (hstart : GoodStart R F a) (hnb : NoBalanced R F a) (hz : fconnect (R.tour F) a z)
    (hc : ArcClosed R F a z) (hsmall : 4 * mass (R.tour F) F a z < cycMass (R.tour F) F a + 2) :
    R.facePerm⁻¹ z ≠ a ∧ pos (R.tour F) a z < pos (R.tour F) a (R.facePerm⁻¹ z) ∧
      ArcClosed R F a (R.facePerm⁻¹ z) ∧
      4 * mass (R.tour F) F a (R.facePerm⁻¹ z) + 2 ≤ 3 * cycMass (R.tour F) F a := by
  have hstep := hS.walk_step hP hz hc
  by_cases hw : R.tour F z ∈ F
  · rw [face_inv_of_mem hS.rev_closed hw] at hstep ⊢
    by_cases hwa : R.tour F z = a
    · have := cycMass_le_of_last F hwa hz
      omega
    · rcases hstep with h | ⟨hlt, hcl⟩
      · exact (hwa h).elim
      · have := mass_succ_le F hz hwa
        exact ⟨hwa, hlt, hcl, by omega⟩
  · rw [face_inv_of_not_mem hS.rev_closed hw] at hstep ⊢
    have hcw := fconnect_apply hz
    rcases hstart with ⟨haF, hheavy, hmin⟩ | hall
    swap
    · exact (hw (hall _ hcw)).elim
    by_cases hra : R.rev (R.tour F z) = a
    · have hwe : R.tour F z = R.rev a := by rw [← hra, R.rev_rev]
      have hwa : R.tour F z ≠ a := fun e => R.rev_ne a (hwe.symm.trans e)
      have hm := mass_succ_of_not_mem hz hwa hw
      unfold Heavy at hheavy
      rw [← hwe, hm] at hheavy
      omega
    · obtain ⟨hwa, hgt⟩ := hS.walk_jump hz hc hw hra
      rcases hstep with h | ⟨hlt, hcl⟩
      · exact (hra h).elim
      refine ⟨hra, hlt, hcl, ?_⟩
      have hcr := connect_trans hcw (hS.fconnect_tour_rev (R.tour F z))
      have hrF : R.rev a ∉ F := fun h => haF (by simpa [R.rev_rev] using hS.rev_closed _ h)
      have hnot : ¬ InArc (R.tour F) a (R.rev (R.tour F z)) (R.rev a) := fun h => by
        have h2 := hcl _ h hrF
        rw [R.rev_rev] at h2
        exact not_inArc_start h2
      have hlt' : pos (R.tour F) a (R.rev (R.tour F z)) < pos (R.tour F) a (R.rev a) := by
        by_contra hle
        exact hnot ⟨hS.fconnect_tour_rev a, R.rev_ne a, by omega⟩
      have hshift := pos_shift hcw hcr hgt.le
      have h0 := pos_pos hcw hwa
      have hnh := hmin _ hcw hw (by omega)
      have hrh : Heavy R F (R.rev (R.tour F z)) := (hnb _ hcw hw).resolve_left hnh
      unfold Heavy at hrh
      rw [R.rev_rev] at hrh
      have hadd := mass_add_mass F (hS.fconnect_tour_rev (R.tour F z)) (R.rev_ne _).symm
      have e1 := cycMass_congr F hcw
      have e2 := cycMass_congr F hcr
      have hj := mass_jump hz hwa hw hcr hgt.le
      omega

/-- **The crossing point.** From a good start, a walk along the face meets a corner whose arc from the
start holds between a quarter and three quarters of the forest darts of the cycle. -/
theorem exists_crossing (hP : R.Planar) {a : D} (ht : 4 ≤ cycMass (R.tour F) F a)
    (hstart : GoodStart R F a) (hnb : NoBalanced R F a) :
    ∃ y, fconnect (⇑R.facePerm⁻¹) a y ∧ cycMass (R.tour F) F a + 2 ≤ 4 * mass (R.tour F) F a y ∧
      4 * mass (R.tour F) F a y + 2 ≤ 3 * cycMass (R.tour F) F a := by
  classical
  let S : Finset D := Finset.univ.filter fun z => fconnect (⇑R.facePerm⁻¹) a z ∧
    ArcClosed R F a z ∧ 4 * mass (R.tour F) F a z < cycMass (R.tour F) F a + 2
  have haS : a ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, mass_self]
    exact ⟨connect_refl a, arcClosed_start a, by omega⟩
  obtain ⟨z, hzS, hmax⟩ := S.exists_max_image (pos (R.tour F) a) ⟨a, haS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS
  obtain ⟨hz, hc, hsm⟩ := hzS
  obtain ⟨_, hlt, hcl, hb⟩ := hS.mass_walk hP ht hstart hnb (hS.fconnect_tour_of_face hz) hc hsm
  refine ⟨R.facePerm⁻¹ z, fconnect_apply hz, ?_, hb⟩
  by_contra hlow
  have hin : R.facePerm⁻¹ z ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fconnect_apply hz, hcl, by omega⟩
  have := hmax _ hin
  omega

/-- A crossing point cuts the cycle in a balanced way. -/
theorem crossing_cut {a y : D} (hay : fconnect (⇑R.facePerm⁻¹) a y)
    (h1 : cycMass (R.tour F) F a + 2 ≤ 4 * mass (R.tour F) F a y)
    (h2 : 4 * mass (R.tour F) F a y + 2 ≤ 3 * cycMass (R.tour F) F a) :
    a ≠ y ∧ 4 * mass (R.tour F) F y a + 2 ≤ 3 * cycMass (R.tour F) F a := by
  have hne : a ≠ y := by
    rintro rfl
    rw [mass_self] at h1
    omega
  have := mass_add_mass F (hS.fconnect_tour_of_face hay) hne
  exact ⟨hne, by omega⟩

/-- **A dart off the forest that is not heavy, with a reverse that is not heavy**, cuts the cycle in a
balanced way at its two corners of one face. -/
theorem balanced_cut {g : D} (hg : g ∉ F) (ht : 1 ≤ cycMass (R.tour F) F g) (h1 : ¬ Heavy R F g)
    (h2 : ¬ Heavy R F (R.rev g)) :
    R.facePerm⁻¹ (R.facePerm g) = g ∧ g ≠ R.facePerm g ∧
      4 * mass (R.tour F) F g (R.facePerm g) + 2 ≤ 3 * cycMass (R.tour F) F g ∧
      4 * mass (R.tour F) F (R.facePerm g) g + 2 ≤ 3 * cycMass (R.tour F) F g := by
  have hrF : R.rev g ∉ F := fun h => hg (by simpa [R.rev_rev] using hS.rev_closed _ h)
  have hrot : R.rot (R.facePerm g) = R.rev g := by
    show R.rot (R.rot.symm (R.rev g)) = R.rev g
    exact R.rot.apply_symm_apply _
  have hy : R.tour F (R.facePerm g) = R.rev g := by
    rw [tour_of_not_mem (by rw [hrot]; exact hrF), hrot]
  have hcr := hS.fconnect_tour_rev g
  have hcy : fconnect (R.tour F) g (R.facePerm g) := by
    refine fconnect_of_apply ?_
    rw [hy]
    exact hcr
  have hadd := mass_add_mass F hcr (R.rev_ne g).symm
  have ecr := cycMass_congr F hcr
  unfold Heavy at h1 h2
  rw [R.rev_rev, ← ecr] at h2
  have hne : g ≠ R.facePerm g := by
    intro e
    have hyg : R.tour F g = R.rev g := by
      have := hy
      rwa [← e] at this
    have hm := mass_succ_of_not_mem (x := g) (y := g) (T := F) (f := R.tour F) (connect_refl g)
      (by rw [hyg]; exact R.rev_ne g) (by rw [hyg]; exact hrF)
    rw [hyg, mass_self] at hm
    omega
  have hm := mass_succ_of_not_mem (T := F) hcy (by rw [hy]; exact R.rev_ne g) (by rw [hy]; exact hrF)
  rw [hy] at hm
  have hadd2 := mass_add_mass F hcy hne
  exact ⟨R.facePerm.symm_apply_apply g, hne, by omega, by omega⟩

/-- **The balance lemma.** A cycle of the tour with at least four forest darts has two corners of one
face, such that both arcs between them hold about three quarters of its forest darts, or less. -/
theorem exists_balanced (hP : R.Planar) {c : D} (ht : 4 ≤ cycMass (R.tour F) F c) :
    ∃ x y, fconnect (R.tour F) c x ∧ x ≠ y ∧ fconnect (⇑R.facePerm⁻¹) x y ∧
      4 * mass (R.tour F) F x y + 2 ≤ 3 * cycMass (R.tour F) F c ∧
      4 * mass (R.tour F) F y x + 2 ≤ 3 * cycMass (R.tour F) F c := by
  classical
  by_cases hb : ∃ g, fconnect (R.tour F) c g ∧ g ∉ F ∧ ¬ Heavy R F g ∧ ¬ Heavy R F (R.rev g)
  · obtain ⟨g, hcg, hg, h1, h2⟩ := hb
    have e := cycMass_congr F hcg
    obtain ⟨h3, h4, h5, h6⟩ := hS.balanced_cut hg (by omega) h1 h2
    refine ⟨g, R.facePerm g, hcg, h4, ?_, by omega, by omega⟩
    have h7 := fconnect1 (⇑R.facePerm⁻¹) (R.facePerm g)
    rw [h3] at h7
    exact fconnect_symm h7
  have hnb : ∀ w, fconnect (R.tour F) c w → w ∉ F → Heavy R F w ∨ Heavy R F (R.rev w) := by
    intro w h1 h2
    by_contra h3
    push Not at h3
    exact hb ⟨w, h1, h2, h3⟩
  have finish : ∀ a, fconnect (R.tour F) c a → GoodStart R F a → ∃ x y,
      fconnect (R.tour F) c x ∧ x ≠ y ∧ fconnect (⇑R.facePerm⁻¹) x y ∧
      4 * mass (R.tour F) F x y + 2 ≤ 3 * cycMass (R.tour F) F c ∧
      4 * mass (R.tour F) F y x + 2 ≤ 3 * cycMass (R.tour F) F c := by
    intro a hca hstart
    have e := cycMass_congr F hca
    obtain ⟨y, hay, h1, h2⟩ := hS.exists_crossing hP (by omega) hstart
      (fun w hw hF => hnb w (connect_trans hca hw) hF)
    obtain ⟨h3, h4⟩ := hS.crossing_cut hay h1 h2
    exact ⟨a, y, hca, h3, hay, by omega, by omega⟩
  by_cases hn : ∃ g, fconnect (R.tour F) c g ∧ g ∉ F
  · obtain ⟨g, hg1, hg2⟩ := hn
    let Hs : Finset D := Finset.univ.filter fun w =>
      fconnect (R.tour F) c w ∧ w ∉ F ∧ Heavy R F w
    have hrF : R.rev g ∉ F := fun h => hg2 (by simpa [R.rev_rev] using hS.rev_closed _ h)
    have hne : Hs.Nonempty := by
      rcases hnb g hg1 hg2 with h | h
      · exact ⟨g, by simp only [Hs, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hg1, hg2, h⟩⟩
      · exact ⟨R.rev g, by
          simp only [Hs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨connect_trans hg1 (hS.fconnect_tour_rev g), hrF, h⟩⟩
    obtain ⟨a, haH, hmin⟩ := Hs.exists_min_image (fun w => pos (R.tour F) w (R.rev w)) hne
    simp only [Hs, Finset.mem_filter, Finset.mem_univ, true_and] at haH
    refine finish a haH.1 (Or.inl ⟨haH.2.1, haH.2.2, fun w hw hwF hlt hH => ?_⟩)
    have hw' : w ∈ Hs := by
      simp only [Hs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨connect_trans haH.1 hw, hwF, hH⟩
    have := hmin w hw'
    omega
  · push Not at hn
    exact finish c (connect_refl c) (Or.inr hn)

end SpanForest

end RotSystem

end SsspFlow
