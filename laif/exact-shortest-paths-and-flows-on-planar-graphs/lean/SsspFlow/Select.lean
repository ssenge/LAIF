import SsspFlow.Potential

/-!
# The cut of a bag

Each bag of a level with marked darts gets a cut of at most two darts by a rule in terms of masses on its tour
(`selOf`). A bag with fewer than four marks is cut at the corner of a vertex without a corner. A larger bag is
cut at a dart `a` that is balanced or first heavy on its tour, and at a dart `y` on the same face of the map
with a balanced arc from `a`. The rule gives a decomposition in the sense of `Decomp` (`decomp_levelSeq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

section Argmin

variable {α : Type*}

open Classical in
/-- The elements of `S` with the least value. -/
noncomputable def argminF (S : Finset α) (f : α → ℕ) : Finset α :=
  S.filter fun z => ∀ z' ∈ S, f z ≤ f z'

theorem mem_argminF {S : Finset α} {f : α → ℕ} {z : α} :
    z ∈ argminF S f ↔ z ∈ S ∧ ∀ z' ∈ S, f z ≤ f z' := by
  classical
  simp [argminF]

theorem argminF_nonempty {S : Finset α} {f : α → ℕ} (h : S.Nonempty) : (argminF S f).Nonempty := by
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S f h
  exact ⟨z, mem_argminF.2 ⟨hz, hmin⟩⟩

theorem argminF_unique {S : Finset α} {f : α → ℕ} (hf : ∀ z ∈ S, ∀ z' ∈ S, f z = f z' → z = z')
    {z z' : α} (h : z ∈ argminF S f) (h' : z' ∈ argminF S f) : z = z' :=
  let ⟨h1, h2⟩ := mem_argminF.1 h
  let ⟨h3, h4⟩ := mem_argminF.1 h'
  hf z h1 z' h3 (le_antisymm (h2 z' h3) (h4 z h1))

theorem card_argminF_le {S : Finset α} {f : α → ℕ} (hf : ∀ z ∈ S, ∀ z' ∈ S, f z = f z' → z = z') :
    (argminF S f).card ≤ 1 :=
  Finset.card_le_one.2 fun _ h _ h' => argminF_unique hf h h'

end Argmin

/-- The first part of a lexicographic value decides. -/
theorem lex_le {W a b c c' : ℕ} (h : a * W + c ≤ b * W + c') (hc : c' < W) : a ≤ b := by
  by_contra hlt
  have h1 : (b + 1) * W ≤ a * W := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

theorem lex_mod {W a c : ℕ} (hc : c < W) : (a * W + c) % W = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- A face of the cone lies on one face of the map. -/
theorem fconnect_face_of_cone (R : RotSystem D) (Γ : Finset D) {x y : D}
    (h : fconnect (R.cone Γ).facePerm x y) : fconnect R.facePerm x y := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
  clear h
  induction n with
  | zero => exact fconnect_iterate _ _ 0
  | succ n ih =>
    rw [Function.iterate_succ_apply', R.cone_facePerm]
    show fconnect R.facePerm x ((R.faceReturn Γ)⁻¹ (R.facePerm _))
    have h1 := fconnect_firstReturn R.facePerm Γ ((R.faceReturn Γ)⁻¹ (R.facePerm
      ((⇑(R.cone Γ).facePerm)^[n] x)))
    have h2 : firstReturn R.facePerm Γ ((R.faceReturn Γ)⁻¹ (R.facePerm
        ((⇑(R.cone Γ).facePerm)^[n] x))) = R.facePerm ((⇑(R.cone Γ).facePerm)^[n] x) :=
      perm_apply_inv_self _ _
    rw [h2] at h1
    exact connect_trans (fconnect_apply ih) (fconnect_symm h1)

variable (R) in
open Classical in
/-- The darts of the bag of `u`. -/
noncomputable def dartsOf (Γ : Finset (D × Bool)) (u : D × Bool) : Finset (D × Bool) :=
  Finset.univ.filter (R.Same Γ u)

theorem mem_dartsOf {Γ : Finset (D × Bool)} {u z : D × Bool} : z ∈ R.dartsOf Γ u ↔ R.Same Γ u z := by
  classical
  simp [dartsOf]

theorem dartsOf_congr {Γ : Finset (D × Bool)} {u u' : D × Bool} (h : R.Same Γ u u') :
    R.dartsOf Γ u = R.dartsOf Γ u' := by
  ext z
  rw [mem_dartsOf, mem_dartsOf]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

theorem npOf_congr {Γ : Finset (D × Bool)} {u u' : D × Bool} (h : R.Same Γ u u') :
    t.npOf Γ u = t.npOf Γ u' := by
  classical
  unfold npOf
  congr 1
  ext z
  simp only [Finset.mem_filter, and_congr_right_iff]
  exact fun _ => ⟨fun h' => Same.trans (Same.symm h) h', fun h' => Same.trans h h'⟩

section Rule

variable (code : D × Bool → ℕ) (W : ℕ) (fid : D × Bool → ℕ) (Γ : Finset (D × Bool))

variable (t) in
/-- A heavy dart on the tour of a level. -/
abbrev Hv (w : D × Bool) : Prop := SpanForest.Heavy (R.double.cone Γ) (t.marks Γ) w

variable (t) in
open Classical in
/-- The value of a start of a cut: balanced darts come first, then heavy darts by the length of their arc. -/
noncomputable def startVal (z : D × Bool) : ℕ :=
  if t.Hv Γ z then (pos (t.tourL Γ) z (R.double.rev z) + 1) * W + code z else 0 * W + code z

variable (t) in
open Classical in
/-- The candidates for a start of a cut. -/
noncomputable def startSet (u : D × Bool) : Finset (D × Bool) :=
  (R.dartsOf Γ u).filter fun z => z ∉ t.marks Γ ∧ (t.Hv Γ z ∨ ¬ t.Hv Γ (R.double.rev z))

variable (t) in
/-- The value of an end of a cut. -/
noncomputable def endVal (a z : D × Bool) : ℕ := mass (t.tourL Γ) (t.marks Γ) a z * W + code z

variable (t) in
open Classical in
/-- The candidates for an end of a cut from `a`. -/
noncomputable def endSet (u a : D × Bool) : Finset (D × Bool) :=
  (R.dartsOf Γ u).filter fun z =>
    fid z = fid a ∧ t.npOf Γ u + 2 ≤ 4 * mass (t.tourL Γ) (t.marks Γ) a z

variable (t) in
open Classical in
/-- The candidates for the cut of a small bag. -/
noncomputable def smallSet (u : D × Bool) : Finset (D × Bool) :=
  (R.dartsOf Γ u).filter fun z => ∃ v, t.NP Γ v ∧ z = t.r0 v

variable (t) in
/-- The start of the cut of a bag. -/
noncomputable def startOfBag (u : D × Bool) : Finset (D × Bool) :=
  argminF (t.startSet Γ u) (t.startVal code W Γ)

variable (t) in
/-- The cut of the bag of `u`. -/
noncomputable def selOf (u : D × Bool) : Finset (D × Bool) :=
  if t.npOf Γ u = 0 then ∅
  else if t.npOf Γ u < 4 then argminF (t.smallSet Γ u) code
  else t.startOfBag code W Γ u ∪
    (t.startOfBag code W Γ u).biUnion fun a =>
      argminF (t.endSet fid Γ u a) (t.endVal code W Γ a)

variable (t) in
/-- The cuts of all bags of a level. -/
noncomputable def sel : Finset (D × Bool) := Finset.univ.biUnion (t.selOf code W fid Γ)

variable {code W fid Γ}

theorem mem_sel {z : D × Bool} : z ∈ t.sel code W fid Γ ↔ ∃ u, z ∈ t.selOf code W fid Γ u := by
  simp [sel]

theorem selOf_congr {u u' : D × Bool} (h : R.Same Γ u u') :
    t.selOf code W fid Γ u = t.selOf code W fid Γ u' := by
  unfold selOf startOfBag startSet endSet smallSet
  rw [dartsOf_congr h, npOf_congr (t := t) h]

theorem startSet_nonempty (hL : t.IsLevel Γ) (hc : R.Connected) (u : D × Bool) :
    (t.startSet Γ u).Nonempty := by
  classical
  obtain ⟨g, hg, hug⟩ := R.double.split_meets (R.double_connected hc) hL.nonempty u
  have hgF := not_mem_marks_of_mem hL hg
  by_cases h : t.Hv Γ g ∨ ¬ t.Hv Γ (R.double.rev g)
  · exact ⟨g, Finset.mem_filter.2 ⟨mem_dartsOf.2 hug, hgF, h⟩⟩
  · push Not at h
    refine ⟨R.double.rev g, Finset.mem_filter.2 ⟨mem_dartsOf.2 (Same.trans hug (same_rev Γ g)), ?_,
      Or.inl h.2⟩⟩
    intro hm
    have := t.marks_revClosed Γ _ hm
    rw [R.double.rev_rev] at this
    exact hgF this

/-- A start of a cut has a balanced arc to a dart on one face of the cone. -/
theorem exists_end (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected) (hW : ∀ z, code z < W)
    {u a : D × Bool} (ha : a ∈ t.startOfBag code W Γ u) (hn : 4 ≤ t.npOf Γ u) :
    ∃ y, fconnect (⇑(R.double.cone Γ).facePerm⁻¹) a y ∧
      t.npOf Γ u + 2 ≤ 4 * mass (t.tourL Γ) (t.marks Γ) a y ∧
      4 * mass (t.tourL Γ) (t.marks Γ) a y + 2 ≤ 3 * t.npOf Γ u := by
  classical
  obtain ⟨hmem, hmin⟩ := mem_argminF.1 ha
  obtain ⟨hau, haF, hcand⟩ := Finset.mem_filter.1 hmem
  have hau' : R.Same Γ u a := mem_dartsOf.1 hau
  have hS := hL.spanForest hR hc
  have hcyc := cycMass_eq_npOf (t := t) hL hR hc a
  rw [npOf_congr (t := t) hau'] at hn ⊢
  rw [← hcyc] at hn ⊢
  have hcand' : ∀ {w}, fconnect (t.tourL Γ) a w → w ∉ t.marks Γ →
      (t.Hv Γ w ∨ ¬ t.Hv Γ (R.double.rev w)) → w ∈ t.startSet Γ u := fun hw hwF h => by
    refine Finset.mem_filter.2 ⟨mem_dartsOf.2 (Same.trans hau' ?_), hwF, h⟩
    exact (R.double.cone_gcomp_iff Γ _ _).1 ((hS.fconnect_tour_iff _ _).1 hw)
  by_cases hH : t.Hv Γ a
  · have hstart : SpanForest.GoodStart (R.double.cone Γ) (t.marks Γ) a := by
      refine Or.inl ⟨haF, hH, fun w hw hwF hlt hHw => ?_⟩
      have h1 := hmin w (hcand' hw hwF (Or.inl hHw))
      unfold startVal at h1
      rw [if_pos hH, if_pos hHw] at h1
      have h2 := lex_le h1 (hW w)
      have h3 : pos (t.tourL Γ) w (R.double.rev w) < pos (t.tourL Γ) a (R.double.rev a) := hlt
      omega
    have hnb : SpanForest.NoBalanced (R.double.cone Γ) (t.marks Γ) a := by
      intro w hw hwF
      by_contra hno
      push Not at hno
      have h1 := hmin w (hcand' hw hwF (Or.inr hno.2))
      unfold startVal at h1
      rw [if_pos hH, if_neg hno.1] at h1
      have h2 := lex_le h1 (hW w)
      omega
    exact hS.exists_crossing (hL.cone_planar hR hc) hn hstart hnb
  · have h2 : ¬ t.Hv Γ (R.double.rev a) := by
      rcases hcand with h | h
      · exact (hH h).elim
      · exact h
    obtain ⟨_, hne, h3, h4⟩ := hS.balanced_cut haF
      (show 1 ≤ cycMass (t.tourL Γ) (t.marks Γ) a by omega) hH h2
    have hf : fconnect (⇑(R.double.cone Γ).facePerm⁻¹) a ((R.double.cone Γ).facePerm a) :=
      (fconnect_inv_iff _).2 (fconnect1 _ a)
    have h5 := mass_add_mass (t.marks Γ) (hS.fconnect_tour_of_face hf) hne
    refine ⟨_, hf, ?_, h3⟩
    have h6 : mass (t.tourL Γ) (t.marks Γ) a ((R.double.cone Γ).facePerm a) +
        mass (t.tourL Γ) (t.marks Γ) ((R.double.cone Γ).facePerm a) a =
        cycMass (t.tourL Γ) (t.marks Γ) a := h5
    have h7 : 4 * mass (t.tourL Γ) (t.marks Γ) ((R.double.cone Γ).facePerm a) a + 2 ≤
        3 * cycMass (t.tourL Γ) (t.marks Γ) a := h4
    show cycMass (t.tourL Γ) (t.marks Γ) a + 2 ≤
      4 * mass (t.tourL Γ) (t.marks Γ) a ((R.double.cone Γ).facePerm a)
    omega

/-- The face of the cone at a corner of a digon is a single dart. -/
theorem cone_face_digon (hL : t.IsLevel Γ) {a : D × Bool} (ha : a ∈ Γ) (h2 : a.2 = false) :
    (R.double.cone Γ).facePerm a = a := by
  obtain ⟨d, b⟩ := a
  obtain rfl : b = false := h2
  have hn : R.double.facePerm (d, false) ∈ Γ := by
    rw [R.double_face_false]
    exact hL.pairs d ha
  have h1 : R.double.faceReturn Γ (d, false) = R.double.facePerm (d, false) :=
    firstReturn_eq_of_trail _ ha (Trail.here hn)
  rw [R.double.cone_facePerm]
  show (R.double.faceReturn Γ)⁻¹ (R.double.facePerm (d, false)) = (d, false)
  rw [← h1, perm_inv_apply_self]

variable {w₀ : D × Bool}

theorem endSet_nonempty (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected)
    (hW : ∀ z, code z < W) (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y)
    {u a : D × Bool} (ha : a ∈ t.startOfBag code W Γ u) (hn : 4 ≤ t.npOf Γ u) :
    (t.endSet fid Γ u a).Nonempty := by
  classical
  obtain ⟨y, hf, h1, _⟩ := exists_end hL hR hc hW ha hn
  obtain ⟨hmem, _⟩ := mem_argminF.1 ha
  have hau' : R.Same Γ u a := mem_dartsOf.1 (Finset.mem_filter.1 hmem).1
  have hf' := (fconnect_inv_iff _).1 hf
  refine ⟨y, Finset.mem_filter.2 ⟨mem_dartsOf.2 (Same.trans hau' ?_), ?_, h1⟩⟩
  · exact (R.double.cone_gcomp_iff Γ _ _).1 ((R.double.cone Γ).toHypermap.gcomp_of_cface hf')
  · exact ((hfid _ _).2 (R.double.fconnect_face_of_cone Γ hf')).symm

/-- The two darts of the cut of a large bag. -/
theorem end_spec (hL₀ : t.IsLevel {w₀}) (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (hR : R.Planar)
    (hc : R.Connected) (hW : ∀ z, code z < W)
    (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y)
    {u a y : D × Bool} (ha : a ∈ t.startOfBag code W Γ u) (hn : 4 ≤ t.npOf Γ u)
    (hy : y ∈ argminF (t.endSet fid Γ u a) (t.endVal code W Γ a)) :
    a ≠ y ∧ R.Same Γ u a ∧ R.Same Γ u y ∧ fconnect R.double.facePerm a y ∧
      fconnect (⇑(R.double.cone Γ).facePerm⁻¹) a y ∧
      4 * mass (t.tourL Γ) (t.marks Γ) a y + 2 ≤ 3 * t.npOf Γ u ∧
      4 * mass (t.tourL Γ) (t.marks Γ) y a + 2 ≤ 3 * t.npOf Γ u := by
  classical
  obtain ⟨y', hf', h1', h2'⟩ := exists_end hL hR hc hW ha hn
  obtain ⟨hmem, _⟩ := mem_argminF.1 ha
  have hau' : R.Same Γ u a := mem_dartsOf.1 (Finset.mem_filter.1 hmem).1
  have hf'' := (fconnect_inv_iff _).1 hf'
  have hy'mem : y' ∈ t.endSet fid Γ u a := by
    refine Finset.mem_filter.2 ⟨mem_dartsOf.2 (Same.trans hau' ?_), ?_, h1'⟩
    · exact (R.double.cone_gcomp_iff Γ _ _).1 ((R.double.cone Γ).toHypermap.gcomp_of_cface hf'')
    · exact ((hfid _ _).2 (R.double.fconnect_face_of_cone Γ hf'')).symm
  obtain ⟨hymem, hymin⟩ := mem_argminF.1 hy
  obtain ⟨huy, hfy, hmy⟩ := Finset.mem_filter.1 hymem
  have huy' : R.Same Γ u y := mem_dartsOf.1 huy
  have hle := lex_le (hymin y' hy'mem) (hW y')
  have hd : ¬ (a ∈ Γ ∧ a.2 = false) := by
    rintro ⟨h3, h4⟩
    have h5 := eq_of_fconnect_of_fixed (cone_face_digon hL h3 h4) hf''
    rw [h5, mass_self] at h1'
    omega
  have hay : fconnect R.double.facePerm a y := (hfid _ _).1 hfy.symm
  have hfc := fconnect_cone_face hL₀ hL hw hR hc (Same.trans (Same.symm hau') huy') hay hd
  have hS := hL.spanForest hR hc
  have hcyc := cycMass_eq_npOf (t := t) hL hR hc a
  have hnp := npOf_congr (t := t) hau'
  have h6 : cycMass (t.tourL Γ) (t.marks Γ) a + 2 ≤ 4 * mass (t.tourL Γ) (t.marks Γ) a y := by
    rw [hcyc, ← hnp]
    exact hmy
  have h7 : 4 * mass (t.tourL Γ) (t.marks Γ) a y + 2 ≤ 3 * cycMass (t.tourL Γ) (t.marks Γ) a := by
    rw [hcyc, ← hnp]
    omega
  obtain ⟨hne, h8⟩ := hS.crossing_cut hfc h6 h7
  refine ⟨hne, hau', huy', hay, hfc, by omega, ?_⟩
  rw [hnp, ← hcyc]
  exact h8

theorem selOf_same {u z : D × Bool} (hz : z ∈ t.selOf code W fid Γ u) : R.Same Γ u z := by
  classical
  unfold selOf at hz
  split_ifs at hz with h0 h4
  · simp at hz
  · exact mem_dartsOf.1 (Finset.mem_filter.1 (mem_argminF.1 hz).1).1
  · rcases Finset.mem_union.1 hz with h | h
    · exact mem_dartsOf.1 (Finset.mem_filter.1 (mem_argminF.1 h).1).1
    · obtain ⟨a, ha, hy⟩ := Finset.mem_biUnion.1 h
      exact mem_dartsOf.1 (Finset.mem_filter.1 (mem_argminF.1 hy).1).1

theorem card_selOf_le (hinj : Function.Injective code) (hW : ∀ z, code z < W) (u : D × Bool) :
    (t.selOf code W fid Γ u).card ≤ 2 := by
  classical
  unfold selOf
  split_ifs with h0 h4
  · simp
  · have := card_argminF_le (S := t.smallSet Γ u) (f := code) fun _ _ _ _ e => hinj e
    omega
  · have hA : (t.startOfBag code W Γ u).card ≤ 1 := by
      refine card_argminF_le fun z _ z' _ e => hinj ?_
      have hm : ∀ z, t.startVal code W Γ z % W = code z := fun z => by
        unfold startVal
        split_ifs <;> exact lex_mod (hW z)
      rw [← hm z, ← hm z', e]
    have hB : ((t.startOfBag code W Γ u).biUnion fun a =>
        argminF (t.endSet fid Γ u a) (t.endVal code W Γ a)).card ≤ 1 := by
      refine (Finset.card_biUnion_le_card_mul _ _ 1 fun a _ => ?_).trans (by omega)
      refine card_argminF_le fun z _ z' _ e => hinj ?_
      have hm : ∀ z, t.endVal code W Γ a z % W = code z := fun z => lex_mod (hW z)
      rw [← hm z, ← hm z', e]
    have := Finset.card_union_le (t.startOfBag code W Γ u)
      ((t.startOfBag code W Γ u).biUnion fun a =>
        argminF (t.endSet fid Γ u a) (t.endVal code W Γ a))
    omega

/-- The rule gives a cut. -/
theorem isCut_sel (hL₀ : t.IsLevel {w₀}) (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (hR : R.Planar)
    (hc : R.Connected) (hinj : Function.Injective code) (hW : ∀ z, code z < W)
    (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y) :
    t.IsCut Γ (t.sel code W fid Γ) := by
  classical
  have hsame : ∀ {u z}, z ∈ t.selOf code W fid Γ u → R.Same Γ u z := selOf_same
  have hA : ∀ u, 4 ≤ t.npOf Γ u → ∃ a y, a ∈ t.selOf code W fid Γ u ∧ y ∈ t.selOf code W fid Γ u ∧
      a ∈ t.startOfBag code W Γ u ∧ y ∈ argminF (t.endSet fid Γ u a) (t.endVal code W Γ a) := by
    intro u hn
    obtain ⟨a, ha⟩ := argminF_nonempty (f := t.startVal code W Γ) (startSet_nonempty hL hc u)
    obtain ⟨y, hy⟩ := argminF_nonempty (f := t.endVal code W Γ a)
      (endSet_nonempty hL hR hc hW hfid ha hn)
    have hsel : t.selOf code W fid Γ u = t.startOfBag code W Γ u ∪
        (t.startOfBag code W Γ u).biUnion fun a =>
          argminF (t.endSet fid Γ u a) (t.endVal code W Γ a) := by
      unfold selOf
      rw [if_neg (by omega), if_neg (by omega)]
    refine ⟨a, y, ?_, ?_, ha, hy⟩
    · rw [hsel]
      exact Finset.mem_union_left _ ha
    · rw [hsel]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, hy⟩)
  have hpair : ∀ d, (d, false) ∈ t.sel code W fid Γ →
      (R.rev d, false) ∈ t.next Γ (t.sel code W fid Γ) := by
    intro d hd
    by_cases hdΓ : (d, false) ∈ Γ
    · exact subset_next _ _ (hL.pairs d hdΓ)
    have hd' := hd
    obtain ⟨u, hu⟩ := mem_sel.1 hd
    unfold selOf at hu
    split_ifs at hu with h0 h4
    · simp at hu
    · obtain ⟨v, hv, he⟩ := (Finset.mem_filter.1 (mem_argminF.1 hu).1).2
      have e : (R.rev d, false) = t.c0 v := by
        have := congrArg Prod.fst he
        simp only [r0] at this
        simp [c0, this]
      rw [e]
      refine mem_next.2 (Or.inr ⟨_, hd', Or.inr (mem_railsUp.2 ⟨v, hv, ?_, Or.inr rfl⟩)⟩)
      rw [he, t.vertM_r0 (hv.ne_root hL)]
      exact Anc.refl
    · have hn : 4 ≤ t.npOf Γ u := by omega
      have hin : ∀ z, z ∈ t.selOf code W fid Γ u → z ∈ t.sel code W fid Γ := fun z hz =>
        mem_sel.2 ⟨u, hz⟩
      have hselOf : t.selOf code W fid Γ u = t.startOfBag code W Γ u ∪
          (t.startOfBag code W Γ u).biUnion fun a =>
            argminF (t.endSet fid Γ u a) (t.endVal code W Γ a) := by
        unfold selOf
        rw [if_neg h0, if_neg h4]
      rcases Finset.mem_union.1 hu with h | h
      · obtain ⟨y, hy⟩ := argminF_nonempty (f := t.endVal code W Γ (d, false))
          (endSet_nonempty hL hR hc hW hfid h hn)
        obtain ⟨hne, -, -, hay, -⟩ := end_spec hL₀ hL hw hR hc hW hfid h hn hy
        rcases fconnect_digon hay with rfl | rfl
        · exact (hne rfl).elim
        · refine mem_next.2 (Or.inr ⟨_, hin _ ?_, Or.inl rfl⟩)
          rw [hselOf]
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(d, false), h, hy⟩)
      · obtain ⟨a, ha, hy⟩ := Finset.mem_biUnion.1 h
        obtain ⟨hne, -, -, hay, -⟩ := end_spec hL₀ hL hw hR hc hW hfid ha hn hy
        have hya : fconnect R.double.facePerm (d, false) a :=
          fconnect_sym R.double.facePerm.injective _ _ hay
        rcases fconnect_digon hya with rfl | rfl
        · exact (hne rfl).elim
        · refine mem_next.2 (Or.inr ⟨_, hin _ ?_, Or.inl rfl⟩)
          rw [hselOf]
          exact Finset.mem_union_left _ ha
  have hL' : t.IsLevel (t.next Γ (t.sel code W fid Γ)) := hL.next hpair
  refine ⟨hpair, fun u => ?_, fun u hu => ?_⟩
  · refine (Finset.card_le_card (t := t.selOf code W fid Γ u) fun z hz => ?_).trans
      (card_selOf_le hinj hW u)
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
    obtain ⟨u', hu'⟩ := mem_sel.1 hz1
    have h1 : R.Same Γ u' u := Same.trans (hsame hu') (Same.symm hz2)
    rwa [← selOf_congr h1]
  · by_cases hn : 4 ≤ t.npOf Γ u
    · obtain ⟨a, y, h1, h2, ha, hy⟩ := hA u hn
      obtain ⟨hne, hua, huy, -, hfc, h3, h4⟩ := end_spec hL₀ hL hw hR hc hW hfid ha hn hy
      have hnp := npOf_congr (t := t) hua
      refine (npOf_balance (t := t) hL hR hc hne hfc hL' ?_ ?_ (subset_next _ _) (Same.symm hua) ?_ ?_).trans
        (by rw [hnp])
      · exact mem_next.2 (Or.inr ⟨a, mem_sel.2 ⟨u, h1⟩, Or.inl rfl⟩)
      · exact mem_next.2 (Or.inr ⟨y, mem_sel.2 ⟨u, h2⟩, Or.inl rfl⟩)
      · rwa [← hnp]
      · rwa [← hnp]
    · -- a small bag
      obtain ⟨z, hz⟩ := Finset.card_pos.1 hu
      obtain ⟨hzm, huz⟩ := Finset.mem_filter.1 hz
      obtain ⟨v, hv, hzv⟩ := t.mem_marks.1 hzm
      have hvne := hv.ne_root hL
      have hzv' : t.vertM z = v ∨ t.vertM z = t.par v := by
        rcases hzv with rfl | rfl
        · exact Or.inl (t.vertM_c1 hvne)
        · exact Or.inr (t.vertM_c0 v)
      have huc1 : R.Same Γ u (t.c1 v) := by
        rcases hzv with rfl | rfl
        · exact huz
        · have h1 : R.Same Γ (t.c0 v) (t.c1 v) := by
            have := same_rev (R := R) Γ (t.c0 v)
            rwa [t.rev_c0] at this
          exact Same.trans huz h1
      have hur0 : R.Same Γ u (t.r0 v) :=
        Same.trans huc1 (hv.gcomp_rails hL (t.vertM_c1 hvne)).1
      have huc0 : R.Same Γ u (t.c0 v) :=
        Same.trans huc1 (hv.gcomp_rails hL (t.vertM_c1 hvne)).2
      have hSm : (t.smallSet Γ u).Nonempty :=
        ⟨t.r0 v, Finset.mem_filter.2 ⟨mem_dartsOf.2 hur0, v, hv, rfl⟩⟩
      obtain ⟨c, hcmem⟩ := argminF_nonempty (f := code) hSm
      obtain ⟨w, hw', hcw⟩ := (Finset.mem_filter.1 (mem_argminF.1 hcmem).1).2
      have huc : R.Same Γ u c := mem_dartsOf.1 (Finset.mem_filter.1 (mem_argminF.1 hcmem).1).1
      have hsel : c ∈ t.sel code W fid Γ := by
        refine mem_sel.2 ⟨u, ?_⟩
        unfold selOf
        rw [if_neg (by omega), if_pos (by omega)]
        exact hcmem
      have hwne := hw'.ne_root hL
      have hnotNP : ¬ t.NP (t.next Γ (t.sel code W fid Γ)) w := fun h =>
        h c (mem_next.2 (Or.inr ⟨c, hsel, Or.inl rfl⟩)) (by rw [hcw]; exact t.vertM_r0 hwne)
      -- the two marks of `w` lie in the bag and vanish
      have huw : R.Same Γ u (t.c1 w) := by
        have h1 := hw'.gcomp_rails hL (t.vertM_c1 hwne)
        rw [hcw] at huc
        exact Same.trans huc (Same.symm h1.1)
      have huw0 : R.Same Γ u (t.c0 w) :=
        Same.trans huw (hw'.gcomp_rails hL (t.vertM_c1 hwne)).2
      have hsub : (t.marks (t.next Γ (t.sel code W fid Γ))).filter
          ((R.double.split (t.next Γ (t.sel code W fid Γ))).toHypermap.gcomp u) ⊆
          (((t.marks Γ).filter ((R.double.split Γ).toHypermap.gcomp u)).erase (t.c1 w)).erase
            (t.c0 w) := by
        intro y hy
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
        obtain ⟨x, hx, hxy⟩ := t.mem_marks.1 hy1
        have hxne := hx.ne_root hL'
        have hxw : x ≠ w := fun e => hnotNP (e ▸ hx)
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2
          ⟨marks_mono (subset_next _ _) hy1, gcomp_split_mono (subset_next _ _) hy2⟩⟩⟩
        · rcases hxy with rfl | rfl
          · exact fun e => c1_ne_c0 _ _ e
          · intro e
            have h5 : R.rev (t.up x) = R.rev (t.up w) := congrArg Prod.fst e
            exact hxw (t.up_inj hxne hwne (R.rev_injective h5))
        · rcases hxy with rfl | rfl
          · intro e
            exact hxw (t.up_inj hxne hwne (congrArg Prod.fst e))
          · exact fun e => c1_ne_c0 _ _ e.symm
      have hcard := Finset.card_le_card hsub
      have hm1 : t.c1 w ∈ (t.marks Γ).filter ((R.double.split Γ).toHypermap.gcomp u) :=
        Finset.mem_filter.2 ⟨t.mem_marks.2 ⟨w, hw', Or.inl rfl⟩, huw⟩
      have hm0 : t.c0 w ∈ ((t.marks Γ).filter ((R.double.split Γ).toHypermap.gcomp u)).erase
          (t.c1 w) :=
        Finset.mem_erase.2 ⟨fun e => c1_ne_c0 _ _ e.symm,
          Finset.mem_filter.2 ⟨t.mem_marks.2 ⟨w, hw', Or.inr rfl⟩, huw0⟩⟩
      rw [Finset.card_erase_of_mem hm0, Finset.card_erase_of_mem hm1] at hcard
      have hpos : 2 ≤ ((t.marks Γ).filter ((R.double.split Γ).toHypermap.gcomp u)).card := by
        have := Finset.card_pos.2 ⟨_, hm0⟩
        rw [Finset.card_erase_of_mem hm1] at this
        omega
      have h1 : t.npOf (t.next Γ (t.sel code W fid Γ)) u + 2 ≤ t.npOf Γ u := by
        unfold npOf
        omega
      omega

variable (t) in
/-- The levels given by the rule. -/
noncomputable def levelSeq (code : D × Bool → ℕ) (W : ℕ) (fid : D × Bool → ℕ) (w₀ : D × Bool) :
    ℕ → Finset (D × Bool)
  | 0 => {w₀}
  | d + 1 => t.next (levelSeq code W fid w₀ d) (t.sel code W fid (levelSeq code W fid w₀ d))

theorem isLevel_singleton (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) : t.IsLevel {w₀} where
  root_mem := ⟨w₀, Finset.mem_singleton_self _, h₀⟩
  rails := fun z hz hr => by
    obtain rfl := Finset.mem_singleton.1 hz
    exact (hr h₀).elim
  pairs := fun d hd => by
    obtain rfl := Finset.mem_singleton.1 hd
    simp at h₁
  skel := fun x hx y hy => by
    obtain rfl := Finset.mem_singleton.1 hx
    obtain rfl := Finset.mem_singleton.1 hy
    exact connect_refl _

/-- **The levels of the rule are a decomposition.** -/
theorem decomp_levelSeq (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (hR : R.Planar)
    (hc : R.Connected) (hinj : Function.Injective code) (hW : ∀ z, code z < W)
    (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y) :
    t.Decomp w₀ (t.levelSeq code W fid w₀)
      (fun d => t.sel code W fid (t.levelSeq code W fid w₀ d)) := by
  have hL₀ := isLevel_singleton (t := t) h₀ h₁
  have hall : ∀ d, t.IsLevel (t.levelSeq code W fid w₀ d) ∧ w₀ ∈ t.levelSeq code W fid w₀ d := by
    intro d
    induction d with
    | zero => exact ⟨hL₀, Finset.mem_singleton_self _⟩
    | succ d ih =>
      obtain ⟨hL, hw⟩ := ih
      have hcut := isCut_sel hL₀ hL hw hR hc hinj hW hfid
      exact ⟨hL.next hcut.pair, subset_next _ _ hw⟩
  exact ⟨h₀, h₁, rfl, fun _ => rfl,
    fun d => isCut_sel hL₀ (hall d).1 (hall d).2 hR hc hinj hW hfid⟩

end Rule

end RootedTree

end RotSystem

end SsspFlow
