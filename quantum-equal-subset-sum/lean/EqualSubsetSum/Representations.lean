import EqualSubsetSum.Validity
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function

/-!
# Lemma 2: the representations of `D`

A partition is good if `D` has exactly `ν l d` coordinates of value `d` on each label `l`. The
free coordinates `F` are the `A`-coordinates with `D = 0`. The pairs `(X, Y) ∈ 𝒳 × 𝒴` with
`X - Y = D` are in bijection with the subsets of `F` of size `f`, a subset `S` marking the free
coordinates that take `(0, 0)`. There are `Nat.choose (ν A 0) f` of them. The layout `ν` is
arbitrary, so `ν l 1` and `ν l (-1)` may differ, and the support may be odd.
-/

open Finset

namespace EqualSubsetSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `L` is good for `D` and the layout `ν`, and `D` has entries in `{-1, 0, 1}`. -/
structure Good (L : ι → Label) (ν : Layout) (D : ι → ℤ) : Prop where
  trinary : Trinary D
  neg : ∀ l, cnt L l (-1) D = ν l (-1)
  zero : ∀ l, cnt L l 0 D = ν l 0
  pos : ∀ l, cnt L l 1 D = ν l 1

omit [DecidableEq ι] in
/-- Every labeling is good for the layout of its own counts. So `Good` is satisfiable for every `D`
over `{-1, 0, 1}`, at odd support and with `ν l 1 ≠ ν l (-1)` included. -/
theorem good_cnt (L : ι → Label) {D : ι → ℤ} (hD : Trinary D) :
    Good L (fun l d => cnt L l d D) D :=
  ⟨hD, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The free coordinates: label `A` and `D = 0`. -/
def free (L : ι → Label) (D : ι → ℤ) : Finset ι := {i | L i = .A ∧ D i = 0}

omit [DecidableEq ι] in
theorem card_free {L : ι → Label} {ν : Layout} {D : ι → ℤ} (h : Good L ν D) :
    #(free L D) = ν .A 0 := h.zero .A

/-- The vector `X` forced by `D` and a choice `S` of free coordinates. -/
def repX (L : ι → Label) (D : ι → ℤ) (S : Finset ι) (i : ι) : ℤ :=
  match L i with
  | .A => if D i = 1 then 1 else if D i = -1 then 0 else if i ∈ S then 0 else 1
  | .B => D i + 1
  | .C => 1

/-- The pair of vectors forced by `D` and `S`. -/
def repOf (L : ι → Label) (D : ι → ℤ) (S : Finset ι) : (ι → ℤ) × (ι → ℤ) :=
  (repX L D S, repX L D S - D)

/-! ## The forced vectors have the required types -/

omit [Fintype ι] in
theorem repX_A {L : ι → Label} {D : ι → ℤ} {S : Finset ι} {i : ι} (h : L i = .A) :
    repX L D S i = if D i = 1 then 1 else if D i = -1 then 0 else if i ∈ S then 0 else 1 := by
  simp [repX, h]

omit [Fintype ι] in
theorem repX_B {L : ι → Label} {D : ι → ℤ} {S : Finset ι} {i : ι} (h : L i = .B) :
    repX L D S i = D i + 1 := by
  simp [repX, h]

omit [Fintype ι] in
theorem repX_C {L : ι → Label} {D : ι → ℤ} {S : Finset ι} {i : ι} (h : L i = .C) :
    repX L D S i = 1 := by
  simp [repX, h]

omit [DecidableEq ι] in
/-- Two vectors that agree in where they take given values have equal counts. -/
theorem cnt_congr {L : ι → Label} {l : Label} {v w : ℤ} {X Z : ι → ℤ}
    (h : ∀ i, L i = l → (X i = v ↔ Z i = w)) : cnt L l v X = cnt L l w Z := by
  unfold cnt
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (h i h1).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (h i h1).mpr h2⟩

variable {L : ι → Label} {ν : Layout} {D : ι → ℤ} {S : Finset ι}

omit [Fintype ι] in
theorem repX_alpha (L : ι → Label) (D : ι → ℤ) (S : Finset ι) (hD : Trinary D) :
    AlphaX L (repX L D S) where
  onA i h := by
    rw [repX_A h]
    split_ifs <;> simp
  onB i h := by
    rw [repX_B h]
    rcases hD i with h' | h' | h' <;> simp [h']
  onC i h := repX_C h

omit [Fintype ι] in
theorem repY_alpha (L : ι → Label) (D : ι → ℤ) (S : Finset ι) (hD : Trinary D) :
    AlphaY L (repX L D S - D) where
  onA i h := by
    simp only [Pi.sub_apply]
    rw [repX_A h]
    rcases hD i with h' | h' | h' <;> simp [h']
    exact em _
  onB i h := by
    simp only [Pi.sub_apply]
    rw [repX_B h]
    ring
  onC i h := by
    simp only [Pi.sub_apply]
    rw [repX_C h]
    rcases hD i with h' | h' | h' <;> simp [h']

/-- `S ⊆ F` and `F \ S` have the sizes that the types require. -/
theorem card_free_sdiff (hD : Good L ν D) (hS : S ∈ powersetCard ν.f (free L D)) :
    #(free L D \ S) = ν.f' := by
  rw [mem_powersetCard] at hS
  rw [card_sdiff_of_subset hS.1, hS.2, card_free hD, Layout.f']

/-- The zeros of `X` on `A`, or of `Y`, split into a forced part and the free part `S`. -/
theorem cnt_split {Z : ι → ℤ} {d : ℤ} (T : Finset ι) {v : ℤ}
    (hT : ∀ i ∈ T, L i = .A ∧ D i = 0)
    (hd : d ≠ 0)
    (h : ∀ i, L i = .A → (Z i = v ↔ D i = d ∨ i ∈ T)) :
    cnt L .A v Z = cnt L .A d D + #T := by
  have : ({i | L i = .A ∧ Z i = v} : Finset ι) = ({i | L i = .A ∧ D i = d} : Finset ι) ∪ T := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (h i h1).mp h2 with h3 | h3
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr h3
    · rintro (⟨h1, h2⟩ | h3)
      · exact ⟨h1, (h i h1).mpr (Or.inl h2)⟩
      · have h1 := (hT i h3).1
        exact ⟨h1, (h i h1).mpr (Or.inr h3)⟩
  unfold cnt
  rw [this, card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [mem_filter, mem_univ, true_and] at hi
  have := (hT i hi').2
  omega

/-- **Forced types, `X`.** The vector `X` forced by `D` and a subset of `F` of size `f` lies in
`𝒳`. -/
theorem repX_isX (hD : Good L ν D) (hS : S ∈ powersetCard ν.f (free L D)) :
    IsX L ν (repX L D S) := by
  have hsub : ∀ i ∈ S, L i = .A ∧ D i = 0 := fun i hi => by
    have := (mem_powersetCard.mp hS).1 hi
    simpa [free] using this
  have hcard := (mem_powersetCard.mp hS).2
  refine ⟨repX_alpha L D S hD.trinary, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cnt_split S hsub (d := -1) (by norm_num), hD.neg, hcard]
    intro i hi
    rw [repX_A hi]
    by_cases h1 : D i = 1 <;> by_cases h2 : D i = -1 <;> by_cases h3 : i ∈ S <;> simp_all
  · rw [cnt_split (free L D \ S) (fun i hi => by
      have := (mem_sdiff.mp hi).1
      simpa [free] using this) (d := 1) (by norm_num), hD.pos, card_free_sdiff hD hS]
    intro i hi
    rw [repX_A hi]
    simp only [mem_sdiff, free, mem_filter, mem_univ, true_and, hi]
    have := hD.trinary i
    by_cases h1 : D i = 1 <;> by_cases h2 : D i = -1 <;> by_cases h3 : i ∈ S <;> simp_all
  · rw [← hD.neg]
    refine cnt_congr fun i hi => ?_
    rw [repX_B hi]
    omega
  · rw [← hD.zero]
    refine cnt_congr fun i hi => ?_
    rw [repX_B hi]
    omega
  · rw [← hD.pos]
    refine cnt_congr fun i hi => ?_
    rw [repX_B hi]
    omega

/-- **Forced types, `Y`.** The vector `Y = X - D` forced by `D` and a subset of `F` of size `f` lies
in `𝒴`. -/
theorem repY_isY (hD : Good L ν D) (hS : S ∈ powersetCard ν.f (free L D)) :
    IsY L ν (repX L D S - D) := by
  have hsub : ∀ i ∈ S, L i = .A ∧ D i = 0 := fun i hi => by
    have := (mem_powersetCard.mp hS).1 hi
    simpa [free] using this
  have hcard := (mem_powersetCard.mp hS).2
  refine ⟨repY_alpha L D S hD.trinary, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cnt_split S hsub (d := 1) (by norm_num), hD.pos, hcard]
    intro i hi
    simp only [Pi.sub_apply]
    rw [repX_A hi]
    have := hD.trinary i
    by_cases h1 : D i = 1 <;> by_cases h2 : D i = -1 <;> by_cases h3 : i ∈ S <;> simp_all
  · rw [cnt_split (free L D \ S) (fun i hi => by
      have := (mem_sdiff.mp hi).1
      simpa [free] using this) (d := -1) (by norm_num), hD.neg, card_free_sdiff hD hS]
    intro i hi
    simp only [Pi.sub_apply]
    rw [repX_A hi]
    simp only [mem_sdiff, free, mem_filter, mem_univ, true_and, hi]
    have := hD.trinary i
    by_cases h1 : D i = 1 <;> by_cases h2 : D i = -1 <;> by_cases h3 : i ∈ S <;> simp_all
  · rw [← hD.pos]
    refine cnt_congr fun i hi => ?_
    simp only [Pi.sub_apply]
    rw [repX_C hi]
    omega
  · rw [← hD.zero]
    refine cnt_congr fun i hi => ?_
    simp only [Pi.sub_apply]
    rw [repX_C hi]
    omega
  · rw [← hD.neg]
    refine cnt_congr fun i hi => ?_
    simp only [Pi.sub_apply]
    rw [repX_C hi]
    omega

/-! ## The bijection -/

open scoped Classical in
/-- The representations of `D`: the pairs in `𝒳 × 𝒴` with `X - Y = D`. -/
noncomputable def reps (L : ι → Label) (ν : Layout) (D : ι → ℤ) :
    Finset ((ι → ℤ) × (ι → ℤ)) :=
  (listX L ν ×ˢ listY L ν).filter fun p => p.1 - p.2 = D

@[simp] theorem mem_reps {p : (ι → ℤ) × (ι → ℤ)} :
    p ∈ reps L ν D ↔ IsX L ν p.1 ∧ IsY L ν p.2 ∧ p.1 - p.2 = D := by
  simp [reps, and_assoc]

theorem repOf_mem (hD : Good L ν D) (hS : S ∈ powersetCard ν.f (free L D)) :
    repOf L D S ∈ reps L ν D := by
  rw [mem_reps]
  exact ⟨repX_isX hD hS, repY_isY hD hS, by simp [repOf]⟩

omit [DecidableEq ι] in
/-- On a representation, `D` forces everything outside the free coordinates. -/
theorem forced_of_mem {X Y : ι → ℤ} (hX : IsX L ν X) (hY : IsY L ν Y)
    (hXY : X - Y = D) (i : ι) :
    (L i = .A → (X i = 0 ∨ X i = 1) ∧ (D i = 1 → X i = 1) ∧ (D i = -1 → X i = 0)) ∧
      (L i = .B → X i = D i + 1) ∧ (L i = .C → X i = 1) := by
  have hd : X i - Y i = D i := by rw [← hXY]; rfl
  refine ⟨fun h => ?_, fun h => ?_, fun h => hX.onC i h⟩
  · have h1 := hX.onA i h
    have h2 := hY.onA i h
    refine ⟨h1, fun h3 => ?_, fun h3 => ?_⟩ <;> omega
  · have := hY.onB i h
    omega

/-- **Lemma 2, the bijection.** For a good partition, `S ↦ (X, Y)` is a bijection from the subsets
of the free coordinates of size `f` onto the representations of `D`. -/
theorem repOf_bijOn (hD : Good L ν D) :
    Set.BijOn (repOf L D) (powersetCard ν.f (free L D) : Finset (Finset ι)) (reps L ν D) := by
  refine ⟨fun S hS => repOf_mem hD hS, ?_, ?_⟩
  · intro S hS S' hS' h
    have hX : repX L D S = repX L D S' := congrArg Prod.fst h
    have key : ∀ T ∈ powersetCard ν.f (free L D), ∀ i, i ∈ T ↔ i ∈ free L D ∧ repX L D T i = 0 := by
      intro T hT i
      have hsub := (mem_powersetCard.mp hT).1
      constructor
      · intro hi
        have h1 := hsub hi
        have h2 : L i = .A ∧ D i = 0 := by simpa [free] using h1
        refine ⟨h1, ?_⟩
        rw [repX_A h2.1]
        simp [h2.2, hi]
      · rintro ⟨h1, h2⟩
        have h3 : L i = .A ∧ D i = 0 := by simpa [free] using h1
        rw [repX_A h3.1] at h2
        by_contra hi
        simp [h3.2, hi] at h2
    ext i
    rw [key S hS, key S' hS', hX]
  · rintro ⟨X, Y⟩ hp
    have hp' := mem_reps.mp hp
    obtain ⟨hX, hY, hXY⟩ := hp'
    simp only at hX hY hXY
    set T : Finset ι := (free L D).filter fun i => X i = 0 with hT
    have hforced := forced_of_mem hX hY hXY
    have hTcard : #T = ν.f := by
      have h1 := hX.a0
      rw [cnt_split T (d := -1) (fun i hi => by
        have := (mem_filter.mp hi).1
        simpa [free] using this) (by norm_num), hD.neg] at h1
      · omega
      · intro i hi
        have hf := (hforced i).1 hi
        simp only [hT, mem_filter, free, mem_univ, true_and]
        have htr := hD.trinary i
        constructor
        · intro h0
          rcases htr with h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨⟨hi, h2⟩, h0⟩
          · have := hf.2.1 h2
            omega
        · rintro (h2 | ⟨_, h2⟩)
          · exact hf.2.2 h2
          · exact h2
    have hTmem : T ∈ powersetCard ν.f (free L D) :=
      mem_powersetCard.mpr ⟨filter_subset _ _, hTcard⟩
    refine ⟨T, hTmem, ?_⟩
    have hrep : repX L D T = X := by
      funext i
      have hf := hforced i
      cases hl : L i with
      | A =>
        rw [repX_A hl]
        have hA := hf.1 hl
        rcases hD.trinary i with h2 | h2 | h2
        · simp [h2, hA.2.2 h2]
        · have hmem : i ∈ T ↔ X i = 0 := by
            simp [hT, free, hl, h2]
          by_cases h0 : X i = 0
          · simp [h2, hmem.mpr h0, h0]
          · have h1 : X i = 1 := hA.1.resolve_left h0
            have : i ∉ T := fun h => h0 (hmem.mp h)
            simp [h2, this, h1]
        · simp [h2, hA.2.1 h2]
      | B => rw [repX_B hl, hf.2.1 hl]
      | C => rw [repX_C hl, hf.2.2 hl]
    have hY' : X - D = Y := by rw [← hXY, sub_sub_cancel]
    simp only [repOf, hrep, hY']

/-- **Lemma 2, the count.** For a good partition there are `Nat.choose (ν A 0) f` representations. -/
theorem card_reps (hD : Good L ν D) :
    #(reps L ν D) = (ν .A 0).choose ν.f := by
  have h := repOf_bijOn hD
  have := Finset.card_nbij (repOf L D) h.mapsTo h.injOn h.surjOn
  rw [← this, card_powersetCard, card_free hD]

/-! ## Values of representations -/

/-- A representation of a solution has `⟨X,y⟩ = ⟨Y,y⟩`. -/
theorem value_eq {y : ι → ℤ} {p : (ι → ℤ) × (ι → ℤ)} (hp : p ∈ reps L ν D)
    (hy : dot D y = 0) : dot p.1 y = dot p.2 y := by
  have := (mem_reps.mp hp).2.2
  have h2 := dot_sub p.1 p.2 y
  rw [this, hy] at h2
  omega

omit [DecidableEq ι] in
/-- Under `2 z < n`, with `z` the zeros of `D`, the free coordinates are fewer than the support.
This is the inequality `|F| ≤ z < n - z` behind the distinctness of the values. -/
theorem card_free_lt_supp (h : 2 * #({i | D i = 0} : Finset ι) < Fintype.card ι) :
    #(free L D) < #(supp D) := by
  have h1 : #(free L D) ≤ #({i | D i = 0} : Finset ι) := by
    apply card_le_card
    intro i hi
    simp only [free, mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2
  have h2 : #({i | D i = 0} : Finset ι) + #(supp D) = Fintype.card ι := by
    have := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => D i = 0)
    simpa [supp] using this
  omega

/-- **Lemma 2, distinctness.** Under minimality of `supp D` and `|F| < |supp D|`, the values
`⟨X,y⟩` of the representations are pairwise distinct. Two representations with equal value differ
only on `F`, which gives a solution with support in `F`. -/
theorem value_injOn {y : ι → ℤ} (hD : Good L ν D) (hmin : MinimalSolution D y)
    (hF : #(free L D) < #(supp D)) :
    Set.InjOn (fun p : (ι → ℤ) × (ι → ℤ) => dot p.1 y) (reps L ν D) := by
  intro p hp q hq hval
  have hval' : dot p.1 y = dot q.1 y := hval
  obtain ⟨hpX, hpY, hpD⟩ := mem_reps.mp hp
  obtain ⟨hqX, hqY, hqD⟩ := mem_reps.mp hq
  have hfp := forced_of_mem hpX hpY hpD
  have hfq := forced_of_mem hqX hqY hqD
  have hsub : ∀ i, i ∉ free L D → p.1 i = q.1 i := by
    intro i hi
    have hfree : ¬(L i = .A ∧ D i = 0) := by simpa [free] using hi
    cases hl : L i with
    | A =>
      have h1 := (hfp i).1 hl
      have h2 := (hfq i).1 hl
      rcases hD.trinary i with h3 | h3 | h3
      · rw [h1.2.2 h3, h2.2.2 h3]
      · exact absurd ⟨hl, h3⟩ hfree
      · rw [h1.2.1 h3, h2.2.1 h3]
    | B => rw [(hfp i).2.1 hl, (hfq i).2.1 hl]
    | C => rw [(hfp i).2.2 hl, (hfq i).2.2 hl]
  have htri : Trinary (p.1 - q.1) := by
    intro i
    simp only [Pi.sub_apply]
    by_cases hi : i ∈ free L D
    · have hl : L i = .A := by
        have : L i = .A ∧ D i = 0 := by simpa [free] using hi
        exact this.1
      have h1 := hpX.onA i hl
      have h2 := hqX.onA i hl
      omega
    · rw [hsub i hi]
      simp
  have heq : p.1 = q.1 := by
    by_contra hne
    have hE : p.1 - q.1 ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hy : dot (p.1 - q.1) y = 0 := by rw [dot_sub, hval', sub_self]
    have h1 := hmin.minimal _ htri hE hy
    have h2 : #(supp (p.1 - q.1)) ≤ #(free L D) := by
      apply card_le_card
      intro i hi
      by_contra hni
      simp [supp, hsub i hni] at hi
    omega
  have heq2 : p.2 = q.2 := by
    have h1 : p.2 = p.1 - D := by rw [← hpD, sub_sub_cancel]
    have h2 : q.2 = q.1 - D := by rw [← hqD, sub_sub_cancel]
    rw [h1, h2, heq]
  exact Prod.ext heq heq2

/-! ## The empty label -/

/-- If `A` has no zeros of `D` then `f = 0` and `K = 1`. -/
theorem choose_of_empty (h0 : ν .A 0 = 0) : (ν .A 0).choose ν.f = 1 := by
  simp [Layout.f, h0]

/-- **Lemma 2, empty label.** If `ν A 0 = 0` there is exactly one representation, so the values are
trivially distinct, with neither minimality nor `p < 1/2`. -/
theorem value_injOn_of_empty {y : ι → ℤ} (hD : Good L ν D) (h0 : ν .A 0 = 0) :
    Set.InjOn (fun p : (ι → ℤ) × (ι → ℤ) => dot p.1 y) (reps L ν D) := by
  have hcard : #(reps L ν D) = 1 := by rw [card_reps hD, choose_of_empty h0]
  intro p hp q hq _
  exact Finset.card_le_one.mp hcard.le p hp q hq

end EqualSubsetSum
