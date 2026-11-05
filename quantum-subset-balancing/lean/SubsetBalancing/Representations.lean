import SubsetBalancing.Multinomial
import SubsetBalancing.Validity

/-!
# Lemma 2: the representations of `D`

A class is a pair `(l, e)` of a label and a value of `D`. Its symbols are the `x ∈ S` with
`x - e ∈ T`, each standing for the pair `(x, x - e)`. A labeling is good if `D` has exactly
`ν l e = ∑_x ν l x (x - e)` coordinates of value `e` on `l`, outside the pin, and `D` has the pinned
value at the pin.

A representation is a pair `(X, Y)` with `X - Y = D`, with `(c, 0)` at the pin, and with exactly
`ν l x y` coordinates of `l` carrying the pair `(x, y)`. Such a pair lies in `𝒳 × 𝒴`. On a good
labeling the representations are in bijection with the functions typed on each class, so their
number is the product over the classes of the multinomials.

The free coordinates `F` are those in classes with at least two positive `ν l x y`. Outside `F` the
pair is forced. The core of the lemma, `no_two_representations`, is abstract: it speaks of two pairs
that agree outside a set `F` with `|F| < |supp D|` and of per-coordinate labels on `F`. There the
width bound of an exchange applies, and minimality of `D` excludes two distinct pairs of equal value.
-/

open Finset

namespace SubsetBalancing

/-! ## Lemma 2, the abstract core -/

section Core

variable {ι : Type*} [Fintype ι]

/-- **Lemma 2, the bound form.** Let `D` be a solution of minimum support. If `X - Y = X' - Y' = D`,
`⟨X,y⟩ = ⟨X',y⟩`, the vectors `X` and `X'` agree outside a set `F` with `|F| < |supp D|`, and
`|X i - X' i| ≤ d` on `F`, then the two pairs are equal. -/
theorem eq_of_value_eq {d : ℤ} {D y X Y X' Y' : ι → ℤ} (hmin : MinimalSolution d D y)
    {F : Finset ι} (hF : #F < #(supp D)) (hXY : X - Y = D) (hXY' : X' - Y' = D)
    (hval : dot X y = dot X' y) (hoff : ∀ i, i ∉ F → X i = X' i)
    (hbd : ∀ i ∈ F, |X i - X' i| ≤ d) : (X, Y) = (X', Y') := by
  classical
  have heq : X = X' := by
    by_contra hne
    have hE : X - X' ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hbox : InBox d (X - X') := by
      intro i
      simp only [Pi.sub_apply]
      by_cases hi : i ∈ F
      · exact hbd i hi
      · rw [hoff i hi, sub_self, abs_zero]
        exact hmin.d_nonneg
    have hy : dot (X - X') y = 0 := by rw [dot_sub, hval, sub_self]
    have h1 := hmin.minimal _ hbox hE hy
    have h2 : #(supp (X - X')) ≤ #F := by
      apply card_le_card
      intro i hi
      by_contra hni
      simp [supp, hoff i hni] at hi
    omega
  have h1 : Y = X - D := by rw [← hXY, sub_sub_cancel]
  have h2 : Y' = X' - D := by rw [← hXY', sub_sub_cancel]
  rw [h1, h2, heq]

/-- **Lemma 2, in general form.** Let `D` be a solution of minimum support in `[-d:d]^n`. Two
representations `(X, Y)`, `(X', Y')` of `D` of equal value, with `X` and `X'` agreeing outside a set
`F` with `|F| < |supp D|`, and with `X i, X' i ∈ S` and `Y i, Y' i ∈ T` for a label `ℓ i` on each
`i ∈ F` with `S - T` inside `[-d:d]`, are equal. Nothing is asked of the coordinates outside `F`. -/
theorem no_two_representations {d : ℤ} {D y X Y X' Y' : ι → ℤ} (hmin : MinimalSolution d D y)
    {F : Finset ι} (hF : #F < #(supp D)) (hXY : X - Y = D) (hXY' : X' - Y' = D)
    (hval : dot X y = dot X' y) (hoff : ∀ i, i ∉ F → X i = X' i) (ℓ : ι → Label)
    (hℓ : ∀ i ∈ F, (ℓ i).Inside d) (hS : ∀ i ∈ F, X i ∈ (ℓ i).S ∧ X' i ∈ (ℓ i).S)
    (hT : ∀ i ∈ F, Y i ∈ (ℓ i).T ∧ Y' i ∈ (ℓ i).T) : (X, Y) = (X', Y') := by
  refine eq_of_value_eq hmin hF hXY hXY' hval hoff fun i hi => ?_
  refine Label.abs_exchange_le (hℓ i hi) (hS i hi).1 (hS i hi).2 (hT i hi).1 (hT i hi).2 ?_
  have h1 := congrFun hXY i
  have h2 := congrFun hXY' i
  simp only [Pi.sub_apply] at h1 h2
  rw [h1, h2]

end Core

variable {ι Lab : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Lab]

/-! ## Classes and goodness -/

namespace Layout

/-- The symbols of the class `(l, e)`: the `x ∈ S` with `x - e ∈ T`. -/
def cSyms (ν : Layout Lab) (l : Lab) (e : ℤ) : Finset ℤ :=
  (ν.iv l).S.filter fun x => x - e ∈ (ν.iv l).T

/-- The size `ν l e = ∑_{x - y = e} ν l x y` of the class `(l, e)`. -/
def cCount (ν : Layout Lab) (l : Lab) (e : ℤ) : ℕ := ∑ x ∈ ν.cSyms l e, ν.nu l x (x - e)

/-- The values of the label `l`: the differences of `S - T`. -/
def diffs (ν : Layout Lab) (l : Lab) : Finset ℤ :=
  ((ν.iv l).S ×ˢ (ν.iv l).T).image fun q => q.1 - q.2

omit [DecidableEq Lab] in
/-- The class size as the sum over the pairs `(x, y) ∈ S × T` with `x - y = e`. -/
theorem cCount_eq_sum_pairs (ν : Layout Lab) (l : Lab) (e : ℤ) :
    ν.cCount l e = ∑ q ∈ ((ν.iv l).S ×ˢ (ν.iv l).T).filter (fun q => q.1 - q.2 = e),
      ν.nu l q.1 q.2 := by
  unfold cCount
  refine sum_bij (fun x _ => (x, x - e)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_filter.mp hx
    simp [h1, h2]
  · intro x _ x' _ h
    exact (Prod.mk.inj h).1
  · rintro ⟨x, y⟩ hq
    simp only [mem_filter, mem_product] at hq
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    refine ⟨x, mem_filter.mpr ⟨h1, ?_⟩, ?_⟩
    · have : x - e = y := by omega
      rwa [this]
    · have : x - e = y := by omega
      simp [this]
  · intro x _
    rfl

variable [Fintype Lab]

/-- The number `K` of representations: the product over the classes `(l, e)` of the multinomial of
the counts `ν l x (x - e)`. -/
def K (ν : Layout Lab) : ℕ :=
  ∏ l, ∏ e ∈ ν.diffs l, Nat.multinomial (ν.cSyms l e) (fun x => ν.nu l x (x - e))

omit [DecidableEq Lab] in
theorem K_pos (ν : Layout Lab) : 0 < ν.K :=
  prod_pos fun _ _ => prod_pos fun _ _ => Nat.multinomial_pos _ _

/-- The classes with at least two positive counts. -/
def varying (ν : Layout Lab) : Finset (Σ _ : Lab, ℤ) :=
  (univ.sigma ν.diffs).filter fun k => 1 < #{x ∈ ν.cSyms k.1 k.2 | 0 < ν.nu k.1 x (x - k.2)}

/-- The total size of the classes with at least two positive counts, the size of `F` on a good
labeling. -/
def freeCount (ν : Layout Lab) : ℕ := ∑ k ∈ ν.varying, ν.cCount k.1 k.2

end Layout

/-- `L` is good for `D` and the layout `ν`: `D` has the pinned value at the pin, and on each label
`l`, outside the pin, it has exactly `ν l e` coordinates of value `e`. -/
structure Good (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D : ι → ℤ) : Prop where
  pin : D p.coord = p.val
  class_eq : ∀ l e, #{i | i ≠ p.coord ∧ L i = l ∧ D i = e} = ν.cCount l e

/-! ## Representations -/

/-- `(X, Y)` is a representation of `D`: the alphabets and the pin, `X - Y = D`, and exactly
`ν l x y` coordinates of `l` carry the pair `(x, y)`. -/
structure IsRep (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D X Y : ι → ℤ) : Prop where
  alphaX : AlphaX ν L p X
  alphaY : AlphaY ν L p Y
  sub : X - Y = D
  pair : ∀ l, ∀ x ∈ (ν.iv l).S, ∀ y ∈ (ν.iv l).T,
    #{i | i ≠ p.coord ∧ L i = l ∧ X i = x ∧ Y i = y} = ν.nu l x y

variable {L : ι → Lab} {ν : Layout Lab} {p : Pin ι} {D y : ι → ℤ}

/-- A representation has `X` in `𝒳`: summing the pair counts over `y` gives the type of `X`. -/
theorem IsRep.isX {X Y : ι → ℤ} (h : IsRep L ν p D X Y) : IsX ν L p X := by
  refine ⟨h.alphaX, fun l s hs => ?_⟩
  have hmaps : ∀ i ∈ ({i | i ≠ p.coord ∧ L i = l ∧ X i = s} : Finset ι), Y i ∈ (ν.iv l).T := by
    intro i hi
    obtain ⟨h1, h2, -⟩ := (mem_filter.mp hi).2
    rw [← h2]
    exact h.alphaY.mem i h1
  unfold cnt Layout.xCount
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun b hb => ?_
  rw [← h.pair l s hs b hb]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  tauto

/-- A representation has `Y` in `𝒴`: summing the pair counts over `x` gives the type of `Y`. -/
theorem IsRep.isY {X Y : ι → ℤ} (h : IsRep L ν p D X Y) : IsY ν L p Y := by
  refine ⟨h.alphaY, fun l s hs => ?_⟩
  have hmaps : ∀ i ∈ ({i | i ≠ p.coord ∧ L i = l ∧ Y i = s} : Finset ι), X i ∈ (ν.iv l).S := by
    intro i hi
    obtain ⟨h1, h2, -⟩ := (mem_filter.mp hi).2
    rw [← h2]
    exact h.alphaX.mem i h1
  unfold cnt Layout.yCount
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun b hb => ?_
  rw [← h.pair l b hb s hs]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  tauto

open scoped Classical in
/-- The set `R` of representations of `D`. -/
noncomputable def reps (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D : ι → ℤ) :
    Finset ((ι → ℤ) × (ι → ℤ)) :=
  (listX ν L p ×ˢ listY ν L p).filter fun q => IsRep L ν p D q.1 q.2

/-- `R` lies inside `𝒳 × 𝒴`. -/
@[simp] theorem mem_reps {q : (ι → ℤ) × (ι → ℤ)} :
    q ∈ reps L ν p D ↔ IsRep L ν p D q.1 q.2 := by
  simp only [reps, mem_filter, mem_product, mem_listX, mem_listY, and_iff_right_iff_imp]
  exact fun h => ⟨h.isX, h.isY⟩

/-- A representation of a solution has `⟨X,y⟩ = ⟨Y,y⟩`. -/
theorem value_eq {q : (ι → ℤ) × (ι → ℤ)} (hq : q ∈ reps L ν p D) (hy : dot D y = 0) :
    dot q.1 y = dot q.2 y := by
  have := (mem_reps.mp hq).sub
  have h2 := dot_sub q.1 q.2 y
  rw [this, hy] at h2
  omega

/-! ## The free coordinates -/

/-- The free coordinates `F`: outside the pin, in classes with at least two positive counts. -/
def free (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D : ι → ℤ) : Finset ι :=
  {i | i ≠ p.coord ∧ 1 < #{x ∈ ν.cSyms (L i) (D i) | 0 < ν.nu (L i) x (x - D i)}}

/-- On a representation, the symbol of a coordinate outside the pin belongs to its class, with a
positive count, since the coordinate itself carries the pair. -/
theorem IsRep.symbol_mem {X Y : ι → ℤ} (h : IsRep L ν p D X Y) {i : ι} (hi : i ≠ p.coord) :
    X i ∈ {x ∈ ν.cSyms (L i) (D i) | 0 < ν.nu (L i) x (x - D i)} := by
  have hS := h.alphaX.mem i hi
  have hT := h.alphaY.mem i hi
  have hY : X i - D i = Y i := by
    have := congrFun h.sub i
    simp only [Pi.sub_apply] at this
    omega
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨hS, by rwa [hY]⟩, ?_⟩
  rw [hY, ← h.pair (L i) (X i) hS (Y i) hT]
  exact card_pos.mpr ⟨i, by simp [hi]⟩

/-- **Outside `F` the pair is forced.** At the pin both vectors have the pinned value. At a coordinate
in a class with at most one positive count, there is only one symbol to take. -/
theorem forced_off_free {X Y X' Y' : ι → ℤ} (h : IsRep L ν p D X Y) (h' : IsRep L ν p D X' Y')
    {i : ι} (hi : i ∉ free L ν p D) : X i = X' i := by
  by_cases hp : i = p.coord
  · rw [hp, h.alphaX.pin, h'.alphaX.pin]
  · have hle : #{x ∈ ν.cSyms (L i) (D i) | 0 < ν.nu (L i) x (x - D i)} ≤ 1 := by
      by_contra hcon
      exact hi (mem_filter.mpr ⟨mem_univ _, hp, not_le.mp hcon⟩)
    exact card_le_one.mp hle _ (h.symbol_mem hp) _ (h'.symbol_mem hp)

/-- **Lemma 2, distinctness.** Let `D` be a solution of minimum support and every label of the layout
have `S - T` inside `[-d:d]`. If `|F| < |supp D|`, the values `⟨X,y⟩` of the representations are
pairwise distinct. -/
theorem value_injOn {d : ℤ} (hmin : MinimalSolution d D y) (hd : ν.Inside d)
    (hF : #(free L ν p D) < #(supp D)) :
    Set.InjOn (fun q : (ι → ℤ) × (ι → ℤ) => dot q.1 y) (reps L ν p D) := by
  rintro ⟨X, Y⟩ hq ⟨X', Y'⟩ hq' hval
  have hr := mem_reps.mp hq
  have hr' := mem_reps.mp hq'
  simp only at hr hr' hval
  refine no_two_representations hmin hF hr.sub hr'.sub hval (fun i hi => forced_off_free hr hr' hi)
    (fun i => ν.iv (L i)) (fun i _ => hd (L i)) (fun i hi => ?_) (fun i hi => ?_)
  · have hp : i ≠ p.coord := (mem_filter.mp hi).2.1
    exact ⟨hr.alphaX.mem i hp, hr'.alphaX.mem i hp⟩
  · have hp : i ≠ p.coord := (mem_filter.mp hi).2.1
    exact ⟨hr.alphaY.mem i hp, hr'.alphaY.mem i hp⟩

/-- **No free coordinates.** If `F` is empty there is at most one representation, so the values are
trivially distinct, with neither minimality nor a condition on the support. -/
theorem card_reps_le_one (hF : free L ν p D = ∅) : #(reps L ν p D) ≤ 1 := by
  refine card_le_one.mpr ?_
  rintro ⟨X, Y⟩ hq ⟨X', Y'⟩ hq'
  have hr := mem_reps.mp hq
  have hr' := mem_reps.mp hq'
  simp only at hr hr'
  have heq : X = X' := funext fun i => forced_off_free hr hr' (by simp [hF])
  have h1 : Y = X - D := by rw [← hr.sub, sub_sub_cancel]
  have h2 : Y' = X' - D := by rw [← hr'.sub, sub_sub_cancel]
  rw [h1, h2, heq]

/-- **Lemma 2, no free coordinates.** If `F` is empty the values are trivially distinct. -/
theorem value_injOn_of_free_empty (hF : free L ν p D = ∅) :
    Set.InjOn (fun q : (ι → ℤ) × (ι → ℤ) => dot q.1 y) (reps L ν p D) := by
  intro q hq q' hq' _
  exact card_le_one.mp (card_reps_le_one hF) q hq q' hq'

omit [DecidableEq Lab] in
/-- If all classes of a label have at most one symbol, because `S` or `T` is a single point, no
coordinate of that label is free. The two labels of the empty scheme are of this kind. -/
theorem free_eq_empty (h : ∀ l, #(ν.iv l).S ≤ 1 ∨ #(ν.iv l).T ≤ 1) : free L ν p D = ∅ := by
  unfold free
  rw [filter_eq_empty_iff]
  intro i _ hi
  have hle : #(ν.cSyms (L i) (D i)) ≤ 1 := by
    rcases h (L i) with h1 | h1
    · exact (card_filter_le _ _).trans h1
    · refine card_le_one.mpr fun a ha b hb => ?_
      have h2 := card_le_one.mp h1 _ (mem_filter.mp ha).2 _ (mem_filter.mp hb).2
      omega
  have := (card_filter_le (ν.cSyms (L i) (D i)) fun x => 0 < ν.nu (L i) x (x - D i)).trans hle
  omega

/-! ## The product formula -/

/-- The coordinates of the class `(l, e)`, outside the pin. -/
def classOf (L : ι → Lab) (p : Pin ι) (D : ι → ℤ) (k : Σ _ : Lab, ℤ) : Finset ι :=
  {i | i ≠ p.coord ∧ L i = k.1 ∧ D i = k.2}

/-- The classes of `D` are pairwise disjoint. -/
theorem classOf_disjoint (k k' : Σ _ : Lab, ℤ) (h : k ≠ k') :
    Disjoint (classOf L p D k) (classOf L p D k') := by
  refine disjoint_left.mpr fun i hi hi' => h ?_
  obtain ⟨-, h1, h2⟩ := (mem_filter.mp hi).2
  obtain ⟨-, h3, h4⟩ := (mem_filter.mp hi').2
  exact Sigma.ext (h1.symm.trans h3) (heq_of_eq (h2.symm.trans h4))

/-- On a good labeling, each coordinate outside the pin has a value among those of its label. -/
theorem Good.mem_diffs (h : Good L ν p D) {i : ι} (hi : i ≠ p.coord) : D i ∈ ν.diffs (L i) := by
  have hpos : 0 < ν.cCount (L i) (D i) := by
    rw [← h.class_eq]
    exact card_pos.mpr ⟨i, by simp [hi]⟩
  have hne : (ν.cSyms (L i) (D i)).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    simp [Layout.cCount, hcon] at hpos
  obtain ⟨x, hx⟩ := hne
  obtain ⟨h1, h2⟩ := mem_filter.mp hx
  exact mem_image.mpr ⟨(x, x - D i), mem_product.mpr ⟨h1, h2⟩, by simp⟩

section Count

variable [Fintype Lab]

/-- The base function of the count: the pinned value at the pin. -/
def pinBase (p : Pin ι) : ι → ℤ := fun i => if i = p.coord then p.val else 0

/-- The functions typed on every class of `D`. -/
def typedClasses (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D : ι → ℤ) : Finset (ι → ℤ) :=
  typedAll (classOf L p D) (fun k => ν.cSyms k.1 k.2) (fun k x => ν.nu k.1 x (x - k.2))
    (pinBase p) (univ.sigma ν.diffs)

/-- **The bijection.** On a good labeling, `X` determines `Y = X - D`, and `(X, Y) ↦ X` is a bijection
from the representations onto the functions typed on every class. -/
theorem fst_bijOn (hD : Good L ν p D) :
    Set.BijOn Prod.fst (reps L ν p D : Set ((ι → ℤ) × (ι → ℤ))) (typedClasses L ν p D) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨X, Y⟩ hq
    have hr : IsRep L ν p D X Y := mem_reps.mp hq
    refine mem_coe.mpr (mem_typedAll.mpr ⟨fun i hi => ?_, fun k _ => ⟨fun i hi => ?_, fun b hb => ?_⟩⟩)
    · by_cases hp : i = p.coord
      · simp only [pinBase, hp, ite_true]
        exact hr.alphaX.pin
      · exact absurd (by simp [classOf, hp]) (hi ⟨L i, D i⟩ (mem_sigma.mpr ⟨mem_univ _, hD.mem_diffs hp⟩))
    · obtain ⟨hp, h1, h2⟩ := (mem_filter.mp hi).2
      have := (mem_filter.mp (hr.symbol_mem hp)).1
      rwa [h1, h2] at this
    · obtain ⟨h1, h2⟩ := mem_filter.mp hb
      show #{i ∈ classOf L p D k | X i = b} = ν.nu k.1 b (b - k.2)
      rw [← hr.pair k.1 b h1 (b - k.2) h2]
      congr 1
      ext i
      have hd := congrFun hr.sub i
      simp only [Pi.sub_apply] at hd
      simp only [classOf, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨h3, h4, h5⟩, h6⟩
        exact ⟨h3, h4, h6, by omega⟩
      · rintro ⟨h3, h4, h6, h7⟩
        exact ⟨⟨h3, h4, by omega⟩, h6⟩
  · rintro ⟨X, Y⟩ hq ⟨X', Y'⟩ hq' hXX'
    have hr : IsRep L ν p D X Y := mem_reps.mp hq
    have hr' : IsRep L ν p D X' Y' := mem_reps.mp hq'
    simp only at hXX'
    have h1 : Y = X - D := by rw [← hr.sub, sub_sub_cancel]
    have h2 : Y' = X' - D := by rw [← hr'.sub, sub_sub_cancel]
    rw [h1, h2, hXX']
  · intro X hX
    obtain ⟨h1, h2⟩ := mem_typedAll.mp (mem_coe.mp hX)
    have hmem : ∀ i, i ≠ p.coord → X i ∈ ν.cSyms (L i) (D i) := fun i hi =>
      (h2 ⟨L i, D i⟩ (mem_sigma.mpr ⟨mem_univ _, hD.mem_diffs hi⟩)).1 i (by simp [classOf, hi])
    have hpinX : X p.coord = p.val := by
      rw [h1 p.coord fun k _ h => (mem_filter.mp h).2.1 rfl]
      simp [pinBase]
    refine ⟨(X, X - D), mem_coe.mpr (mem_reps.mpr ⟨⟨hpinX, fun i hi => ?_⟩, ⟨?_, fun i hi => ?_⟩,
      ?_, fun l x hx y hy => ?_⟩), rfl⟩
    · exact (mem_filter.mp (hmem i hi)).1
    · simp [hpinX, hD.pin]
    · exact (mem_filter.mp (hmem i hi)).2
    · simp
    · have hxS : x ∈ ν.cSyms l (x - y) := by
        refine mem_filter.mpr ⟨hx, ?_⟩
        rwa [sub_sub_cancel]
      have hk : (⟨l, x - y⟩ : Σ _ : Lab, ℤ) ∈ univ.sigma ν.diffs :=
        mem_sigma.mpr ⟨mem_univ _, mem_image.mpr ⟨(x, y), mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩
      have h3 := (h2 _ hk).2 x hxS
      simp only [sub_sub_cancel] at h3
      rw [← h3]
      congr 1
      ext i
      simp only [classOf, mem_filter, mem_univ, true_and, Pi.sub_apply]
      constructor
      · rintro ⟨h4, h5, h6, h7⟩
        exact ⟨⟨h4, h5, by omega⟩, h6⟩
      · rintro ⟨⟨h4, h5, h6⟩, h7⟩
        exact ⟨h4, h5, h7, by omega⟩

/-- **The count of representations.** On a good labeling, the number of representations is
`K = ∏_{(l, e)} multinomial (ν l x (x - e))`. -/
theorem card_reps (hD : Good L ν p D) : #(reps L ν p D) = ν.K := by
  have h := fst_bijOn hD
  rw [Finset.card_nbij Prod.fst h.mapsTo h.injOn h.surjOn, typedClasses,
    card_typedAll _ _ _ _ _ classOf_disjoint (fun k _ => (hD.class_eq k.1 k.2).symm), prod_sigma]
  rfl

/-- On a good labeling, the size of `F` is the total size of the varying classes, a number depending
on the layout only. -/
theorem card_free (hD : Good L ν p D) : #(free L ν p D) = ν.freeCount := by
  have hF : free L ν p D = ν.varying.biUnion (classOf L p D) := by
    ext i
    simp only [free, mem_filter, mem_univ, true_and, mem_biUnion, Layout.varying, mem_sigma,
      classOf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨L i, D i⟩, ⟨hD.mem_diffs h1, h2⟩, h1, rfl, rfl⟩
    · rintro ⟨k, ⟨-, h1⟩, h2, h3, h4⟩
      rw [h3, h4]
      exact ⟨h2, h1⟩
  rw [hF, card_biUnion fun k _ k' _ hk => classOf_disjoint k k' hk]
  exact sum_congr rfl fun k _ => hD.class_eq k.1 k.2

end Count

end SubsetBalancing
