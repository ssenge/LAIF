import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The labels, the typed lists and Lemma 1

A label is a pair of integer intervals `(S, T)` with `S - T` inside `[-d:d]`. Coordinates carry a
label from a finite type. One coordinate is pinned: every `X` has the value `c` there and every `Y`
has the value `0`. The other coordinates of `X` take values in `S` of their label, those of `Y` in
`T`. A layout gives the counts `ν l x y`, and the lists fix the number of coordinates of each symbol
per label, through the two marginals of `ν`.

Validity needs only the alphabets and the pin. The width bound `|x - x'| ≤ min (s, t) ≤ d` of an
exchange inside a label is what makes the difference of two representations a vector of `[-d:d]^n`.
-/

open Finset

namespace SubsetBalancing

/-- A pair of integer intervals `S = [sLo : sHi]`, `T = [tLo : tHi]`. -/
@[ext] structure Label where
  sLo : ℤ
  sHi : ℤ
  tLo : ℤ
  tHi : ℤ

namespace Label

/-- The interval of `X`-symbols. -/
def S (l : Label) : Finset ℤ := Finset.Icc l.sLo l.sHi

/-- The interval of `Y`-symbols. -/
def T (l : Label) : Finset ℤ := Finset.Icc l.tLo l.tHi

/-- The width `s = |S| - 1`. -/
def s (l : Label) : ℤ := l.sHi - l.sLo

/-- The width `t = |T| - 1`. -/
def t (l : Label) : ℤ := l.tHi - l.tLo

/-- `S - T` lies inside `[-d:d]`. -/
def Inside (d : ℤ) (l : Label) : Prop := ∀ x ∈ l.S, ∀ y ∈ l.T, |x - y| ≤ d

theorem mem_S {l : Label} {x : ℤ} : x ∈ l.S ↔ l.sLo ≤ x ∧ x ≤ l.sHi := Finset.mem_Icc

theorem mem_T {l : Label} {y : ℤ} : y ∈ l.T ↔ l.tLo ≤ y ∧ y ≤ l.tHi := Finset.mem_Icc

/-- **The widths.** For nonempty intervals, `S - T` inside `[-d:d]` gives `s + t ≤ 2 d`. -/
theorem width_add_le {l : Label} {d : ℤ} (h : l.Inside d) (hS : l.sLo ≤ l.sHi)
    (hT : l.tLo ≤ l.tHi) : l.s + l.t ≤ 2 * d := by
  have h1 := h l.sHi (mem_S.mpr ⟨hS, le_rfl⟩) l.tLo (mem_T.mpr ⟨le_rfl, hT⟩)
  have h2 := h l.sLo (mem_S.mpr ⟨le_rfl, hS⟩) l.tHi (mem_T.mpr ⟨hT, le_rfl⟩)
  rw [abs_le] at h1 h2
  unfold s t
  omega

/-- The width bound fails for an empty interval, where the condition on `S - T` is vacuous: nonempty
intervals are needed in `width_add_le`. -/
theorem width_needs_nonempty : ∃ l : Label, l.Inside 0 ∧ ¬ l.s + l.t ≤ 2 * 0 := by
  refine ⟨⟨0, -1, 0, 100⟩, ?_, ?_⟩
  · intro x hx
    have := mem_S.mp hx
    simp only at this
    omega
  · simp [s, t]

/-- **The smaller width.** `s + t ≤ 2 d` implies `min (s, t) ≤ d`. -/
theorem min_width_le {s t d : ℤ} (h : s + t ≤ 2 * d) : min s t ≤ d := by
  rcases le_total s t with h' | h'
  · rw [min_eq_left h']
    omega
  · rw [min_eq_right h']
    omega

theorem abs_sub_le_s {l : Label} {x x' : ℤ} (hx : x ∈ l.S) (hx' : x' ∈ l.S) : |x - x'| ≤ l.s := by
  have h1 := mem_S.mp hx
  have h2 := mem_S.mp hx'
  rw [abs_le]
  unfold s
  omega

theorem abs_sub_le_t {l : Label} {y y' : ℤ} (hy : y ∈ l.T) (hy' : y' ∈ l.T) : |y - y'| ≤ l.t := by
  have h1 := mem_T.mp hy
  have h2 := mem_T.mp hy'
  rw [abs_le]
  unfold t
  omega

/-- An exchange inside a label: if `x - y = x' - y'` then `E = x - x' = y - y'` is a difference within
`S` and within `T`, so `|E| ≤ min (s, t)`. -/
theorem abs_exchange_le_min {l : Label} {x x' y y' : ℤ} (hx : x ∈ l.S) (hx' : x' ∈ l.S)
    (hy : y ∈ l.T) (hy' : y' ∈ l.T) (h : x - y = x' - y') : |x - x'| ≤ min l.s l.t := by
  have hE : x - x' = y - y' := by omega
  refine le_min (abs_sub_le_s hx hx') ?_
  rw [hE]
  exact abs_sub_le_t hy hy'

/-- **The width bound of an exchange.** For `x, x' ∈ S` and `y, y' ∈ T` with `x - y = x' - y'`, the
difference `E = x - x'` has `|E| ≤ d`. -/
theorem abs_exchange_le {l : Label} {d : ℤ} (hl : l.Inside d) {x x' y y' : ℤ} (hx : x ∈ l.S)
    (hx' : x' ∈ l.S) (hy : y ∈ l.T) (hy' : y' ∈ l.T) (h : x - y = x' - y') : |x - x'| ≤ d := by
  have hS : l.sLo ≤ l.sHi := by
    have := mem_S.mp hx
    omega
  have hT : l.tLo ≤ l.tHi := by
    have := mem_T.mp hy
    omega
  exact (abs_exchange_le_min hx hx' hy hy' h).trans (min_width_le (width_add_le hl hS hT))

/-- The wide label with `S = [0:s]` and `T = [s - d : s - d + t]`, `s + t = 2 d`. -/
def wide (d s t : ℤ) : Label := ⟨0, s, s - d, s - d + t⟩

/-- A wide label has `S - T` inside `[-d:d]`, and its differences reach both ends. -/
theorem wide_inside {d s t : ℤ} (h : s + t = 2 * d) : (wide d s t).Inside d := by
  intro x hx y hy
  have h1 := mem_S.mp hx
  have h2 := mem_T.mp hy
  simp only [wide] at h1 h2
  rw [abs_le]
  omega

end Label

/-- A layout: a label of intervals for each label name, and the counts `ν l x y`. -/
structure Layout (Lab : Type*) where
  /-- The intervals of each label. -/
  iv : Lab → Label
  /-- The number of coordinates of the label that carry the pair `(x, y)`. -/
  nu : Lab → ℤ → ℤ → ℕ

namespace Layout

variable {Lab : Type*}

/-- Every label of the layout has `S - T` inside `[-d:d]`. -/
def Inside (ν : Layout Lab) (d : ℤ) : Prop := ∀ l, (ν.iv l).Inside d

/-- The count of the symbol `s` required of `X` on `l`: `∑_y ν l s y`. -/
def xCount (ν : Layout Lab) (l : Lab) (s : ℤ) : ℕ := ∑ y ∈ (ν.iv l).T, ν.nu l s y

/-- The count of the symbol `s` required of `Y` on `l`: `∑_x ν l x s`. -/
def yCount (ν : Layout Lab) (l : Lab) (s : ℤ) : ℕ := ∑ x ∈ (ν.iv l).S, ν.nu l x s

end Layout

/-- The pinned coordinate and the value of `X` there. -/
structure Pin (ι : Type*) where
  /-- The coordinate `i*`. -/
  coord : ι
  /-- The value `c*`. -/
  val : ℤ

variable {ι Lab : Type*} [Fintype ι]

/-- The inner product `⟨u, y⟩`. -/
def dot (u y : ι → ℤ) : ℤ := ∑ i, u i * y i

theorem dot_sub (u v y : ι → ℤ) : dot (u - v) y = dot u y - dot v y := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

/-- Entries in `[-d:d]`. -/
def InBox (d : ℤ) (D : ι → ℤ) : Prop := ∀ i, |D i| ≤ d

/-- The coordinate alphabets of the list `𝒳`: the pin, and `S` of the label elsewhere. -/
structure AlphaX (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) (X : ι → ℤ) : Prop where
  pin : X p.coord = p.val
  mem : ∀ i, i ≠ p.coord → X i ∈ (ν.iv (L i)).S

/-- The coordinate alphabets of the list `𝒴`: zero at the pin, and `T` of the label elsewhere. -/
structure AlphaY (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) (Y : ι → ℤ) : Prop where
  pin : Y p.coord = 0
  mem : ∀ i, i ≠ p.coord → Y i ∈ (ν.iv (L i)).T

section Lists

variable [DecidableEq ι] [DecidableEq Lab]

/-- The number of coordinates of label `l`, other than the pin, where `X` has the value `v`. -/
def cnt (L : ι → Lab) (p : Pin ι) (l : Lab) (v : ℤ) (X : ι → ℤ) : ℕ :=
  #{i | i ≠ p.coord ∧ L i = l ∧ X i = v}

/-- Membership in `𝒳`: the alphabets and the exact types. -/
structure IsX (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) (X : ι → ℤ) : Prop
    extends AlphaX ν L p X where
  type : ∀ l, ∀ s ∈ (ν.iv l).S, cnt L p l s X = ν.xCount l s

/-- Membership in `𝒴`: the alphabets and the exact types. -/
structure IsY (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) (Y : ι → ℤ) : Prop
    extends AlphaY ν L p Y where
  type : ∀ l, ∀ s ∈ (ν.iv l).T, cnt L p l s Y = ν.yCount l s

open scoped Classical in
/-- The list `𝒳` as a finite set of vectors. -/
noncomputable def listX (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun i => if i = p.coord then {p.val} else (ν.iv (L i)).S).filter (IsX ν L p)

open scoped Classical in
/-- The list `𝒴` as a finite set of vectors. -/
noncomputable def listY (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun i => if i = p.coord then {0} else (ν.iv (L i)).T).filter (IsY ν L p)

@[simp] theorem mem_listX {ν : Layout Lab} {L : ι → Lab} {p : Pin ι} {X : ι → ℤ} :
    X ∈ listX ν L p ↔ IsX ν L p X := by
  classical
  simp only [listX, mem_filter, Fintype.mem_piFinset, and_iff_right_iff_imp]
  intro h i
  by_cases hi : i = p.coord
  · subst hi
    simp [h.pin]
  · simpa [hi] using h.mem i hi

@[simp] theorem mem_listY {ν : Layout Lab} {L : ι → Lab} {p : Pin ι} {Y : ι → ℤ} :
    Y ∈ listY ν L p ↔ IsY ν L p Y := by
  classical
  simp only [listY, mem_filter, Fintype.mem_piFinset, and_iff_right_iff_imp]
  intro h i
  by_cases hi : i = p.coord
  · subst hi
    simp [h.pin]
  · simpa [hi] using h.mem i hi

end Lists

/-! ## Lemma 1 -/

omit [Fintype ι] in
/-- `X - Y` has entries in `[-d:d]`. On a label, `x - y ∈ S - T`. At the pin the difference is `c`. -/
theorem sub_inBox {ν : Layout Lab} {L : ι → Lab} {p : Pin ι} {d : ℤ} {X Y : ι → ℤ}
    (hd : ν.Inside d) (hc : |p.val| ≤ d) (hX : AlphaX ν L p X) (hY : AlphaY ν L p Y) :
    InBox d (X - Y) := by
  intro i
  simp only [Pi.sub_apply]
  by_cases hi : i = p.coord
  · subst hi
    rw [hX.pin, hY.pin, sub_zero]
    exact hc
  · exact hd (L i) _ (hX.mem i hi) _ (hY.mem i hi)

omit [Fintype ι] in
/-- A pinned coordinate with `X = c`, `Y = 0`, `c ≠ 0` forces `X ≠ Y`. -/
theorem ne_of_pin {ν : Layout Lab} {L : ι → Lab} {p : Pin ι} {X Y : ι → ℤ} (hc : p.val ≠ 0)
    (hX : AlphaX ν L p X) (hY : AlphaY ν L p Y) : X ≠ Y := by
  rintro rfl
  exact hc (hX.pin.symm.trans hY.pin)

/-- **Lemma 1.** If `X` and `Y` have the alphabets of the lists, `c ≠ 0`, `|c| ≤ d` and
`⟨X,y⟩ = ⟨Y,y⟩`, then `X - Y` is a nonzero vector of `[-d:d]^n` annihilating `y`. -/
theorem validity {ν : Layout Lab} {L : ι → Lab} {p : Pin ι} {d : ℤ} {X Y y : ι → ℤ}
    (hd : ν.Inside d) (hc : |p.val| ≤ d) (hc0 : p.val ≠ 0) (hX : AlphaX ν L p X)
    (hY : AlphaY ν L p Y) (hsum : dot X y = dot Y y) :
    InBox d (X - Y) ∧ X - Y ≠ 0 ∧ dot (X - Y) y = 0 := by
  refine ⟨sub_inBox hd hc hX hY, ?_, ?_⟩
  · intro h
    exact ne_of_pin hc0 hX hY (sub_eq_zero.mp h)
  · rw [dot_sub, hsum, sub_self]

/-! ## The reduction by signs -/

/-- The support of `D`. -/
def supp (D : ι → ℤ) : Finset ι := {i | D i ≠ 0}

/-- `D` is a nonzero solution for `y` in `[-d:d]^n` of minimum support. -/
structure MinimalSolution (d : ℤ) (D y : ι → ℤ) : Prop where
  inBox : InBox d D
  ne_zero : D ≠ 0
  dot_eq : dot D y = 0
  minimal : ∀ E : ι → ℤ, InBox d E → E ≠ 0 → dot E y = 0 → #(supp D) ≤ #(supp E)

/-- A nonzero solution in `[-d:d]^n` forces `d ≥ 0`. -/
theorem MinimalSolution.d_nonneg {d : ℤ} {D y : ι → ℤ} (h : MinimalSolution d D y) : 0 ≤ d := by
  obtain ⟨i, -⟩ := Function.ne_iff.mp h.ne_zero
  exact (abs_nonneg _).trans (h.inBox i)

/-- Multiplying `D` and `x` coordinatewise by the same signs preserves solutions of minimum
support: `D` flipped by `ε` is a solution of minimum support for `y_i = ε_i x_i`. -/
theorem MinimalSolution.flip {d : ℤ} {D x ε : ι → ℤ} (h : MinimalSolution d D x)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    MinimalSolution d (fun i => ε i * D i) (fun i => ε i * x i) := by
  have hne : ∀ i, ε i ≠ 0 := fun i => by rcases hε i with h | h <;> omega
  have hsq : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have hsupp : ∀ E : ι → ℤ, supp (fun i => ε i * E i) = supp E := fun E => by
    ext i
    simp [supp, hne i]
  have hdot : ∀ E : ι → ℤ, dot (fun i => ε i * E i) (fun i => ε i * x i) = dot E x := fun E => by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ε i * E i * (ε i * x i) = (ε i * ε i) * (E i * x i) := by ring
      _ = E i * x i := by rw [hsq, one_mul]
  have hbox : ∀ E : ι → ℤ, InBox d E → InBox d fun i => ε i * E i := fun E hE i => by
    rcases hε i with h' | h' <;> simpa [h', abs_neg] using hE i
  refine ⟨hbox D h.inBox, ?_, ?_, ?_⟩
  · intro h0
    apply h.ne_zero
    funext i
    have := congrFun h0 i
    simpa [hne i] using this
  · rw [hdot]
    exact h.dot_eq
  · intro E hE hE0 hEy
    rw [hsupp]
    have hEE : (fun i => ε i * ((fun i => ε i * E i) i)) = E := by
      funext i
      show ε i * (ε i * E i) = E i
      rw [← mul_assoc, hsq, one_mul]
    have h1 : dot (fun i => ε i * E i) x = 0 := by
      rw [← hdot (fun i => ε i * E i), hEE]
      exact hEy
    have h2 := h.minimal _ (hbox E hE) ?_ h1
    · rwa [hsupp] at h2
    · intro h0
      apply hE0
      funext i
      have := congrFun h0 i
      simpa [hne i] using this

end SubsetBalancing
