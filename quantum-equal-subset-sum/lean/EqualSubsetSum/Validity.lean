import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The labels, the typed lists and Lemma 1

Coordinates carry a label `A`, `B` or `C`. An integer layout gives counts `ν l d`, one for each
label `l` and each value `d ∈ {-1, 0, 1}`, with `ν l 1` and `ν l (-1)` allowed to differ. The two
lists are defined by the coordinate alphabets

* `X`: on `A` in `{0,1}`, on `B` in `{0,1,2}`, on `C` constant `1`,
* `Y`: on `A` in `{0,1}`, on `B` constant `1`, on `C` in `{0,1,2}`,

and by exact counts of each symbol per label. With `f = ⌊ν A 0 / 2⌋` and `f' = ν A 0 - f`:

* `X` has `ν A (-1) + f` zeros and `ν A 1 + f'` ones on `A`, and type
  `(ν B (-1), ν B 0, ν B 1)` over `(0,1,2)` on `B`,
* `Y` has `ν A 1 + f` zeros and `ν A (-1) + f'` ones on `A`, and type
  `(ν C 1, ν C 0, ν C (-1))` over `(0,1,2)` on `C`.

Validity needs only the alphabets, and the fact that `X` has a zero on `B`.
-/

open Finset

namespace EqualSubsetSum

/-- The three kinds of coordinates. -/
inductive Label
  | A
  | B
  | C
  deriving DecidableEq

variable {ι : Type*} [Fintype ι]

/-- The inner product `⟨u, y⟩`. -/
def dot (u y : ι → ℤ) : ℤ := ∑ i, u i * y i

theorem dot_sub (u v y : ι → ℤ) : dot (u - v) y = dot u y - dot v y := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

/-- The number of coordinates with label `l` where `X` takes the value `v`. -/
def cnt (L : ι → Label) (l : Label) (v : ℤ) (X : ι → ℤ) : ℕ :=
  #{i | L i = l ∧ X i = v}

/-- Entries in `{-1, 0, 1}`. -/
def Trinary (D : ι → ℤ) : Prop := ∀ i, D i = -1 ∨ D i = 0 ∨ D i = 1

/-- The coordinate alphabets of the list `𝒳`. -/
structure AlphaX (L : ι → Label) (X : ι → ℤ) : Prop where
  onA : ∀ i, L i = .A → X i = 0 ∨ X i = 1
  onB : ∀ i, L i = .B → X i = 0 ∨ X i = 1 ∨ X i = 2
  onC : ∀ i, L i = .C → X i = 1

/-- The coordinate alphabets of the list `𝒴`. -/
structure AlphaY (L : ι → Label) (Y : ι → ℤ) : Prop where
  onA : ∀ i, L i = .A → Y i = 0 ∨ Y i = 1
  onB : ∀ i, L i = .B → Y i = 1
  onC : ∀ i, L i = .C → Y i = 0 ∨ Y i = 1 ∨ Y i = 2

/-- An integer layout: the count `ν l d` of coordinates of value `d` on label `l`. Only the values
`d ∈ {-1, 0, 1}` matter. Nothing forces `ν l 1 = ν l (-1)`. -/
abbrev Layout := Label → ℤ → ℕ

/-- `f = ⌊ν A 0 / 2⌋`. -/
def Layout.f (ν : Layout) : ℕ := ν .A 0 / 2

/-- `f' = ν A 0 - f`. -/
def Layout.f' (ν : Layout) : ℕ := ν .A 0 - ν.f

theorem Layout.f_le (ν : Layout) : ν.f ≤ ν .A 0 := Nat.div_le_self _ _

/-- Membership in `𝒳`: the alphabets and the exact types. -/
structure IsX (L : ι → Label) (ν : Layout) (X : ι → ℤ) : Prop extends AlphaX L X where
  a0 : cnt L .A 0 X = ν .A (-1) + ν.f
  a1 : cnt L .A 1 X = ν .A 1 + ν.f'
  b0 : cnt L .B 0 X = ν .B (-1)
  b1 : cnt L .B 1 X = ν .B 0
  b2 : cnt L .B 2 X = ν .B 1

/-- Membership in `𝒴`: the alphabets and the exact types. This is not `IsX` with the labels `B`
and `C` swapped: the zeros on `A` are `ν A 1 + f`, so the two lists differ at odd support. -/
structure IsY (L : ι → Label) (ν : Layout) (Y : ι → ℤ) : Prop extends AlphaY L Y where
  a0 : cnt L .A 0 Y = ν .A 1 + ν.f
  a1 : cnt L .A 1 Y = ν .A (-1) + ν.f'
  c0 : cnt L .C 0 Y = ν .C 1
  c1 : cnt L .C 1 Y = ν .C 0
  c2 : cnt L .C 2 Y = ν .C (-1)

open scoped Classical in
/-- The list `𝒳` as a finite set of vectors. -/
noncomputable def listX [DecidableEq ι] (L : ι → Label) (ν : Layout) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun _ => ({0, 1, 2} : Finset ℤ)).filter (IsX L ν)

open scoped Classical in
/-- The list `𝒴` as a finite set of vectors. -/
noncomputable def listY [DecidableEq ι] (L : ι → Label) (ν : Layout) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun _ => ({0, 1, 2} : Finset ℤ)).filter (IsY L ν)

omit [Fintype ι] in
theorem AlphaX.mem {L : ι → Label} {X : ι → ℤ} (h : AlphaX L X) (i : ι) :
    X i = 0 ∨ X i = 1 ∨ X i = 2 := by
  cases hl : L i with
  | A => rcases h.onA i hl with h | h <;> simp [h]
  | B => exact h.onB i hl
  | C => simp [h.onC i hl]

omit [Fintype ι] in
theorem AlphaY.mem {L : ι → Label} {Y : ι → ℤ} (h : AlphaY L Y) (i : ι) :
    Y i = 0 ∨ Y i = 1 ∨ Y i = 2 := by
  cases hl : L i with
  | A => rcases h.onA i hl with h | h <;> simp [h]
  | B => simp [h.onB i hl]
  | C => exact h.onC i hl

@[simp] theorem mem_listX [DecidableEq ι] {L : ι → Label} {ν : Layout} {X : ι → ℤ} :
    X ∈ listX L ν ↔ IsX L ν X := by
  classical
  simp only [listX, mem_filter, Fintype.mem_piFinset, and_iff_right_iff_imp]
  intro h i
  simpa using h.toAlphaX.mem i

@[simp] theorem mem_listY [DecidableEq ι] {L : ι → Label} {ν : Layout} {Y : ι → ℤ} :
    Y ∈ listY L ν ↔ IsY L ν Y := by
  classical
  simp only [listY, mem_filter, Fintype.mem_piFinset, and_iff_right_iff_imp]
  intro h i
  simpa using h.toAlphaY.mem i

/-! ## Lemma 1 -/

omit [Fintype ι] in
/-- `X - Y` has entries in `{-1, 0, 1}`. On `A` both are in `{0,1}`. On `B`, `Y = 1` and
`X ∈ {0,1,2}`. On `C` the reverse. -/
theorem sub_trinary {L : ι → Label} {X Y : ι → ℤ} (hX : AlphaX L X) (hY : AlphaY L Y) :
    Trinary (X - Y) := by
  intro i
  simp only [Pi.sub_apply]
  cases hl : L i with
  | A =>
    rcases hX.onA i hl with h | h <;> rcases hY.onA i hl with h' | h' <;> simp [h, h']
  | B =>
    have h' := hY.onB i hl
    rcases hX.onB i hl with h | h | h <;> simp [h, h']
  | C =>
    have h := hX.onC i hl
    rcases hY.onC i hl with h' | h' | h' <;> simp [h, h']

omit [Fintype ι] in
/-- `X ≠ Y` as soon as `X` has a zero on `B`, where `Y = 1`. -/
theorem ne_of_zero_on_B {L : ι → Label} {X Y : ι → ℤ} (hY : AlphaY L Y)
    (h : ∃ i, L i = .B ∧ X i = 0) : X ≠ Y := by
  obtain ⟨i, hl, hi⟩ := h
  rintro rfl
  have := hY.onB i hl
  omega

/-- A vector of `𝒳` has a zero on `B` when `ν B (-1) > 0`. -/
theorem exists_zero_on_B {L : ι → Label} {ν : Layout} {X : ι → ℤ} (hX : IsX L ν X)
    (h : 0 < ν .B (-1)) : ∃ i, L i = .B ∧ X i = 0 := by
  have h2 : 0 < cnt L .B 0 X := by rw [hX.b0]; exact h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h2
  simpa using ⟨i, by simpa using hi⟩

/-- **Lemma 1.** If `X ∈ 𝒳`, `Y ∈ 𝒴`, `ν B (-1) > 0` and `⟨X,y⟩ = ⟨Y,y⟩`, then `X - Y` is a nonzero
vector over `{-1, 0, 1}` annihilating `y`. -/
theorem validity {L : ι → Label} {ν : Layout} {X Y y : ι → ℤ} (hX : IsX L ν X) (hY : IsY L ν Y)
    (hB : 0 < ν .B (-1)) (hsum : dot X y = dot Y y) :
    Trinary (X - Y) ∧ X - Y ≠ 0 ∧ dot (X - Y) y = 0 := by
  refine ⟨sub_trinary hX.toAlphaX hY.toAlphaY, ?_, ?_⟩
  · intro h
    exact ne_of_zero_on_B hY.toAlphaY (exists_zero_on_B hX hB) (sub_eq_zero.mp h)
  · rw [dot_sub, hsum, sub_self]

/-! ## The reduction by signs -/

/-- The support of `D`. -/
def supp (D : ι → ℤ) : Finset ι := {i | D i ≠ 0}

/-- `D` is a nonzero solution for `y` of minimum support. -/
structure MinimalSolution (D y : ι → ℤ) : Prop where
  trinary : Trinary D
  ne_zero : D ≠ 0
  dot_eq : dot D y = 0
  minimal : ∀ E : ι → ℤ, Trinary E → E ≠ 0 → dot E y = 0 → #(supp D) ≤ #(supp E)

/-- Multiplying `D` and `x` coordinatewise by the same signs preserves solutions of minimum
support: `D` flipped by `ε` is a solution of minimum support for `y_i = ε_i x_i`. -/
theorem MinimalSolution.flip {D x ε : ι → ℤ} (h : MinimalSolution D x)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    MinimalSolution (fun i => ε i * D i) (fun i => ε i * x i) := by
  have hne : ∀ i, ε i ≠ 0 := fun i => by rcases hε i with h | h <;> omega
  have hsq : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have hsupp : ∀ E : ι → ℤ, supp (fun i => ε i * E i) = supp E := fun E => by
    ext i
    simp [supp, hne i]
  have hdot : ∀ E : ι → ℤ, dot (fun i => ε i * E i) (fun i => ε i * x i) = dot E x := fun E => by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ε i * E i * (ε i * x i) = (ε i * ε i) * (E i * x i) := by ring
      _ = E i * x i := by rw [hsq, one_mul]
  have htri : ∀ E : ι → ℤ, Trinary E → Trinary fun i => ε i * E i := fun E hE i => by
    rcases hε i with h | h <;> rcases hE i with h' | h' | h' <;> simp [h, h']
  refine ⟨htri D h.trinary, ?_, ?_, ?_⟩
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
    have h2 := h.minimal _ (htri E hE) ?_ h1
    · rwa [hsupp] at h2
    · intro h0
      apply hE0
      funext i
      have := congrFun h0 i
      simpa [hne i] using this

end EqualSubsetSum
