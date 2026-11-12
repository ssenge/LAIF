import Mathlib

/-!
Hard instances for ε-approximate equilibria of zero-sum games. The row player maximizes over
`Fin m`, the column player minimizes over `Fin c ⊕ Fin k`, where the `k` padding columns are all
ones. Row `i` has a single zero at column `p i`, or no zero if `p i = none`.

No instance: every row has a zero. Yes instance: exactly one row has none. An ε-approximate
equilibrium with `c ε < 1/2` puts weight more than `1/2` on that row, and the value is `1` on yes
instances and at most `1 - 1/c` on no instances. The relation used in the relational adversary bound
(remove the zero of one row) has the counts `m`, `c`, `1`, `1`.
-/

namespace ZeroSumLB

open Finset

variable {m c k : ℕ}

def A (p : Fin m → Option (Fin c)) : Fin m → Fin c ⊕ Fin k → ℝ
  | i, Sum.inl l => if p i = some l then 0 else 1
  | _, Sum.inr _ => 1

/-- Payoff of column `l` against the row strategy `x`. -/
def colPay (p : Fin m → Option (Fin c)) (x : Fin m → ℝ) (l : Fin c ⊕ Fin k) : ℝ :=
  ∑ i, x i * A p i l

/-- Payoff of row `i` against the column strategy `y`. -/
def rowPay (p : Fin m → Option (Fin c)) (y : Fin c ⊕ Fin k → ℝ) (i : Fin m) : ℝ :=
  ∑ l, A p i l * y l

def Simplex {ι : Type*} [Fintype ι] (x : ι → ℝ) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- `(x, y)` is an ε-approximate equilibrium: `max_i (A y)_i - min_l (xᵀ A)_l ≤ ε`. -/
def ApproxNE (p : Fin m → Option (Fin c)) (ε : ℝ) (x : Fin m → ℝ) (y : Fin c ⊕ Fin k → ℝ) :
    Prop :=
  Simplex x ∧ Simplex y ∧ ∀ i (l : Fin c ⊕ Fin k), rowPay p y i - colPay p x l ≤ ε

theorem colPay_inl (p : Fin m → Option (Fin c)) (x : Fin m → ℝ) (l : Fin c) :
    colPay (k := k) p x (Sum.inl l) = ∑ i, x i - ∑ i, if p i = some l then x i else 0 := by
  simp only [colPay, A]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i; split_ifs <;> ring

/-- Total loss over the real columns is the weight on rows that have a zero. -/
theorem loss_sum (p : Fin m → Option (Fin c)) (x : Fin m → ℝ) (hx : ∑ i, x i = 1) :
    ∑ l : Fin c, (1 - colPay (k := k) p x (Sum.inl l)) =
      ∑ i, if p i = none then 0 else x i := by
  simp_rw [colPay_inl, hx, sub_sub_cancel]
  rw [Finset.sum_comm]
  congr 1; ext i
  cases h : p i with
  | none => simp
  | some l0 => simp

theorem yes_row (p : Fin m → Option (Fin c)) (j : Fin m) (hj : p j = none)
    (y : Fin c ⊕ Fin k → ℝ) (hy : ∑ l, y l = 1) : rowPay p y j = 1 := by
  rw [← hy]; simp only [rowPay]; congr 1; ext l
  cases l <;> simp [A, hj]

/-- On a yes instance, an ε-approximate equilibrium with `c ε < 1/2` puts weight
more than `1/2` on the row without a zero. -/
theorem yes_identifies (p : Fin m → Option (Fin c)) (j : Fin m) (hj : p j = none)
    (hoth : ∀ i, i ≠ j → p i ≠ none) (ε : ℝ) (x : Fin m → ℝ) (y : Fin c ⊕ Fin k → ℝ)
    (h : ApproxNE p ε x y) (hc : (c : ℝ) * ε < 1 / 2) : 1 / 2 < x j := by
  obtain ⟨⟨_, hx1⟩, ⟨_, hy1⟩, hne⟩ := h
  have hcol : ∀ l : Fin c, 1 - colPay (k := k) p x (Sum.inl l) ≤ ε := by
    intro l; have := hne j (Sum.inl l); rwa [yes_row p j hj y hy1] at this
  have hle : ∑ l : Fin c, (1 - colPay (k := k) p x (Sum.inl l)) ≤ c * ε := by
    calc _ ≤ ∑ _l : Fin c, ε := Finset.sum_le_sum fun l _ => hcol l
      _ = c * ε := by simp
  have hpt : ∀ i, (if p i = none then 0 else x i) = x i - if i = j then x i else 0 := by
    intro i; by_cases hi : i = j
    · subst hi; simp [hj]
    · simp [hi, hoth i hi]
  rw [loss_sum p x hx1] at hle
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hx1] at hle
  linarith

/-- On a yes instance the row without a zero guarantees `1`. -/
theorem yes_pure (p : Fin m → Option (Fin c)) (j : Fin m) (hj : p j = none)
    (l : Fin c ⊕ Fin k) : colPay p (Pi.single j 1) l = 1 := by
  simp only [colPay]
  rw [Finset.sum_eq_single j]
  · cases l <;> simp [A, hj]
  · intro i _ hi; simp [hi]
  · simp

/-- On a no instance every row strategy has a column with payoff at most `1 - 1/c`. -/
theorem no_gap (p : Fin m → Option (Fin c)) (hall : ∀ i, p i ≠ none) (x : Fin m → ℝ)
    (hx : Simplex x) (hc : 0 < c) :
    ∃ l : Fin c, colPay (k := k) p x (Sum.inl l) ≤ 1 - 1 / c := by
  have hsum := loss_sum (k := k) p x hx.2
  simp only [hall, ite_false, hx.2] at hsum
  have hne : (univ : Finset (Fin c)).Nonempty := ⟨⟨0, hc⟩, mem_univ _⟩
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (1 : ℝ) / c) (g := fun l => 1 - colPay (k := k) p x (Sum.inl l))
    (by rw [hsum]; simp [hcR.ne'])
  exact ⟨l, by linarith⟩

/-! ### The adversary relation -/

/-- Input bit `(i, l)`: row `i` has its zero at column `l`. -/
def bit (p : Fin m → Option (Fin c)) (i : Fin m) (l : Fin c) : Prop := p i = some l

def NoInst (p : Fin m → Option (Fin c)) : Prop := ∀ i, p i ≠ none

def YesInst (p : Fin m → Option (Fin c)) : Prop :=
  ∃ j, p j = none ∧ ∀ i, i ≠ j → p i ≠ none

/-- `y` arises from the no instance `x` by removing the zero of one row. -/
def Rel (x y : Fin m → Option (Fin c)) : Prop := NoInst x ∧ ∃ j, y = Function.update x j none

theorem rel_yes {x y : Fin m → Option (Fin c)} (h : Rel x y) : YesInst y := by
  obtain ⟨hx, j, rfl⟩ := h
  exact ⟨j, by simp, fun i hi => by simp [Function.update_of_ne hi, hx i]⟩

/-- Each no instance is related to `m` yes instances. -/
theorem left_many (x : Fin m → Option (Fin c)) (hx : NoInst x) :
    Function.Injective (fun j => Function.update x j none) ∧
      ∀ j, Rel x (Function.update x j none) := by
  refine ⟨fun j1 j2 h => ?_, fun j => ⟨hx, j, rfl⟩⟩
  by_contra hne
  have := congrFun h j1
  simp [Function.update_of_ne hne] at this
  exact hx j1 this.symm

/-- Each yes instance is related to `c` no instances. -/
theorem right_many (y : Fin m → Option (Fin c)) (j : Fin m) (hj : y j = none)
    (hoth : ∀ i, i ≠ j → y i ≠ none) :
    Function.Injective (fun l : Fin c => Function.update y j (some l)) ∧
      ∀ l, Rel (Function.update y j (some l)) y := by
  refine ⟨fun l1 l2 h => by simpa using congrFun h j, fun l => ⟨?_, j, ?_⟩⟩
  · intro i; by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi, hoth i hi]
  · funext i; by_cases hi : i = j
    · subst hi; simp [hj]
    · simp [Function.update_of_ne hi]

/-- For a no instance and a bit, at most one related yes instance differs there. -/
theorem left_unique (x y1 y2 : Fin m → Option (Fin c)) (i : Fin m) (l : Fin c)
    (h1 : Rel x y1) (h2 : Rel x y2) (d1 : ¬(bit x i l ↔ bit y1 i l))
    (d2 : ¬(bit x i l ↔ bit y2 i l)) : y1 = y2 := by
  obtain ⟨_, j1, rfl⟩ := h1
  obtain ⟨_, j2, rfl⟩ := h2
  have e1 : i = j1 := by
    by_contra hi; exact d1 (by simp [bit, Function.update_of_ne hi])
  have e2 : i = j2 := by
    by_contra hi; exact d2 (by simp [bit, Function.update_of_ne hi])
  rw [← e1, ← e2]

/-- For a yes instance and a bit, at most one related no instance differs there. -/
theorem right_unique (y x1 x2 : Fin m → Option (Fin c)) (i : Fin m) (l : Fin c)
    (hy : YesInst y) (h1 : Rel x1 y) (h2 : Rel x2 y) (d1 : ¬(bit x1 i l ↔ bit y i l))
    (d2 : ¬(bit x2 i l ↔ bit y i l)) : x1 = x2 := by
  obtain ⟨j0, _, hoth⟩ := hy
  -- the removed row is the unique row of `y` without a zero
  have key : ∀ x, Rel x y → ¬(bit x i l ↔ bit y i l) →
      i = j0 ∧ x i = some l ∧ ∀ t, t ≠ j0 → x t = y t := by
    intro x ⟨_, j, hyx⟩ d
    have hj : j = j0 := by
      by_contra hne; exact hoth j hne (by rw [hyx]; simp)
    subst hj
    have hrest : ∀ t, t ≠ j → x t = y t := fun t ht => by rw [hyx, Function.update_of_ne ht]
    have hi : i = j := by
      by_contra hne; exact d (by rw [bit, bit, hrest i hne])
    subst hi
    refine ⟨rfl, ?_, hrest⟩
    have hyi : y i = none := by rw [hyx]; simp
    by_contra hx; exact d (by simp [bit, hyi, hx])
  obtain ⟨e, a1, r1⟩ := key x1 h1 d1
  obtain ⟨_, a2, r2⟩ := key x2 h2 d2
  funext t; by_cases ht : t = j0
  · rw [ht, ← e, a1, a2]
  · rw [r1 t ht, r2 t ht]

end ZeroSumLB
