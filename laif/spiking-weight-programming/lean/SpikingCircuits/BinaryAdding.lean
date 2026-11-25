/-!
# Binary adding with a layer of gates that fire unless all conditions hold

The input of a step is a pair `(m, b)`: mask and bit. The label of a sequence is the number of steps with
`m = b = true`. The first layer of the network has 30 gates `n i c`, one for each count `i < 10` and each input
case `c` (`0`: mask off, `1`: mask on and bit off, `2`: mask on and bit on). A gate has drive
`3/4 * (fanIn - conditions that hold)` and fires when the drive exceeds the threshold `1/2`; `gate` states this
in integers. The gate `n i c` is silent exactly when the count before the step is `i` and the input case is `c`.
The count before a step is read from the silent gate of the previous step.

`network_eq_label`: for every non-empty sequence of any length with label at most 9, the class unit `j` of the
second layer fires after the last step exactly when `j` is the label.
`class_units_differ` and `ten_ones_no_class` show that the statement has content: the answer depends on the
input, and with ten counted steps no class unit fires, so the bound on the label is needed.
The file uses core Lean only. It describes the logic of the gates; a gate that does not fire has drive 0 and a
gate that fires is reset, so no membrane potential is carried from step to step.
-/

namespace BinaryAdding

/-- Which of the 30 gates fire. -/
abbrev Pattern := Fin 10 → Fin 3 → Bool

/-- Input case of a step: 0 mask off, 1 mask on and bit off, 2 mask on and bit on. -/
def caseOf (m b : Bool) : Fin 3 := if m then (if b then 2 else 1) else 0

/-- 1 if gate `n i c` exists and is silent. -/
def silent (f : Pattern) (i : Nat) (c : Fin 3) : Nat :=
  if h : i < 10 then (if f ⟨i, h⟩ c then 0 else 1) else 0

/-- Number of silent gates among the sources of count `i`: after a step whose silent gate is `n i 0`, `n i 1`
or `n (i - 1) 2` the count is `i`. -/
def state (f : Pattern) (i : Nat) : Nat :=
  silent f i 0 + silent f i 1 + (if 0 < i then silent f (i - 1) 2 else 0)

/-- At the first step the count is 0. -/
def stateFirst (i : Nat) : Nat := if i = 0 then 1 else 0

/-- Number of input conditions of case `c` that hold. -/
def lits (c : Fin 3) (m b : Bool) : Nat :=
  if c = 0 then (if m then 0 else 1)
  else if c = 1 then (if m then 1 else 0) + (if b then 0 else 1)
  else (if m then 1 else 0) + (if b then 1 else 0)

/-- Number of conditions of a gate: the count and one or two input conditions. -/
def fanIn (c : Fin 3) : Nat := if c = 0 then 2 else 3

/-- The gate fires iff `3/4 * (fanIn - conditions that hold) > 1/2`, where `st` says whether the count
condition holds. -/
def gate (st : Nat) (c : Fin 3) (m b : Bool) : Bool := decide (3 * (st + lits c m b) + 2 < 3 * fanIn c)

def step (f : Pattern) (m b : Bool) : Pattern := fun i c => gate (state f i.val) c m b

def first (m b : Bool) : Pattern := fun i c => gate (stateFirst i.val) c m b

/-- Class unit `j` of the second layer: drive `3/4 * (silent sources of count j)` against threshold `1/2`. -/
def classUnit (f : Pattern) (j : Nat) : Bool := decide (2 < 3 * state f j)

def run : Pattern → List (Bool × Bool) → Pattern
  | f, [] => f
  | f, x :: xs => run (step f x.1 x.2) xs

/-- Firing pattern of the first layer after the last step. -/
def network : List (Bool × Bool) → Pattern
  | [] => fun _ _ => true
  | x :: xs => run (first x.1 x.2) xs

/-- Number of steps with mask and bit on. -/
def label : List (Bool × Bool) → Nat
  | [] => 0
  | x :: xs => (if x.1 && x.2 then 1 else 0) + label xs

/-- Exactly the gate `n i c` is silent. -/
def hot (i : Nat) (c : Fin 3) : Pattern := fun a d => !(decide (a.val = i) && decide (d = c))

/-- 1 if the step of case `c` is counted. -/
def inc (c : Fin 3) : Nat := if c = 2 then 1 else 0

theorem inc_caseOf (m b : Bool) : inc (caseOf m b) = if m && b then 1 else 0 := by
  cases m <;> cases b <;> rfl

theorem first_hot : ∀ (m b : Bool) (a : Fin 10) (d : Fin 3), first m b a d = hot 0 (caseOf m b) a d := by
  decide

theorem step_hot : ∀ (i : Fin 10) (c : Fin 3), i.val + inc c ≤ 9 → ∀ (m b : Bool) (a : Fin 10) (d : Fin 3),
    step (hot i.val c) m b a d = hot (i.val + inc c) (caseOf m b) a d := by
  decide

theorem class_hot : ∀ (i : Fin 10) (c : Fin 3), i.val + inc c ≤ 9 → ∀ j : Fin 10,
    classUnit (hot i.val c) j.val = decide (j.val = i.val + inc c) := by
  decide

theorem run_hot (xs : List (Bool × Bool)) : ∀ (n : Nat) (c : Fin 3), n + inc c + label xs ≤ 9 →
    ∃ n' c', run (hot n c) xs = hot n' c' ∧ n' + inc c' = n + inc c + label xs := by
  induction xs with
  | nil => intro n c _; exact ⟨n, c, rfl, by simp [label]⟩
  | cons x xs ih =>
    intro n c h
    have hl : label (x :: xs) = (if x.1 && x.2 then 1 else 0) + label xs := rfl
    have hs : step (hot n c) x.1 x.2 = hot (n + inc c) (caseOf x.1 x.2) := by
      funext a d
      exact step_hot ⟨n, by omega⟩ c (by show n + inc c ≤ 9; omega) x.1 x.2 a d
    obtain ⟨n', c', h1, h2⟩ := ih (n + inc c) (caseOf x.1 x.2) (by rw [inc_caseOf]; omega)
    exact ⟨n', c', by show run (step (hot n c) x.1 x.2) xs = _; rw [hs, h1], by rw [h2, inc_caseOf]; omega⟩

/-- After any non-empty sequence with label at most 9, class unit `j` fires iff `j` is the label. -/
theorem network_eq_label (xs : List (Bool × Bool)) (hne : xs ≠ []) (h : label xs ≤ 9) (j : Fin 10) :
    classUnit (network xs) j.val = decide (j.val = label xs) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs =>
    have hl : label (x :: xs) = (if x.1 && x.2 then 1 else 0) + label xs := rfl
    have hf : first x.1 x.2 = hot 0 (caseOf x.1 x.2) := by funext a d; exact first_hot x.1 x.2 a d
    obtain ⟨n', c', h1, h2⟩ := run_hot xs 0 (caseOf x.1 x.2) (by rw [inc_caseOf]; omega)
    have h3 : n' + inc c' = label (x :: xs) := by rw [h2, inc_caseOf]; omega
    show classUnit (run (first x.1 x.2) xs) j.val = _
    rw [hf, h1, ← h3]
    exact class_hot ⟨n', by omega⟩ c' (by show n' + inc c' ≤ 9; omega) j

/-- The hypotheses can hold, and the answer depends on the input. -/
theorem class_units_differ :
    label [(true, true), (true, false)] ≤ 9 ∧ classUnit (network [(true, true), (true, false)]) 1 = true ∧
    classUnit (network [(true, false), (true, false)]) 1 = false := by
  decide

/-- With ten counted steps no class unit fires: the bound on the label is needed. -/
theorem ten_ones_no_class : ∀ j : Fin 10, classUnit (network (List.replicate 10 (true, true))) j.val = false := by
  decide

end BinaryAdding
