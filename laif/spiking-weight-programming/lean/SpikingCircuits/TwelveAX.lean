/-!
# The 12AX task and the four-flag state machine

`target` is the target function of the 12AX task: it remembers the last digit and the last relevant
letter, and answers `true` (R) at an `X` that follows `1 … A …`, or at a `Y` that follows `2 … B …`.

`machine` is the state machine that the spiking circuit implements with four latches:
`c1`, `c2` (last digit was 1, 2) and `px`, `py` (armed for X, armed for Y).

`machine_eq_target`: both give the same outputs on every symbol sequence.
`target_not_constant` and `machineNoClear_ne_target` show that the statement has content.
The file uses core Lean only.
-/

namespace TwelveAX

inductive Sym | one | two | A | B | C | X | Y | Z
  deriving DecidableEq, Repr

inductive Digit | none | one | two
  deriving DecidableEq

inductive Letter | none | A | B | X | Y
  deriving DecidableEq

/-- State of the target function: last digit and last relevant letter. -/
structure Ref where
  num : Digit
  letter : Letter

/-- One step of the target function: new state and output. -/
def refStep (r : Ref) : Sym → Ref × Bool
  | .one => (⟨.one, .none⟩, false)
  | .two => (⟨.two, .none⟩, false)
  | .A => (⟨r.num, .A⟩, false)
  | .B => (⟨r.num, .B⟩, false)
  | .C => (r, false)
  | .Z => (r, false)
  | .X => (⟨r.num, .X⟩, decide (r.num = .one ∧ r.letter = .A))
  | .Y => (⟨r.num, .Y⟩, decide (r.num = .two ∧ r.letter = .B))

/-- Outputs of the target function along a sequence. -/
def target : Ref → List Sym → List Bool
  | _, [] => []
  | r, s :: l => (refStep r s).2 :: target (refStep r s).1 l

/-- State of the machine: the four latches. -/
structure Flags where
  c1 : Bool
  c2 : Bool
  px : Bool
  py : Bool
  deriving DecidableEq

/-- One step of the machine. A digit sets its context latch and clears the rest. `A` arms `px` in
context 1 and clears `py`; `B` arms `py` in context 2 and clears `px`. `X` answers `px`, `Y` answers
`py`, and both clear `px` and `py`. -/
def machStep (f : Flags) : Sym → Flags × Bool
  | .one => (⟨true, false, false, false⟩, false)
  | .two => (⟨false, true, false, false⟩, false)
  | .A => (⟨f.c1, f.c2, f.px || f.c1, false⟩, false)
  | .B => (⟨f.c1, f.c2, false, f.py || f.c2⟩, false)
  | .C => (f, false)
  | .Z => (f, false)
  | .X => (⟨f.c1, f.c2, false, false⟩, f.px)
  | .Y => (⟨f.c1, f.c2, false, false⟩, f.py)

/-- Outputs of the machine along a sequence. -/
def machine : Flags → List Sym → List Bool
  | _, [] => []
  | f, s :: l => (machStep f s).2 :: machine (machStep f s).1 l

/-- The latch values that belong to a state of the target function. -/
def flags (r : Ref) : Flags :=
  ⟨decide (r.num = .one), decide (r.num = .two),
   decide (r.num = .one ∧ r.letter = .A), decide (r.num = .two ∧ r.letter = .B)⟩

theorem step_eq (r : Ref) (s : Sym) :
    machStep (flags r) s = (flags (refStep r s).1, (refStep r s).2) := by
  obtain ⟨n, l⟩ := r
  cases n <;> cases l <;> cases s <;> rfl

theorem machine_eq_target_from (r : Ref) (l : List Sym) :
    machine (flags r) l = target r l := by
  induction l generalizing r with
  | nil => rfl
  | cons s l ih =>
    simp only [machine, target, step_eq]
    rw [ih]

/-- From the empty start state, the machine and the target function agree on every sequence. -/
theorem machine_eq_target (l : List Sym) :
    machine ⟨false, false, false, false⟩ l = target ⟨.none, .none⟩ l :=
  machine_eq_target_from ⟨.none, .none⟩ l

/-! ### Content of the statement

`machine_eq_target` has no hypotheses. The lemmas below show that it is not an equality of constant functions,
and that a machine with one transition changed does not satisfy it. -/

/-- The target function has content: `1 A C X` ends with an R, and a second `X` does not. -/
theorem target_example :
    target ⟨.none, .none⟩ [.one, .A, .C, .X, .X] = [false, false, false, true, false] := by decide

/-- The target is not constant: it answers R on one sequence and never on another of the same length. -/
theorem target_not_constant :
    target ⟨.none, .none⟩ [.one, .A, .X] ≠ target ⟨.none, .none⟩ [.two, .A, .X] := by decide

/-- A machine that forgets to clear the armed flags at `X` and `Y`. -/
def machStepNoClear (f : Flags) : Sym → Flags × Bool
  | .X => (f, f.px)
  | .Y => (f, f.py)
  | s => machStep f s

def machineNoClear : Flags → List Sym → List Bool
  | _, [] => []
  | f, s :: l => (machStepNoClear f s).2 :: machineNoClear (machStepNoClear f s).1 l

/-- The changed machine disagrees with the target on `1 A X X`, so the statement can fail for a wrong machine. -/
theorem machineNoClear_ne_target :
    machineNoClear ⟨false, false, false, false⟩ [.one, .A, .X, .X]
      ≠ target ⟨.none, .none⟩ [.one, .A, .X, .X] := by decide

end TwelveAX
