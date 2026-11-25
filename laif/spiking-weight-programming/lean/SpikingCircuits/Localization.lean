/-!
# The localization task and the thermometer counter

A robot starts at the origin with heading 0 and receives actions: stop, go straight, turn left, turn right.
Going straight changes the x coordinate by +1 with heading 1 and by -1 with heading 3. The label of a
sequence is whether the final x coordinate is at least 1.

The network tracks x with a thermometer code `u : Int → Bool`, where `u k` stands for `k ≤ x`, and updates
every unit by one threshold function of the unit, its two neighbours and the increment of the step. Two
further units fire when x goes from 0 to 1 and from 1 to 0. The readout adds the first and subtracts the
second over the whole sequence.

`readout_eq_label`: this sum is 1 if the final x is at least 1, and 0 otherwise, for every action sequence.
The thermometer code is unbounded here. The file uses core Lean only.
-/

namespace Localization

inductive Act | stop | straight | left | right
  deriving DecidableEq, Repr

/-- Heading after an action; headings are 0, 1, 2, 3. -/
def turn (h : Nat) : Act → Nat
  | .left => (h + 3) % 4
  | .right => (h + 1) % 4
  | _ => h

/-- Change of the x coordinate caused by an action at heading `h`. -/
def incr (h : Nat) : Act → Int
  | .straight => if h = 1 then 1 else if h = 3 then -1 else 0
  | _ => 0

theorem incr_cases (h : Nat) (a : Act) : incr h a = -1 ∨ incr h a = 0 ∨ incr h a = 1 := by
  cases a
  case straight =>
    unfold incr
    by_cases h1 : h = 1 <;> by_cases h3 : h = 3 <;> simp [h1, h3]
  all_goals simp [incr]

/-- Final x coordinate of the robot from heading `h` and coordinate `x`. -/
def finalX : Nat → Int → List Act → Int
  | _, x, [] => x
  | h, x, a :: l => finalX (turn h a) (x + incr h a) l

def b2i (b : Bool) : Int := if b then 1 else 0

/-- One step of a thermometer unit: a threshold function of the unit, its neighbours and the increment. -/
def unext (u : Int → Bool) (d : Int) (k : Int) : Bool :=
  decide (2 ≤ b2i (u (k - 1)) + b2i (u k) + b2i (u (k + 1)) + d)

/-- The thermometer code of x. -/
def thermo (x : Int) : Int → Bool := fun k => decide (k ≤ x)

theorem unext_thermo (x d : Int) (hd : d = -1 ∨ d = 0 ∨ d = 1) :
    unext (thermo x) d = thermo (x + d) := by
  funext k
  simp only [unext, thermo, b2i]
  by_cases h1 : k - 1 ≤ x <;> by_cases h2 : k ≤ x <;> by_cases h3 : k + 1 ≤ x <;>
    simp [h1, h2, h3] <;> omega

/-- Output of the two crossing units in one step: +1 when x goes from 0 to 1, -1 when it goes from 1 to 0.
The first unit reads `u 0`, `u 1` and an increment, the second reads `u 1`, `u 2` and a decrement. -/
def event (u : Int → Bool) (d : Int) : Int :=
  b2i (u 0 && !u 1 && decide (d = 1)) - b2i (u 1 && !u 2 && decide (d = -1))

def ind (x : Int) : Int := if 1 ≤ x then 1 else 0

theorem event_thermo (x d : Int) (hd : d = -1 ∨ d = 0 ∨ d = 1) :
    event (thermo x) d = ind (x + d) - ind x := by
  simp only [event, thermo, b2i, ind]
  rcases hd with hd | hd | hd <;> subst hd <;>
    by_cases h0 : (0 : Int) ≤ x <;> by_cases h1 : (1 : Int) ≤ x <;> by_cases h2 : (2 : Int) ≤ x <;>
    simp [h0, h1, h2] <;> omega

/-- The network: heading, thermometer code, and the running sum of the readout. -/
def readout : Nat → (Int → Bool) → List Act → Int
  | _, _, [] => 0
  | h, u, a :: l => event u (incr h a) + readout (turn h a) (unext u (incr h a)) l

theorem readout_from (h : Nat) (x : Int) (l : List Act) :
    readout h (thermo x) l = ind (finalX h x l) - ind x := by
  induction l generalizing h x with
  | nil => simp [readout, finalX]
  | cons a l ih =>
    simp only [readout, finalX]
    rw [unext_thermo x _ (incr_cases h a), ih, event_thermo x _ (incr_cases h a)]
    omega

/-- From the start (heading 0, x = 0) the summed readout is the label of the sequence. -/
theorem readout_eq_label (l : List Act) :
    readout 0 (thermo 0) l = ind (finalX 0 0 l) := by
  rw [readout_from]; simp [ind]

/-- The label has content: turn right, go straight gives x = 1; turning around and going straight gives 0. -/
example : ind (finalX 0 0 [.right, .straight]) = 1 := by decide
example : ind (finalX 0 0 [.right, .straight, .right, .right, .straight]) = 0 := by decide

end Localization
