import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A leaky neuron with hard reset as a threshold gate

Neuron model: with carried potential `c` (0 after a spike), the potential after an input `x` is `d * c + x`,
the neuron spikes iff this exceeds the threshold `θ`, and after a spike the carried potential is 0.

Suppose every input is either low, in `[lo, L]`, or high, at least `F`. `Margins` states conditions on the decay
`d` under which the potential left over from earlier steps never changes the outcome: the neuron spikes exactly
at the high inputs (`spikes_eq`), for input sequences of any length.

The last part checks the conditions for the neurons of the localization network at decay 3/10 and
threshold 1/2, and shows that the statement has content: both outcomes occur, and at decay 1/2 the same neuron
fires at low inputs.
-/

namespace LeakyGate

/-- Conditions for a gate: carried potentials stay in `[m, M]`. -/
structure Margins (d θ lo L F m M : ℝ) : Prop where
  d_nonneg : 0 ≤ d
  m_nonpos : m ≤ 0
  M_nonneg : 0 ≤ M
  M_le : M ≤ θ
  low : m ≤ d * m + lo
  high : d * M + L ≤ M
  fire : θ < d * m + F

variable {d θ lo L F m M : ℝ}

/-- A low input gives no spike and keeps the carried potential in `[m, M]`. -/
theorem low_step (h : Margins d θ lo L F m M) {c x : ℝ} (hm : m ≤ c) (hM : c ≤ M)
    (hlo : lo ≤ x) (hL : x ≤ L) :
    ¬ θ < d * c + x ∧ m ≤ d * c + x ∧ d * c + x ≤ M := by
  have h1 : d * c ≤ d * M := mul_le_mul_of_nonneg_left hM h.d_nonneg
  have h2 : d * m ≤ d * c := mul_le_mul_of_nonneg_left hm h.d_nonneg
  have hle : d * c + x ≤ M := by linarith [h.high]
  refine ⟨?_, ?_, hle⟩
  · have := h.M_le
    linarith
  · linarith [h.low]

/-- A high input gives a spike. -/
theorem high_step (h : Margins d θ lo L F m M) {c x : ℝ} (hm : m ≤ c) (hF : F ≤ x) :
    θ < d * c + x := by
  have h2 : d * m ≤ d * c := mul_le_mul_of_nonneg_left hm h.d_nonneg
  linarith [h.fire]

/-- Low inputs are below high inputs. -/
theorem L_lt_F (h : Margins d θ lo L F m M) : L < F := by
  have h1 : 0 ≤ d * M := mul_nonneg h.d_nonneg h.M_nonneg
  have h2 : d * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h.d_nonneg h.m_nonpos
  linarith [h.high, h.M_le, h.fire]

/-- Spikes of the neuron along a sequence of inputs, from carried potential `c`. -/
noncomputable def spikes (d θ : ℝ) : ℝ → List ℝ → List Bool
  | _, [] => []
  | c, x :: l => decide (θ < d * c + x) :: spikes d θ (if θ < d * c + x then 0 else d * c + x) l

/-- The neuron spikes exactly at the high inputs, whatever came before. -/
theorem spikes_eq (h : Margins d θ lo L F m M) (c : ℝ) (hm : m ≤ c) (hM : c ≤ M) (l : List ℝ)
    (hl : ∀ x ∈ l, (lo ≤ x ∧ x ≤ L) ∨ F ≤ x) :
    spikes d θ c l = l.map (fun x => decide (F ≤ x)) := by
  induction l generalizing c with
  | nil => rfl
  | cons x l ih =>
    have hx := hl x (List.mem_cons_self ..)
    have hl' : ∀ y ∈ l, (lo ≤ y ∧ y ≤ L) ∨ F ≤ y := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rcases hx with ⟨hlo, hL⟩ | hF
    · obtain ⟨hno, h1, h2⟩ := low_step h hm hM hlo hL
      have hnF : ¬ F ≤ x := by
        have := L_lt_F h
        intro hF
        linarith
      simp only [spikes, List.map_cons, if_neg hno, decide_eq_false hno, decide_eq_false hnF]
      rw [ih _ h1 h2 hl']
    · have hyes := high_step h hm hF
      simp only [spikes, List.map_cons, if_pos hyes, decide_eq_true hyes, decide_eq_true hF]
      rw [ih 0 h.m_nonpos h.M_nonneg hl']

/-! ### The neurons of the localization network, decay 3/10 and threshold 1/2 -/

/-- Gate of two unit inputs with weight 0.75 and bias -0.42: drives -0.42, 0.33 (low) and 1.08 (high). -/
theorem and_gate : Margins (3 / 10) (1 / 2) (-42 / 100) (33 / 100) (108 / 100) (-6 / 10) (48 / 100) := by
  constructor <;> norm_num

/-- Thermometer unit with bias -0.67: drives from -1.67 to 0.33 (levels -1 to 1, low) and from 1.33 (level 2). -/
theorem counter_unit : Margins (3 / 10) (1 / 2) (-167 / 100) (33 / 100) (133 / 100) (-24 / 10) (48 / 100) := by
  constructor <;> norm_num

/-- Crossing unit: drives -1.17, -0.42, 0.33 (low) and 1.08 (high). -/
theorem crossing_unit : Margins (3 / 10) (1 / 2) (-117 / 100) (33 / 100) (108 / 100) (-17 / 10) (48 / 100) := by
  constructor <;> norm_num

/-- Relay unit of the third layer: drive 0 (low) or 1 (high). -/
theorem relay_unit : Margins (3 / 10) (1 / 2) 0 0 1 0 0 := by
  constructor <;> norm_num

/-! ### Content of the statement

The four theorems above show that the hypotheses of `spikes_eq` can hold, with the parameters of the network.
The next lemmas show that its conclusion takes both values and that it fails without the margins. -/

/-- With the margins of `and_gate` the neuron is silent at a low input and fires at a high one. -/
theorem and_gate_outcomes :
    spikes (3 / 10) (1 / 2) 0 [33 / 100, 108 / 100, 33 / 100] = [false, true, false] := by
  norm_num [spikes]

/-- At decay 1/2 the same low input, repeated, makes the neuron fire: the conclusion of `spikes_eq` fails
when the margins do not hold. -/
theorem low_inputs_fire_at_decay_half :
    spikes (1 / 2) (1 / 2) 0 [33 / 100, 33 / 100, 33 / 100] = [false, false, true] := by
  norm_num [spikes]

/-- The margins of `and_gate` cannot be met at decay 1/2 with the same drives, for any range `[m, M]`. -/
theorem no_and_gate_margins_at_decay_half (m M : ℝ) :
    ¬ Margins (1 / 2) (1 / 2) (-42 / 100) (33 / 100) (108 / 100) m M := by
  intro h
  have h1 := h.high
  have h2 := h.M_le
  linarith

end LeakyGate
