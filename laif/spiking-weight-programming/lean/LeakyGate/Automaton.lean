import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Every finite automaton on one recurrent layer of leaky neurons with hard reset, at every decay

Neuron model: the potential after a step is `d * c + x`, where `x` is the drive of the step and `c` is the
potential carried over, which is 0 after a spike. The neuron spikes when the potential exceeds `1/2`.

For an automaton with states `Q`, input symbols `A`, transition function `δ` and start state `q0`, the network
has one gate for each pair `(q, a)` and one marker neuron with constant drive 1. The gate `(q, a)` has drive
`3/4 * (2 - [the state is q] - [the input is a])`, so it is silent exactly when the automaton is in state `q` and
reads `a`. "The state is `q'`" is the number of silent gates `(q, a)` of the previous step with `δ q a = q'`,
a linear function of the spikes of the previous step; the marker neuron corrects this term at the first step.
A silent gate has drive 0 and a gate that spikes is reset, so no potential is carried over and the decay `d`
does not enter.

`network_hot`: for every real decay `d` and every non-empty input word, after the last step exactly the gate
`(state before the last symbol, last symbol)` is silent.
`readout_eq_state`: the linear readout for state `q'` is 1 if the automaton is in `q'` after the word and 0
otherwise.
`hot_unique`, `not_hot_init`, `parity_readouts` and `parity_net_ne_or` show that the statement has content: the\nreadout takes both values and differs from the state of another automaton.
-/

namespace LeakyGate.Automaton

set_option linter.unusedSectionVars false

variable {Q A : Type} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]

/-- Potentials and spikes of the gates, and potential and spike of the marker neuron. -/
structure Net (Q A : Type) where
  v : Q × A → ℝ
  y : Q × A → Bool
  gv : ℝ
  g : Bool

/-- Before the first step: all potentials 0, no spikes. -/
def init : Net Q A := ⟨fun _ => 0, fun _ => false, 0, false⟩

/-- 1 for a silent gate, 0 for a gate that spiked. -/
def sil (y : Q × A → Bool) (p : Q × A) : ℝ := if y p then 0 else 1

/-- Linear function of the spikes of the previous step that is 1 if the automaton is in state `q` and 0
otherwise. The second term, switched by the marker neuron, sets the start state at the first step. -/
def stateTerm (δ : Q → A → Q) (q0 : Q) (s : Net Q A) (q : Q) : ℝ :=
  (∑ p : Q × A, if δ p.1 p.2 = q then sil s.y p else 0)
    - (if s.g then 0 else (∑ p : Q × A, if δ p.1 p.2 = q then (1 : ℝ) else 0) - (if q = q0 then 1 else 0))

/-- Drive of the gate `p` when the input symbol is `a`. -/
noncomputable def drive (δ : Q → A → Q) (q0 : Q) (s : Net Q A) (a : A) (p : Q × A) : ℝ :=
  3 / 4 * (2 - stateTerm δ q0 s p.1 - (if p.2 = a then 1 else 0))

/-- One step of the network at decay `d` with input symbol `a`. -/
noncomputable def step (d : ℝ) (δ : Q → A → Q) (q0 : Q) (s : Net Q A) (a : A) : Net Q A where
  v := fun p => d * s.v p * (if s.y p then 0 else 1) + drive δ q0 s a p
  y := fun p => decide (1 / 2 < d * s.v p * (if s.y p then 0 else 1) + drive δ q0 s a p)
  gv := d * s.gv * (if s.g then 0 else 1) + 1
  g := decide (1 / 2 < d * s.gv * (if s.g then 0 else 1) + 1)

noncomputable def run (d : ℝ) (δ : Q → A → Q) (q0 : Q) : Net Q A → List A → Net Q A
  | s, [] => s
  | s, a :: l => run d δ q0 (step d δ q0 s a) l

/-- The marker neuron spiked, exactly the gate `(q, a)` is silent, and its potential is 0. -/
def Hot (s : Net Q A) (q : Q) (a : A) : Prop :=
  s.g = true ∧ ∀ p : Q × A, s.y p = decide (p ≠ (q, a)) ∧ (p = (q, a) → s.v p = 0)

/-- State and symbol of the last step, starting from state `p.1` reading `p.2` and then the word `l`. -/
def track (δ : Q → A → Q) : Q × A → List A → Q × A
  | p, [] => p
  | p, x :: l => track δ (δ p.1 p.2, x) l

theorem stateTerm_init (δ : Q → A → Q) (q0 q : Q) :
    stateTerm δ q0 (init : Net Q A) q = if q = q0 then 1 else 0 := by
  have h : ∀ p : Q × A, sil (init : Net Q A).y p = 1 := fun _ => rfl
  unfold stateTerm
  simp only [h]
  have hg : (init : Net Q A).g = false := rfl
  rw [hg]
  simp

theorem stateTerm_hot (δ : Q → A → Q) (q0 : Q) {s : Net Q A} {q : Q} {a : A} (h : Hot s q a) (q' : Q) :
    stateTerm δ q0 s q' = if q' = δ q a then 1 else 0 := by
  obtain ⟨hg, hy⟩ := h
  have hsum : (∑ p : Q × A, if δ p.1 p.2 = q' then sil s.y p else 0) = if q' = δ q a then (1 : ℝ) else 0 := by
    rw [Finset.sum_eq_single (q, a)]
    · have hs : s.y (q, a) = false := by rw [(hy (q, a)).1]; simp
      by_cases hq : q' = δ q a
      · simp [sil, hs, hq]
      · have hq' : ¬ δ q a = q' := fun e => hq e.symm
        simp [hq, hq']
    · intro b _ hb
      have hs : s.y b = true := by rw [(hy b).1]; simpa using hb
      simp [sil, hs]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  unfold stateTerm
  rw [hsum, hg]
  simp

/-- If no potential is carried over and the state term is the indicator of `cur`, then after a step with
symbol `a` exactly the gate `(cur, a)` is silent. -/
theorem step_hot (d : ℝ) (δ : Q → A → Q) (q0 : Q) {s : Net Q A} {cur : Q} (a : A)
    (hv : ∀ p, s.y p = false → s.v p = 0) (hgv : s.g = false → s.gv = 0)
    (hst : ∀ q', stateTerm δ q0 s q' = if q' = cur then 1 else 0) :
    Hot (step d δ q0 s a) cur a := by
  have hpot : ∀ p, d * s.v p * (if s.y p then (0 : ℝ) else 1) = 0 := by
    intro p
    cases hy : s.y p
    · simp [hv p hy]
    · simp
  have hval : ∀ p : Q × A, d * s.v p * (if s.y p then (0 : ℝ) else 1) + drive δ q0 s a p
      = 3 / 4 * (2 - (if p.1 = cur then 1 else 0) - (if p.2 = a then 1 else 0)) := by
    intro p
    rw [hpot p, drive, hst p.1]
    ring
  have hmark : d * s.gv * (if s.g then (0 : ℝ) else 1) = 0 := by
    cases hg : s.g
    · simp [hgv hg]
    · simp
  refine ⟨?_, ?_⟩
  · show decide ((1 : ℝ) / 2 < d * s.gv * (if s.g then 0 else 1) + 1) = true
    rw [hmark]
    exact decide_eq_true (by norm_num)
  · intro p
    have hy : (step d δ q0 s a).y p
        = decide ((1 : ℝ) / 2 < 3 / 4 * (2 - (if p.1 = cur then 1 else 0) - (if p.2 = a then 1 else 0))) := by
      show decide ((1 : ℝ) / 2 < d * s.v p * (if s.y p then 0 else 1) + drive δ q0 s a p) = _
      rw [hval p]
    have hvv : (step d δ q0 s a).v p
        = 3 / 4 * (2 - (if p.1 = cur then 1 else 0) - (if p.2 = a then 1 else 0)) := hval p
    by_cases h1 : p.1 = cur
    · by_cases h2 : p.2 = a
      · have hp : p = (cur, a) := Prod.ext h1 h2
        refine ⟨?_, fun _ => ?_⟩
        · rw [hy, if_pos h1, if_pos h2, decide_eq_false (by norm_num), decide_eq_false (not_not.mpr hp)]
        · rw [hvv, if_pos h1, if_pos h2]; norm_num
      · have hp : p ≠ (cur, a) := fun e => h2 (by rw [e])
        refine ⟨?_, fun e => absurd e hp⟩
        rw [hy, if_pos h1, if_neg h2, decide_eq_true (by norm_num), decide_eq_true hp]
    · have hp : p ≠ (cur, a) := fun e => h1 (by rw [e])
      refine ⟨?_, fun e => absurd e hp⟩
      by_cases h2 : p.2 = a
      · rw [hy, if_neg h1, if_pos h2, decide_eq_true (by norm_num), decide_eq_true hp]
      · rw [hy, if_neg h1, if_neg h2, decide_eq_true (by norm_num), decide_eq_true hp]

theorem hot_carry {s : Net Q A} {q : Q} {a : A} (h : Hot s q a) :
    (∀ p, s.y p = false → s.v p = 0) ∧ (s.g = false → s.gv = 0) := by
  refine ⟨fun p hp => (h.2 p).2 ?_, fun hg => ?_⟩
  · have e := (h.2 p).1
    rw [hp] at e
    exact of_not_not (of_decide_eq_false e.symm)
  · rw [h.1] at hg; exact absurd hg (by simp)

theorem run_hot (d : ℝ) (δ : Q → A → Q) (q0 : Q) (l : List A) : ∀ (s : Net Q A) (p : Q × A),
    Hot s p.1 p.2 → Hot (run d δ q0 s l) (track δ p l).1 (track δ p l).2 := by
  induction l with
  | nil => intro s p h; exact h
  | cons x l ih =>
    intro s p h
    exact ih (step d δ q0 s x) (δ p.1 p.2, x)
      (step_hot d δ q0 x (hot_carry h).1 (hot_carry h).2 (stateTerm_hot δ q0 h))

/-- After the word `a :: l`, at every decay `d`, exactly one gate is silent: the one for the state before the
last symbol and the last symbol. -/
theorem network_hot (d : ℝ) (δ : Q → A → Q) (q0 : Q) (a : A) (l : List A) :
    Hot (run d δ q0 (init : Net Q A) (a :: l)) (track δ (q0, a) l).1 (track δ (q0, a) l).2 :=
  run_hot d δ q0 l _ (q0, a)
    (step_hot d δ q0 a (fun _ _ => rfl) (fun _ => rfl) (stateTerm_init δ q0))

theorem track_next (δ : Q → A → Q) (l : List A) : ∀ p : Q × A,
    δ (track δ p l).1 (track δ p l).2 = l.foldl δ (δ p.1 p.2) := by
  induction l with
  | nil => intro p; rfl
  | cons x l ih => intro p; exact ih (δ p.1 p.2, x)

/-- The linear readout for state `q'` after a non-empty word is 1 if the automaton is in `q'` and 0 otherwise,
at every decay. -/
theorem readout_eq_state (d : ℝ) (δ : Q → A → Q) (q0 : Q) (a : A) (l : List A) (q' : Q) :
    stateTerm δ q0 (run d δ q0 (init : Net Q A) (a :: l)) q' = if q' = (a :: l).foldl δ q0 then 1 else 0 := by
  rw [stateTerm_hot δ q0 (network_hot d δ q0 a l) q', track_next δ l (q0, a)]
  rfl

/-- The pattern determines the state and the symbol. -/
theorem hot_unique {s : Net Q A} {q q' : Q} {a a' : A} (h : Hot s q a) (h' : Hot s q' a') :
    (q, a) = (q', a') := by
  have e := (h'.2 (q, a)).1
  rw [(h.2 (q, a)).1, decide_eq_false (not_not.mpr rfl)] at e
  exact of_not_not (of_decide_eq_false e.symm)

/-- Before the first step no pattern of this kind is present. -/
theorem not_hot_init (q : Q) (a : A) : ¬ Hot (init : Net Q A) q a := by
  intro h
  have hg : (init : Net Q A).g = false := rfl
  rw [h.1] at hg
  exact absurd hg (by simp)

/-- Parity of the number of `true` symbols: the readout for the odd state is 1 after one `true` and 0 after
two, at every decay. -/
theorem parity_readouts (d : ℝ) :
    stateTerm (fun q a : Bool => xor q a) false (run d (fun q a : Bool => xor q a) false init [true]) true = 1 ∧
    stateTerm (fun q a : Bool => xor q a) false (run d (fun q a : Bool => xor q a) false init [true, true]) true
      = 0 := by
  constructor
  · rw [readout_eq_state]; simp
  · rw [readout_eq_state]; simp

/-- The network of the parity automaton does not give the state of another automaton: after two `true`
symbols the automaton that remembers whether a `true` occurred is in its `true` state, and the readout for that
state is 0. -/
theorem parity_net_ne_or (d : ℝ) :
    stateTerm (fun q a : Bool => xor q a) false (run d (fun q a : Bool => xor q a) false init [true, true]) true
      ≠ if true = [true, true].foldl (fun q a : Bool => q || a) false then 1 else 0 := by
  rw [readout_eq_state]; simp

end LeakyGate.Automaton
