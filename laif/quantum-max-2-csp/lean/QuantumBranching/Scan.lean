import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The scan over independent parts

The input is the list of the minimum budgets of the parts, and a budget `k`. The scan runs through
`b = 0, 1, 2, ...`. In a round it tests the parts in order with budget `b`, as long as at least two
parts are unsolved. A part with minimum budget at most `b` is solved, and its budget adds to `used`.
Before a round with at least two unsolved parts, `k < 2 * b + used` answers no. This is the form of
`2 * b > k - used` that is safe for natural subtraction. The last part is decided against the
remaining budget, also in the safe form `used + c ≤ k`.

`scan` also returns the list of tests and the number of rounds. The definition is total, with the
measure `k + 1 - b`, and `scan_rounds_le` bounds the rounds by `k / 2 + 1`.

- `scan_answer_iff`: the scan answers yes iff the sum of the list is at most `k`.
- `scan_tests`: every test is made with at least two parts unsolved, and has `2 * b ≤ k` and
  `b ≤` the minimum budget of the tested part.
- `scan_tests_length`: there are at most `l.length * (k / 2 + 1)` tests.
- `value_call_log_measure`: value calls have log measure at most half of `log B v`, plus the constant.
-/

namespace QuantumBranching

/-- A test: the budget, the minimum budget of the tested part, and the number of unsolved parts. -/
structure Test where
  budget : ℕ
  part : ℕ
  unsolved : ℕ
  deriving DecidableEq, Repr

/-- The result of a round. -/
structure RoundResult where
  unsolved : List ℕ
  added : ℕ
  tests : List Test
  deriving Repr

/-- A round at budget `b`. `others` counts the unsolved parts kept earlier in the round. A part is
tested only if another part is unsolved. -/
def round (b : ℕ) : ℕ → List ℕ → RoundResult
  | _, [] => ⟨[], 0, []⟩
  | others, p :: rest =>
    if others + rest.length = 0 then ⟨[p], 0, []⟩
    else
      let t : Test := ⟨b, p, others + rest.length + 1⟩
      if p ≤ b then
        let r := round b others rest
        ⟨r.unsolved, p + r.added, t :: r.tests⟩
      else
        let r := round b (others + 1) rest
        ⟨p :: r.unsolved, r.added, t :: r.tests⟩

/-- The result of the scan. -/
structure ScanResult where
  answer : Bool
  tests : List Test
  rounds : ℕ
  deriving Repr

/-- The scan from a given budget and a given sum of solved budgets. -/
def scanAux (k : ℕ) (b used : ℕ) (l : List ℕ) : ScanResult :=
  match l with
  | [] => ⟨decide (used ≤ k), [], 0⟩
  | [c] => ⟨decide (used + c ≤ k), [], 0⟩
  | a :: c :: rest =>
    if k < 2 * b + used then ⟨false, [], 0⟩
    else
      let r := round b 0 (a :: c :: rest)
      let s := scanAux k (b + 1) (used + r.added) r.unsolved
      ⟨s.answer, r.tests ++ s.tests, s.rounds + 1⟩
termination_by k + 1 - b
decreasing_by omega

/-- The scan. -/
def scan (k : ℕ) (l : List ℕ) : ScanResult := scanAux k 0 0 l

section Round

variable (b : ℕ)

theorem round_sum (o : ℕ) (l : List ℕ) :
    (round b o l).unsolved.sum + (round b o l).added = l.sum := by
  induction l generalizing o with
  | nil => simp [round]
  | cons p rest ih =>
    simp only [round]
    split_ifs with h0
    · have hr : rest = [] := List.length_eq_zero_iff.mp (by omega)
      simp [hr]
    · have := ih o
      simp only [List.sum_cons]
      omega
    · have := ih (o + 1)
      simp only [List.sum_cons]
      omega

theorem round_length (o : ℕ) (l : List ℕ) : (round b o l).unsolved.length ≤ l.length := by
  induction l generalizing o with
  | nil => simp [round]
  | cons p rest ih =>
    simp only [round]
    split_ifs
    · simp
    · have := ih o
      simp only [List.length_cons]
      omega
    · have := ih (o + 1)
      simp only [List.length_cons]
      omega

theorem round_tests_length (o : ℕ) (l : List ℕ) : (round b o l).tests.length ≤ l.length := by
  induction l generalizing o with
  | nil => simp [round]
  | cons p rest ih =>
    simp only [round]
    split_ifs
    · simp
    · have := ih o
      simp only [List.length_cons]
      omega
    · have := ih (o + 1)
      simp only [List.length_cons]
      omega

theorem round_subset (o : ℕ) (l : List ℕ) : ∀ p ∈ (round b o l).unsolved, p ∈ l := by
  induction l generalizing o with
  | nil => simp [round]
  | cons p rest ih =>
    intro q hq
    simp only [round] at hq
    split_ifs at hq
    · simp only [List.mem_singleton] at hq
      simp [hq]
    · exact List.mem_cons_of_mem _ (ih o q hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · simp
      · exact List.mem_cons_of_mem _ (ih (o + 1) q hq)

/-- After a round that leaves two parts unsolved, these parts all need more than `b`. -/
theorem round_gt (o : ℕ) (l : List ℕ) :
    2 ≤ o + (round b o l).unsolved.length → ∀ p ∈ (round b o l).unsolved, b < p := by
  induction l generalizing o with
  | nil => simp [round]
  | cons p rest ih =>
    simp only [round]
    split_ifs with h0 h1
    · simp only [List.length_cons, List.length_nil]
      omega
    · exact ih o
    · intro h q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · omega
      · simp only [List.length_cons] at h
        exact ih (o + 1) (by omega) q hq

theorem round_tests (o : ℕ) (l : List ℕ) :
    ∀ t ∈ (round b o l).tests, t.budget = b ∧ 2 ≤ t.unsolved ∧ t.part ∈ l := by
  induction l generalizing o with
  | nil => simp [round]
  | cons p rest ih =>
    simp only [round]
    split_ifs with h0 h1
    · simp
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨rfl, by simp only; omega, by simp⟩
      · obtain ⟨h1, h2, h3⟩ := ih o t ht
        exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨rfl, by simp only; omega, by simp⟩
      · obtain ⟨h1, h2, h3⟩ := ih (o + 1) t ht
        exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩

end Round

theorem two_mul_le_sum {b : ℕ} {a c : ℕ} {rest : List ℕ}
    (h : ∀ x ∈ a :: c :: rest, b ≤ x) : 2 * b ≤ (a :: c :: rest).sum := by
  have ha := h a (by simp)
  have hc := h c (by simp)
  simp only [List.sum_cons]
  omega

/-- The unfolding of a step with at least two parts. -/
theorem scanAux_two (k b used a c : ℕ) (rest : List ℕ) :
    scanAux k b used (a :: c :: rest) =
      if k < 2 * b + used then ⟨false, [], 0⟩
      else
        ⟨(scanAux k (b + 1) (used + (round b 0 (a :: c :: rest)).added)
            (round b 0 (a :: c :: rest)).unsolved).answer,
          (round b 0 (a :: c :: rest)).tests ++
            (scanAux k (b + 1) (used + (round b 0 (a :: c :: rest)).added)
              (round b 0 (a :: c :: rest)).unsolved).tests,
          (scanAux k (b + 1) (used + (round b 0 (a :: c :: rest)).added)
            (round b 0 (a :: c :: rest)).unsolved).rounds + 1⟩ := by
  rw [scanAux]

/-- The invariant passes to the next round. -/
theorem invariant_next {b : ℕ} (l : List ℕ) :
    2 ≤ (round b 0 l).unsolved.length → ∀ x ∈ (round b 0 l).unsolved, b + 1 ≤ x := by
  intro h x hx
  have := round_gt b 0 l (by omega) x hx
  omega

/-- Correctness of the scan, under the invariant that unsolved parts need at least `b`. -/
theorem scanAux_answer (k : ℕ) (n : ℕ) : ∀ (b used : ℕ) (l : List ℕ), k + 1 - b ≤ n →
    (2 ≤ l.length → ∀ x ∈ l, b ≤ x) →
    ((scanAux k b used l).answer = true ↔ used + l.sum ≤ k) := by
  induction n with
  | zero =>
    intro b used l hn hinv
    match l, hinv with
    | [], _ => simp [scanAux]
    | [c], _ => simp [scanAux]
    | a :: c :: rest, hinv =>
      have hle := two_mul_le_sum (hinv (by simp))
      rw [scanAux_two, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      simp only [Bool.false_eq_true, false_iff]
      omega
  | succ n ih =>
    intro b used l hn hinv
    match l, hinv with
    | [], _ => simp [scanAux]
    | [c], _ => simp [scanAux]
    | a :: c :: rest, hinv =>
      have hle := two_mul_le_sum (hinv (by simp))
      rw [scanAux_two]
      split_ifs with h
      · simp only [false_iff]
        omega
      · simp only
        rw [ih (b + 1) _ _ (by omega) (invariant_next _)]
        have := round_sum b 0 (a :: c :: rest)
        omega

/-- **The answer of the scan.** It answers yes iff the sum of the list is at most `k`. -/
theorem scan_answer_iff (k : ℕ) (l : List ℕ) : (scan k l).answer = true ↔ l.sum ≤ k := by
  have := scanAux_answer k (k + 1) 0 0 l (by omega) (fun _ _ _ => Nat.zero_le _)
  simpa [scan] using this

/-- The properties of the tests of the scan. -/
theorem scanAux_tests (k : ℕ) (n : ℕ) : ∀ (b used : ℕ) (l : List ℕ), k + 1 - b ≤ n →
    (2 ≤ l.length → ∀ x ∈ l, b ≤ x) →
    ∀ t ∈ (scanAux k b used l).tests,
      2 ≤ t.unsolved ∧ 2 * t.budget ≤ k ∧ t.budget ≤ t.part := by
  induction n with
  | zero =>
    intro b used l hn hinv t ht
    match l, hinv, ht with
    | [], _, ht => simp [scanAux] at ht
    | [c], _, ht => simp [scanAux] at ht
    | a :: c :: rest, hinv, ht =>
      rw [scanAux_two, ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at ht
      simp at ht
  | succ n ih =>
    intro b used l hn hinv t ht
    match l, hinv, ht with
    | [], _, ht => simp [scanAux] at ht
    | [c], _, ht => simp [scanAux] at ht
    | a :: c :: rest, hinv, ht =>
      rw [scanAux_two] at ht
      split_ifs at ht with h
      · simp at ht
      · simp only [List.mem_append] at ht
        rcases ht with ht | ht
        · obtain ⟨h1, h2, h3⟩ := round_tests b 0 _ t ht
          have h4 := hinv (by simp) _ h3
          exact ⟨h2, by omega, by omega⟩
        · exact ih (b + 1) _ _ (by omega) (invariant_next _) t ht

/-- **The tests.** Every test is made with at least two parts unsolved, at a budget `b` with
`2 * b ≤ k`, and `b` is at most the minimum budget of the tested part. -/
theorem scan_tests (k : ℕ) (l : List ℕ) :
    ∀ t ∈ (scan k l).tests, 2 ≤ t.unsolved ∧ 2 * t.budget ≤ k ∧ t.budget ≤ t.part :=
  scanAux_tests k (k + 1) 0 0 l (by omega) (fun _ _ _ => Nat.zero_le _)

/-- The number of rounds and of tests. -/
theorem scanAux_counts (k : ℕ) (n : ℕ) : ∀ (b used : ℕ) (l : List ℕ), k + 1 - b ≤ n →
    (scanAux k b used l).rounds ≤ k / 2 + 1 - b ∧
      (scanAux k b used l).tests.length ≤ l.length * (k / 2 + 1 - b) := by
  induction n with
  | zero =>
    intro b used l hn
    match l with
    | [] => simp [scanAux]
    | [c] => simp [scanAux]
    | a :: c :: rest =>
      rw [scanAux_two, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      simp
  | succ n ih =>
    intro b used l hn
    match l with
    | [] => simp [scanAux]
    | [c] => simp [scanAux]
    | a :: c :: rest =>
      rw [scanAux_two]
      split_ifs with h
      · simp
      · simp only [List.length_append]
        obtain ⟨h1, h2⟩ := ih (b + 1) (used + (round b 0 (a :: c :: rest)).added)
          (round b 0 (a :: c :: rest)).unsolved (by omega)
        have hb : b ≤ k / 2 := by omega
        have hk : k / 2 + 1 - b = (k / 2 + 1 - (b + 1)) + 1 := by omega
        refine ⟨by omega, ?_⟩
        rw [hk, Nat.mul_add, Nat.mul_one]
        have h3 := round_tests_length b 0 (a :: c :: rest)
        have h4 := round_length b 0 (a :: c :: rest)
        have h5 : (round b 0 (a :: c :: rest)).unsolved.length * (k / 2 + 1 - (b + 1)) ≤
            (a :: c :: rest).length * (k / 2 + 1 - (b + 1)) := Nat.mul_le_mul_right _ h4
        omega

/-- **Termination, with a bound.** The scan makes at most `k / 2 + 1` rounds. -/
theorem scan_rounds_le (k : ℕ) (l : List ℕ) : (scan k l).rounds ≤ k / 2 + 1 :=
  (scanAux_counts k (k + 1) 0 0 l (by omega)).1

/-- The scan makes polynomially many tests. -/
theorem scan_tests_length (k : ℕ) (l : List ℕ) :
    (scan k l).tests.length ≤ l.length * (k / 2 + 1) :=
  (scanAux_counts k (k + 1) 0 0 l (by omega)).2

/-- **Value calls have log measure at most half.** Let the log measure of a part with budget `b` be at
most `β * b + c₀`, and let `β * k ≤ log B v`. -/
theorem value_call_log_measure (μ : ℕ → ℝ) {β c₀ logB : ℝ} (hβ : 0 ≤ β)
    (hμ : ∀ b, μ b ≤ β * b + c₀) {k : ℕ} (hk : β * k ≤ logB) (l : List ℕ) :
    ∀ t ∈ (scan k l).tests, μ t.budget ≤ (1 / 2) * logB + c₀ := by
  intro t ht
  have h2 : (2 : ℝ) * t.budget ≤ k := by exact_mod_cast (scan_tests k l t ht).2.1
  have := hμ t.budget
  nlinarith

/-- So (M2) holds, with `1/2` in place of `3/4`. -/
theorem value_call_M2 (μ : ℕ → ℝ) {β c₀ logB : ℝ} (hβ : 0 ≤ β)
    (hμ : ∀ b, μ b ≤ β * b + c₀) {k : ℕ} (hk : β * k ≤ logB) (hlog : 0 ≤ logB) (l : List ℕ) :
    ∀ t ∈ (scan k l).tests, μ t.budget ≤ (3 / 4) * logB + c₀ := by
  intro t ht
  have := value_call_log_measure μ hβ hμ hk l t ht
  linarith

/-- The scan evaluates: the sum `5` fits the budget `5`. -/
theorem scan_example_yes : (scan 5 [1, 2, 2]).answer = true := by decide +kernel

/-- The scan evaluates: the sum `5` does not fit the budget `4`. -/
theorem scan_example_no : (scan 4 [1, 2, 2]).answer = false := by decide +kernel

/-- A single part is decided against the budget, with no test, even when `2 * b > k` would hold. -/
theorem scan_example_single : (scan 3 [3]).answer = true ∧ (scan 3 [3]).tests = [] := by
  decide +kernel

end QuantumBranching
