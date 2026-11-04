import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The quantum model and the quantum facts taken as hypotheses

Nothing here is an `axiom`. Every quantum fact is a `def … : Prop`, and a theorem using one has it as an explicit
argument. `Axioms.lean` confirms that only the three standard axioms appear.

There are two layers.

**Concrete layer.** A `QAlg` is a sequence of unitaries with phase queries to a bit string, as in the sibling projects.

* `BBHTSearch`: quantum search. Cost and correctness in one statement about real circuits.
* `DurrHoyerMin`: quantum minimum finding, with queries to a comparison bit string.
* `ORLowerBound`: the OR lower bound.

These are published theorems, used as hypotheses only. Only `ORBound` enters a proof here, in `LowerBoundQuery.lean`.

**Accounting layer.** The README nest searches, and a nested search with a bounded-error inner routine is a statement
about programs, not about one `QAlg`. The accounting does not model that. It uses abstract routines:

* `search N x δ` and `minFind N f δ` are distributions on outcomes.
* `GroverCorrect`, `MinCorrect`: they fail with probability at most `δ`.
* `GroverCost`, `MinCost`: they make `O(√N log(1/δ))` calls of the predicate.
* A call of a predicate of inner cost `I` is charged `2 I`, for compute and uncompute (`searchQ`, `minQ` in `Cost.lean`).

`primitives_consistent` exhibits a model of all four, so together they cannot be inconsistent. The witness is exact
classical search with the desired count written in. So this shows logical consistency only, and says nothing about
physical realizability. The bridge between the two layers, that is, that a coherent implementation exists with these
costs, is what `README.md` argues in Lemma 6 and is not formalized.
-/

open Finset

namespace Strings

/-! ## Concrete quantum query algorithms -/

/-- A `T`-query quantum algorithm on the basis `St` with outputs in `O`. -/
structure QAlg (Q : Type) (T : ℕ) (St : Type) [Fintype St] [DecidableEq St] (O : Type) where
  /-- The position queried on a basis state, if any. -/
  ix : St → Option Q
  U : Fin (T + 1) → Matrix.unitaryGroup St ℂ
  init : St
  out : St → O

variable {Q : Type} {St : Type} [Fintype St] [DecidableEq St] {O : Type} {T : ℕ}

/-- The phase of a query on a basis state. -/
def QAlg.phase (A : QAlg Q T St O) (x : Q → Bool) (b : St) : ℂ :=
  match A.ix b with
  | none => 1
  | some q => if x q then -1 else 1

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def QAlg.state (A : QAlg Q T St O) (x : Q → Bool) : (t : ℕ) → t ≤ T → St → ℂ
  | 0, _ => (A.U ⟨0, Nat.succ_pos T⟩ : Matrix St St ℂ).mulVec (Pi.single A.init 1)
  | t + 1, h => (A.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix St St ℂ).mulVec
      fun b => A.phase x b * A.state x t (Nat.le_of_succ_le h) b

open Classical in
/-- The probability that the final measurement reports `o`. -/
noncomputable def QAlg.prob (A : QAlg Q T St O) (x : Q → Bool) (o : O) : ℝ :=
  ∑ b, if A.out b = o then Complex.normSq (A.state x T le_rfl b) else 0

/-- **Quantum search**, with a final check of the outcome and repetition. On `N ≥ 1` candidates
and for `δ ∈ (0, 1/2]` there is an algorithm with `O(√N log(1/δ))` queries that on every input never outputs an unmarked
item, outputs "none" with certainty if no item is marked, and if some item is marked outputs "none" with probability at
most `δ`. -/
def BBHTSearch : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (δ : ℝ), 1 ≤ N → 0 < δ → δ ≤ 1 / 2 →
    ∃ (T : ℕ) (St : Type) (_ : Fintype St) (_ : DecidableEq St) (A : QAlg (Fin N) T St (Option (Fin N))),
      (T : ℝ) ≤ c * Real.sqrt N * Real.log (1 / δ) ∧
      ∀ x : Fin N → Bool,
        (∀ i, x i = false → A.prob x (some i) = 0) ∧
        ((∀ i, x i = false) → A.prob x none = 1) ∧
        ((∃ i, x i = true) → A.prob x none ≤ δ)

/-- The comparison bit string of a key function, the oracle of minimum finding. -/
def cmpBits {N : ℕ} (f : Fin N → ℕ) (q : Fin N × Fin N) : Bool := decide (f q.1 < f q.2)

/-- **Minimum finding.** On `N ≥ 1` items and for `δ ∈ (0, 1/2]`, `O(√N log(1/δ))` comparison queries
output an item of least key with probability at least `1 - δ`. -/
def DurrHoyerMin : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (δ : ℝ), 1 ≤ N → 0 < δ → δ ≤ 1 / 2 →
    ∃ (T : ℕ) (St : Type) (_ : Fintype St) (_ : DecidableEq St) (A : QAlg (Fin N × Fin N) T St (Fin N)),
      (T : ℝ) ≤ c * Real.sqrt N * Real.log (1 / δ) ∧
      ∀ f : Fin N → ℕ, 1 - δ ≤ ∑ i, if ∀ j, f i ≤ f j then A.prob (cmpBits f) i else 0

/-- The bit string with a single `1`, at `i`. -/
def singleBit {N : ℕ} (i : Fin N) (j : Fin N) : Bool := decide (j = i)

/-- The OR lower bound with the constant `c`. -/
def ORBound (c : ℝ) : Prop :=
  ∀ (N T : ℕ) (St : Type) (_ : Fintype St) (_ : DecidableEq St) (A : QAlg (Fin N) T St Bool),
    2 / 3 ≤ A.prob (fun _ => false) false →
    (∀ i : Fin N, 2 / 3 ≤ A.prob (singleBit i) true) →
    c * Real.sqrt N ≤ T

/-- **The OR lower bound.** An algorithm that tells the zero string from
every string with a single `1`, with error at most `1/3`, needs `Ω(√N)` queries. -/
def ORLowerBound : Prop := ∃ c : ℝ, 0 < c ∧ ORBound c

/-! ## Abstract routines for the accounting -/

/-- The abstract routines, and the count of predicate calls they make. -/
structure Primitives where
  /-- Search on `N` items for a marked one, with failure parameter `δ`. -/
  search : (N : ℕ) → (Fin N → Bool) → ℝ → PMF (Option (Fin N))
  /-- Minimum finding on `N + 1` items, with failure parameter `δ`. -/
  minFind : (N : ℕ) → (Fin (N + 1) → ℕ) → ℝ → PMF (Fin (N + 1))
  /-- The predicate calls of a search. -/
  qS : ℕ → ℝ → ℝ
  /-- The predicate calls of a minimum finding. -/
  qM : ℕ → ℝ → ℝ

/-- A good outcome of a search: a marked item, or "none" if nothing is marked. -/
def SearchGood {N : ℕ} (x : Fin N → Bool) : Option (Fin N) → Prop
  | some i => x i = true
  | none => ∀ i, x i = false

/-- **Search, correctness.** A search has a bad outcome with probability at most `δ`. -/
def GroverCorrect (M : Primitives) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Bool) (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
    (M.search N x δ).toOuterMeasure {o | ¬ SearchGood x o} ≤ ENNReal.ofReal δ

/-- **Search, cost.** A search makes at most `c √N log(1/δ)` predicate calls. -/
def GroverCost (M : Primitives) (c : ℝ) : Prop :=
  ∀ (N : ℕ) (δ : ℝ), 1 ≤ N → 0 < δ → δ ≤ 1 / 2 → 0 ≤ M.qS N δ ∧ M.qS N δ ≤ c * Real.sqrt N * Real.log (1 / δ)

/-- **Minimum finding, correctness.** It returns a non-minimal item with probability at most `δ`. -/
def MinCorrect (M : Primitives) : Prop :=
  ∀ (N : ℕ) (f : Fin (N + 1) → ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
    (M.minFind N f δ).toOuterMeasure {i | ¬ ∀ j, f i ≤ f j} ≤ ENNReal.ofReal δ

/-- **Minimum finding, cost.** It makes at most `c √N log(1/δ)` predicate calls. -/
def MinCost (M : Primitives) (c : ℝ) : Prop :=
  ∀ (N : ℕ) (δ : ℝ), 1 ≤ N → 0 < δ → δ ≤ 1 / 2 → 0 ≤ M.qM N δ ∧ M.qM N δ ≤ c * Real.sqrt N * Real.log (1 / δ)

open Classical in
/-- An exact classical search. -/
noncomputable def exactSearch {N : ℕ} (x : Fin N → Bool) : Option (Fin N) :=
  if h : ∃ i, x i = true then some h.choose else none

theorem exactSearch_good {N : ℕ} (x : Fin N → Bool) : SearchGood x (exactSearch x) := by
  classical
  unfold exactSearch
  split
  · next h => exact h.choose_spec
  · next h =>
    intro i
    by_contra hi
    exact h ⟨i, by simpa using hi⟩

theorem exists_min_index {N : ℕ} (f : Fin (N + 1) → ℕ) : ∃ i, ∀ j, f i ≤ f j := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ f ⟨0, Finset.mem_univ _⟩
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- **The hypotheses are satisfiable together.** So none of them can make a theorem vacuous through inconsistency of the
abstract interface. The witness runs exact classical search with the count written in; it is a model of the interface,
not a claim about machines. -/
theorem primitives_consistent :
    ∃ M : Primitives, GroverCorrect M ∧ GroverCost M 1 ∧ MinCorrect M ∧ MinCost M 1 := by
  classical
  refine ⟨⟨fun _ x _ => PMF.pure (exactSearch x), fun _ f _ => PMF.pure (exists_min_index f).choose,
    fun N δ => Real.sqrt N * Real.log (1 / δ), fun N δ => Real.sqrt N * Real.log (1 / δ)⟩, ?_, ?_, ?_, ?_⟩
  · intro N x δ _ _
    rw [PMF.toOuterMeasure_pure_apply]
    split
    · next h => exact absurd (exactSearch_good x) h
    · exact zero_le
  · intro N δ _ hδ hδ'
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    exact ⟨mul_nonneg (Real.sqrt_nonneg _) hlog, by simp⟩
  · intro N f δ _ _
    rw [PMF.toOuterMeasure_pure_apply]
    split
    · next h => exact absurd (exists_min_index f).choose_spec h
    · exact zero_le
  · intro N δ _ hδ hδ'
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    exact ⟨mul_nonneg (Real.sqrt_nonneg _) hlog, by simp⟩

end Strings
