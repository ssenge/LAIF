import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The quantum model and the cost of quantum search, taken as hypotheses

A fixed-length quantum query algorithm as in `../monge/lean/Monge/Model.lean`, and adaptive
compositions of them, where a classical tree chooses the next circuit from measured outcomes.
This is what "expected number of queries" means for repeated search, whose length depends on what it
finds.

Two facts about quantum search are named here and not proved: `GroverFindAll` and `GroverFindOne`.
They are `Prop`s passed as arguments, and `Axioms.lean` confirms that no axiom is added. Only the
bounds they give are used, so the proofs never unfold the quantum definitions. The definitions are
here so that the hypotheses are statements about the real objects.
-/

open Finset

namespace LPType

/-! ## Fixed-length algorithms -/

/-- Basis states: a query index, an answer register, and a workspace. -/
abbrev QBasis (J : Type) (k w : ℕ) := J × Fin k × Fin w

/-- A `T`-query algorithm with a workspace of size `w`. The unitaries do not depend on the input. -/
structure QAlg (J : Type) [Fintype J] [DecidableEq J] (k w T : ℕ) (E : Type) where
  /-- The unitaries between queries. -/
  U : Fin (T + 1) → Matrix.unitaryGroup (QBasis J k w) ℂ
  /-- The initial basis state. -/
  init : QBasis J k w
  /-- The classical outcome of a basis state in the final measurement. -/
  out : QBasis J k w → E

variable {J : Type} [Fintype J] [DecidableEq J] {k w T : ℕ} {E : Type}

/-- The query `|j, b, z⟩ ↦ |j, b + x_j, z⟩` as a permutation matrix, with addition in `Fin k`. -/
def queryMatrix (x : J → Fin k) : Matrix (QBasis J k w) (QBasis J k w) ℂ :=
  Matrix.of fun s' s => if s' = (s.1, s.2.1 + x s.1, s.2.2) then 1 else 0

/-- The amplitudes after `U_t O_x U_{t-1} ⋯ O_x U_0` on the initial basis state. -/
noncomputable def QAlg.state (A : QAlg J k w T E) (x : J → Fin k) :
    (t : ℕ) → t ≤ T → QBasis J k w → ℂ
  | 0, _ => (A.U ⟨0, Nat.succ_pos T⟩ : Matrix _ _ ℂ).mulVec (Pi.single A.init 1)
  | t + 1, h => (A.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix _ _ ℂ).mulVec
      ((queryMatrix x).mulVec (A.state x t (Nat.le_of_succ_le h)))

/-- The probability that the final measurement reports the outcome `e`. -/
noncomputable def QAlg.outProb [DecidableEq E] (A : QAlg J k w T E) (x : J → Fin k) (e : E) : ℝ :=
  ∑ s, if A.out s = e then Complex.normSq (A.state x T le_rfl s) else 0

/-! ## Adaptive compositions -/

/-- A classical decision tree over quantum subroutines: run a fixed-length circuit, measure one of
`m` outcomes, and continue according to the outcome. Classical randomness is a circuit too. -/
inductive AdaptiveAlg (J : Type) [Fintype J] [DecidableEq J] (k : ℕ) (E : Type) : Type
  /-- Stop and output `e`. -/
  | done (e : E) : AdaptiveAlg J k E
  /-- Run a `T`-query circuit, measure, continue. -/
  | step (m w T : ℕ) (A : QAlg J k w T (Fin m)) (next : Fin m → AdaptiveAlg J k E) :
      AdaptiveAlg J k E

/-- The expected number of queries on the input `x`. -/
noncomputable def AdaptiveAlg.expCost (x : J → Fin k) : AdaptiveAlg J k E → ℝ
  | .done _ => 0
  | .step _ _ T A next => T + ∑ o, A.outProb x o * (next o).expCost x

open scoped Classical in
/-- The probability on the input `x` that the output is not `good`. -/
noncomputable def AdaptiveAlg.failProb (x : J → Fin k) (good : E → Prop) : AdaptiveAlg J k E → ℝ
  | .done e => if good e then 0 else 1
  | .step _ _ _ A next => ∑ o, A.outProb x o * (next o).failProb x good

/-! ## The hypotheses -/

/-- The positions marked on the input `x`. Whether `j` is marked depends on `j` and on the value `x j`,
so one query decides it, as for the marks of Section 3 of the README, which are decided by the fixed
random function `u` and the weights. -/
def markedSet {n k : ℕ} (m : Fin n → Fin k → Bool) (x : Fin n → Fin k) : Finset (Fin n) :=
  univ.filter fun j => m j (x j)

/-- **Finding all marked elements**, by repeated quantum search that excludes what it has found (see
arXiv:2510.08348, Claim 6). If `k` are marked the expected cost is
at most `κ (√(n k) + √(n log n))`, with error at most `1/n³`, and with `κ` universal over `n`, the
alphabet, the marks and the input. Marks are computed and uncomputed with one query each, as the
inverse of the query is a query between two relabellings of the answer register. The condition
`2 ≤ n` is needed: for `n = 1` the right side is `0` when nothing is marked, and one query is needed. -/
def GroverFindAll (κ : ℝ) : Prop :=
  ∀ (n k : ℕ) (m : Fin n → Fin k → Bool), 2 ≤ n →
    ∃ A : AdaptiveAlg (Fin n) k (Finset (Fin n)), ∀ x : Fin n → Fin k,
      A.failProb x (· = markedSet m x) ≤ 1 / (n : ℝ) ^ 3 ∧
      A.expCost x ≤ κ * (√((n : ℝ) * #(markedSet m x)) + √((n : ℝ) * Real.log n))

/-- **Searching for one marked element or reporting none**, with error at most `1/n³`, in at most
`κ √(n log n)` queries (arXiv:cs/9904019, for the small error). -/
def GroverFindOne (κ : ℝ) : Prop :=
  ∀ (n k : ℕ) (m : Fin n → Fin k → Bool), 2 ≤ n →
    ∃ A : AdaptiveAlg (Fin n) k (Option (Fin n)), ∀ x : Fin n → Fin k,
      A.failProb x (fun e => match e with
        | some j => j ∈ markedSet m x
        | none => markedSet m x = ∅) ≤ 1 / (n : ℝ) ^ 3 ∧
      A.expCost x ≤ κ * √((n : ℝ) * Real.log n)

end LPType
