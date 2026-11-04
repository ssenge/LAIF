import GraphClasses.Nested

/-!
# The quantum query model and the quantum facts taken as hypotheses

An input is a bit string `x : Q → Bool`. A query is a phase `(-1)^{x q}` on basis states that name a position `q`, and
is trivial on the others. A `T`-query algorithm alternates `T + 1` unitaries with `T` queries, and measures.

Two facts are taken as named hypotheses and are not proved here: `BBHTSearch` and `ORLowerBound`.
-/

open Finset

namespace GraphClasses

/-- A `T`-query quantum algorithm on the basis `S` with outputs in `O`. -/
structure QAlg (Q : Type) (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (O : Type) where
  /-- The position queried on a basis state, if any. -/
  ix : S → Option Q
  U : Fin (T + 1) → Matrix.unitaryGroup S ℂ
  init : S
  out : S → O

variable {Q : Type} {S : Type} [Fintype S] [DecidableEq S] {O : Type} {T : ℕ}

/-- The phase of a query on a basis state. -/
def QAlg.phase (A : QAlg Q T S O) (x : Q → Bool) (b : S) : ℂ :=
  match A.ix b with
  | none => 1
  | some q => if x q then -1 else 1

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def QAlg.state (A : QAlg Q T S O) (x : Q → Bool) : (t : ℕ) → t ≤ T → S → ℂ
  | 0, _ => (A.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single A.init 1)
  | t + 1, h => (A.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ).mulVec
      fun b => A.phase x b * A.state x t (Nat.le_of_succ_le h) b

open Classical in
/-- The probability that the final measurement reports `o`. -/
noncomputable def QAlg.prob (A : QAlg Q T S O) (x : Q → Bool) (o : O) : ℝ :=
  ∑ b, if A.out b = o then Complex.normSq (A.state x T le_rfl b) else 0

/-- **BBHT** (Boyer, Brassard, Høyer, Tapp 1998), with a final check of the outcome and repetition. On `N ≥ 1`
candidates and for `δ ∈ (0, 1/2]` there is an algorithm with `O(√N log(1/δ))` queries that on every input:
never outputs an unmarked item; outputs "none" with certainty if no item is marked; if some item is marked, outputs
"none" with probability at most `δ`; and gives every marked item the same probability, so the outcome is uniform. -/
def BBHTSearch : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (δ : ℝ), 1 ≤ N → 0 < δ → δ ≤ 1 / 2 →
    ∃ (T : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (A : QAlg (Fin N) T S (Option (Fin N))),
      (T : ℝ) ≤ c * Real.sqrt N * Real.log (1 / δ) ∧
      ∀ x : Fin N → Bool,
        (∀ i, x i = false → A.prob x (some i) = 0) ∧
        ((∀ i, x i = false) → A.prob x none = 1) ∧
        ((∃ i, x i = true) → A.prob x none ≤ δ) ∧
        (∀ i j, x i = true → x j = true → A.prob x (some i) = A.prob x (some j))

/-- The bit string with a single `1`, at `i`. -/
def singleBit {N : ℕ} (i : Fin N) (j : Fin N) : Bool := decide (j = i)

/-- The OR lower bound with the constant `c`. -/
def ORBound (c : ℝ) : Prop :=
  ∀ (N T : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (A : QAlg (Fin N) T S Bool),
    2 / 3 ≤ A.prob (fun _ => false) false →
    (∀ i : Fin N, 2 / 3 ≤ A.prob (singleBit i) true) →
    c * Real.sqrt N ≤ T

/-- **The OR lower bound** (Bennett, Bernstein, Brassard, Vazirani 1997). An algorithm that tells the zero string from
every string with a single `1`, with error at most `1/3`, needs `Ω(√N)` queries. -/
def ORLowerBound : Prop := ∃ c : ℝ, 0 < c ∧ ORBound c

end GraphClasses
