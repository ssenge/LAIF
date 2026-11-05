import EqualSubsetSum.Grover
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# The quantum facts taken as hypotheses

The model is QRAQM, quantum memory written coherently and read in superposition. This file does not
define a circuit model. `Primitives` records, for instances of size `n`, the running time of each
primitive and its probability of success, as real functions. The named hypotheses below bound them.
They are not proved. They are `Prop`s passed as arguments, and `Axioms.lean` confirms that no axiom is
added. Everything downstream only uses these bounds, so the theorems of `EqualSubsetSum.Accounting`
are statements about how the costs compose, not about gates.

The hypotheses have a polynomial overhead `π n`, which collects the `poly(n)` factors of arithmetic,
of logarithms of sizes, of the `O(n)` repetitions of a check and of the unitary preparing the coins.
They are claimed only for sizes at most `Λ n`, in the application `Λ n = 2^{O(n)}`: above that the
logarithm of a size is not polynomial in `n`, and the accumulated error of the checks is not small.

`hypotheses_satisfiable` checks that the hypotheses about `Primitives` are jointly consistent, so the
composition is not vacuously true.
-/

open Finset

namespace EqualSubsetSum

/-- `π` is bounded by a polynomial in `n`. -/
def IsPoly (π : ℕ → ℝ) : Prop := ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n, π n ≤ C * ((n : ℝ) + 1) ^ k

/-- Running times and success probabilities of the primitives, for instances of size `n`. -/
structure Primitives where
  /-- The time to build the table of counts, for any modulus at most `P`. -/
  table : ℕ → ℝ → ℝ
  /-- The time to read the `I`-th element of a bin through the table. -/
  unrank : ℕ → ℝ
  /-- The time of the bounded-error check on two windows padded to exactly `T`, with queries of cost
  `q` and a hard time limit. -/
  claw : ℕ → ℝ → ℝ → ℝ
  /-- The time of `j` Grover iterations over the residues, with a check of cost `c`. -/
  grover : ℕ → ℝ → ℝ → ℝ
  /-- The probability that `j` iterations return a marked residue, for a marked fraction `φ`. -/
  groverSucc : ℕ → ℝ → ℕ → ℝ
  /-- The time of amplitude amplification of a procedure of cost `c` and success probability `q`. -/
  amplify : ℕ → ℝ → ℝ → ℝ
  /-- The success probability of the amplified procedure. -/
  amplifySucc : ℕ → ℝ → ℝ → ℝ
  table_nonneg : ∀ n P, 0 ≤ table n P
  unrank_nonneg : ∀ n, 0 ≤ unrank n
  claw_nonneg : ∀ n T q, 0 ≤ claw n T q
  grover_nonneg : ∀ n j c, 0 ≤ grover n j c
  amplify_nonneg : ∀ n q c, 0 ≤ amplify n q c
  groverSucc_nonneg : ∀ n φ j, 0 ≤ groverSucc n φ j

/-- **The table.** A dynamic program over the coordinates with state (position, counts of each symbol
per label, residue) has `P poly(n)` entries and is built in that time. arXiv:2111.07059, Theorem 3.5,
with a larger alphabet and counts. -/
def TableBuild (G : Primitives) (π Λ : ℕ → ℝ) : Prop :=
  ∀ n P, 1 ≤ P → P ≤ Λ n → G.table n P ≤ π n * P

/-- **Unranking.** With the table in memory, the `I`-th element of a bin takes `poly(n)` time. -/
def Unranking (G : Primitives) (π : ℕ → ℝ) : Prop :=
  ∀ n, G.unrank n ≤ π n

/-- **Claw finding on padded windows.** On two windows padded with tagged dummies to exactly `T`, a
check costs `T^{2/3} poly(n)` queries and steps, including the `O(n)` repetitions.
arXiv:2608.07309, Theorem 2.7. -/
def ClawWindows (G : Primitives) (π Λ : ℕ → ℝ) : Prop :=
  ∀ n T q, 1 ≤ T → T ≤ Λ n → 0 ≤ q → G.claw n T q ≤ π n * T ^ ((2 : ℝ) / 3) * (q + 1)

/-- **Grover over residues, time.** `j` iterations with a check of cost `c` take time
`(j + 1) (c + 1) poly(n)`, the factor `j + 1` counting the preparation of the superposition. -/
def GroverResidues (G : Primitives) (π Λ : ℕ → ℝ) : Prop :=
  ∀ n j c, 0 ≤ j → j ≤ Λ n → 0 ≤ c → G.grover n j c ≤ π n * (j + 1) * (c + 1)

/-- **Grover over residues, success.** For a marked fraction `φ`, after `j` iterations a marked
residue is returned with probability `sin² ((2 j + 1) θ)`, where `sin² θ = φ`, up to an error `ε n`
from the errors of the checks, which accumulate over at most `Λ n` iterations. -/
def GroverSuccess (G : Primitives) (ε Λ : ℕ → ℝ) : Prop :=
  ∀ n φ (j : ℕ), 0 ≤ φ → φ ≤ 1 → (j : ℝ) ≤ Λ n → groverProb φ j - ε n ≤ G.groverSucc n φ j

/-- **Amplitude amplification.** A unitary procedure with a verified flag, of cost `c` and success
probability at least `q`, is amplified to success probability at least `2/3` in time
`((c + 1) / √q) poly(n)`, the `1` covering the reflections. -/
def AmplitudeAmplification (G : Primitives) (π Λ : ℕ → ℝ) : Prop :=
  ∀ n q c, 0 < q → q ≤ 1 → 1 / q ≤ Λ n → 0 ≤ c →
    G.amplify n q c ≤ π n * ((c + 1) / √q) ∧ (2 : ℝ) / 3 ≤ G.amplifySucc n q c

/-- **The number of primes.** There are at least `P₀ / (C log₂ P₀)` primes in `[P₀, 2 P₀]`. -/
def PrimeCount (C : ℝ) : Prop :=
  ∀ P₀ : ℕ, 2 ≤ P₀ →
    (P₀ : ℝ) ≤ C * (Nat.log 2 P₀ : ℝ) * #((Icc P₀ (2 * P₀)).filter Nat.Prime)

/-- The hypotheses on `Primitives` are jointly satisfiable. -/
theorem hypotheses_satisfiable :
    ∀ Λ : ℕ → ℝ, ∃ (G : Primitives) (π : ℕ → ℝ) (ε : ℕ → ℝ),
      IsPoly π ∧ (∀ n, 1 ≤ π n) ∧ (∀ n, ε n = 0) ∧
      TableBuild G π Λ ∧ Unranking G π ∧ ClawWindows G π Λ ∧ GroverResidues G π Λ ∧
      GroverSuccess G ε Λ ∧ AmplitudeAmplification G π Λ := by
  intro Λ
  refine ⟨⟨fun _ _ => 0, fun _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ φ j => groverProb φ j,
    fun _ _ _ => 0, fun _ _ _ => 1, fun _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl,
    fun _ _ _ => le_rfl, fun _ _ _ => le_rfl, fun _ _ _ => sq_nonneg _⟩, fun _ => 1, fun _ => 0,
    ⟨1, 0, by norm_num, fun n => by simp⟩, fun _ => le_rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n P hP _
    simpa using (by linarith : (0 : ℝ) ≤ P)
  · intro n
    norm_num
  · intro n T q hT _ hq
    have : (0 : ℝ) ≤ T ^ ((2 : ℝ) / 3) := by positivity
    simp only [one_mul]
    positivity
  · intro n j c hj _ hc
    simp only [one_mul]
    positivity
  · intro n φ j _ _ _
    simp
  · intro n q c hq _ _ hc
    refine ⟨?_, by norm_num⟩
    simp only [one_mul]
    positivity

end EqualSubsetSum
