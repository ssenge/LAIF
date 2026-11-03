import Mathlib

/-!
# The models and the two classical theorems taken as hypotheses

Weighted graphs on `Fin n`, cut queries, classical randomized query algorithms, quantum query algorithms,
public-coin communication protocols, and the statements of the approximate degree of `AND` and of the
randomized communication complexity of disjointness.
-/

open Finset

namespace CutQuery

/-- Unordered pairs of vertices, written with the smaller vertex first. -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Integer edge weights. -/
abbrev Weights (n : ℕ) := Edge n → ℤ

variable {n : ℕ}

/-- `1` if the edge crosses the query set, else `0`. -/
def crosses (x : Fin n → Bool) (e : Edge n) : ℤ := if x e.1.1 ≠ x e.1.2 then 1 else 0

/-- The value of a cut query. -/
def cut (A : Weights n) (x : Fin n → Bool) : ℤ := ∑ e, A e * crosses x e

/-- The weighted degree of a vertex. -/
def degree (A : Weights n) (v : Fin n) : ℤ := ∑ e, if e.1.1 = v ∨ e.1.2 = v then A e else 0

/-- The minimum degree. -/
def minDegree [NeZero n] (A : Weights n) : ℤ :=
  univ.inf' ⟨0, mem_univ _⟩ (degree A)

/-- Graphs with weights in `[0, W]`. -/
def InClass (W : ℤ) (A : Weights n) : Prop := ∀ e, 0 ≤ A e ∧ A e ≤ W

/-- Unweighted graphs. -/
def IsSimple (A : Weights n) : Prop := ∀ e, A e = 0 ∨ A e = 1

/-- The weight bound of the classical theorem. -/
def classicalWeight (n C : ℕ) : ℤ := 2 ^ (C * n * (Nat.log 2 n + 1))

/-- The weight bound of the quantum theorem. -/
def quantumWeight (n C : ℕ) : ℕ := 2 ^ (C * n ^ 2 * (Nat.log 2 n + 1))

/-! ## Classical query algorithms -/

/-- A deterministic adaptive algorithm: the next query and the output are functions of the answers so far. -/
structure DetAlg (n : ℕ) where
  query : List ℤ → Fin n → Bool
  output : List ℤ → ℤ

/-- The answers after `t` queries. -/
def DetAlg.answers (alg : DetAlg n) (A : Weights n) : ℕ → List ℤ
  | 0 => []
  | t + 1 => alg.answers A t ++ [cut A (alg.query (alg.answers A t))]

/-- The output after `T` queries. -/
def DetAlg.run (alg : DetAlg n) (T : ℕ) (A : Weights n) : ℤ := alg.output (alg.answers A T)

/-- A randomized algorithm: a probability distribution on deterministic ones. -/
structure RandAlg (n : ℕ) (Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : ∑ ω, p ω = 1
  alg : Ω → DetAlg n

/-- The probability that the algorithm, with `T` queries, misses the minimum degree. -/
noncomputable def RandAlg.err [NeZero n] {Ω : Type*} [Fintype Ω] (r : RandAlg n Ω) (T : ℕ) (A : Weights n) : ℝ :=
  ∑ ω, if (r.alg ω).run T A = minDegree A then 0 else r.p ω

/-! ## Quantum query algorithms -/

/-- A `T`-query quantum algorithm on the basis `S`. Each basis state names a query set `x` and a multiplier
`z`, so any workspace is allowed. The unitaries do not depend on the input. -/
structure QAlg (n T : ℕ) (S : Type*) [Fintype S] [DecidableEq S] where
  x : S → Fin n → Bool
  z : S → ℤ
  U : Fin (T + 1) → Matrix.unitaryGroup S ℂ
  init : S
  out : S → ℤ

/-- The phase query `|x, z⟩ ↦ exp(2 π i z cut_A(x) / N) |x, z⟩`, as a diagonal. -/
noncomputable def QAlg.phase {T : ℕ} {S : Type*} [Fintype S] [DecidableEq S] (q : QAlg n T S) (N : ℕ)
    (A : Weights n) (s : S) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (q.z s * cut A (q.x s) : ℤ) / N)

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def QAlg.state {T : ℕ} {S : Type*} [Fintype S] [DecidableEq S] (q : QAlg n T S) (N : ℕ)
    (A : Weights n) : (t : ℕ) → t ≤ T → S → ℂ
  | 0, _ => (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1)
  | t + 1, h => (q.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ).mulVec
      fun s => q.phase N A s * q.state N A t (Nat.le_of_succ_le h) s

/-- The probability that the final measurement reports a value other than `d`. -/
noncomputable def QAlg.errAt {T : ℕ} {S : Type*} [Fintype S] [DecidableEq S] (q : QAlg n T S) (N : ℕ)
    (A : Weights n) (d : ℤ) : ℝ :=
  ∑ s, if q.out s = d then 0 else Complex.normSq (q.state N A T le_rfl s)

/-! ## Classical theorems taken as hypotheses -/

/-- The value of the `AND` function at a point of the cube. -/
def andBool {k : ℕ} (x : Fin k → Bool) : ℝ := if ∀ i, x i = true then 1 else 0

/-- The approximate degree of `AND_k` is `Ω(√k)`. -/
def AndApproxDegree : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (p : MvPolynomial (Fin k) ℝ),
    (∀ x : Fin k → Bool,
      |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p - andBool x| ≤ 1 / 3) →
    c * Real.sqrt k ≤ p.totalDegree

/-- A deterministic two-party protocol with `t` rounds: in each round both players know the transcript so far,
which is a list of bits, and the speaker sends one bit that depends on the transcript and on the speaker's input. -/
structure Protocol (X Y : Type*) where
  aliceSpeaks : List Bool → Bool
  alice : List Bool → X → Bool
  bob : List Bool → Y → Bool
  output : List Bool → Bool

/-- The transcript after `t` bits. -/
def Protocol.transcript {X Y : Type*} (π : Protocol X Y) (a : X) (b : Y) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
    let h := π.transcript a b t
    h ++ [if π.aliceSpeaks h then π.alice h a else π.bob h b]

/-- Disjointness of `k`-bit strings: true if no index has both bits set. -/
def disjoint {k : ℕ} (a b : Fin k → Bool) : Bool := decide (∀ i, ¬ (a i = true ∧ b i = true))

/-- Randomized public-coin communication of disjointness is `Ω(k)`: a distribution over `t`-bit deterministic
protocols with error at most `1/3` on every input needs `t ≥ c k`. -/
def DisjLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (k t : ℕ) (Ω : Type) [Fintype Ω] (p : Ω → ℝ) (π : Ω → Protocol (Fin k → Bool) (Fin k → Bool)),
    (∀ ω, 0 ≤ p ω) → ∑ ω, p ω = 1 →
    (∀ a b : Fin k → Bool,
      ∑ ω, (if (π ω).output ((π ω).transcript a b t) = disjoint a b then 0 else p ω) ≤ 1 / 3) →
    c * k ≤ t

end CutQuery
