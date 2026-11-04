import Mathlib

/-!
# The model

Digraphs are relations `E : V → V → Prop`. Paths are walks, and `dominates_iff_paths` and `onAllPaths_iff_paths` in
`Lemma2.lean` show that replacing walks by simple paths changes none of the definitions below.

Quantum and classical query algorithms are concrete: a `QAlg` is a sequence of unitaries with phase queries,
and a `RandAlg` is a distribution on adaptive decision trees. What is taken from the literature is stated at
the end of this file as named `Prop`s, and is never asserted. A theorem that uses one has it as a hypothesis.

* `DHHM_Thm23`: quantum Connectivity needs `Ω(n^{3/2})` matrix queries.
* `ClassicalConnectivity`: randomized Connectivity needs `Ω(n²)` matrix queries.
* `BBHT`: quantum search, expected `O(√(N/t))` queries.
* `DurrHoyer`: quantum minimum finding, `O(√N log(1/δ))` queries.
-/

open Finset

namespace Dominators

universe u

/-! ## Walks and reachability -/

/-- A walk from `x` to `y` along edges of `E`. -/
inductive Walk {V : Type u} (E : V → V → Prop) : V → V → Type u
  | nil (v : V) : Walk E v v
  | cons {x y z : V} (h : E x y) (p : Walk E y z) : Walk E x z

namespace Walk

variable {V : Type u} {E : V → V → Prop}

/-- The vertices of a walk, in order. -/
def support : {x y : V} → Walk E x y → List V
  | _, _, .nil v => [v]
  | x, _, .cons _ p => x :: p.support

/-- The edges of a walk, in order. -/
def edges : {x y : V} → Walk E x y → List (V × V)
  | _, _, .nil _ => []
  | x, _, .cons (y := y) _ p => (x, y) :: p.edges

/-- Concatenation. -/
def append : {x y z : V} → Walk E x y → Walk E y z → Walk E x z
  | _, _, _, .nil _, q => q
  | _, _, _, .cons h p, q => .cons h (p.append q)

end Walk

variable {V : Type u}

/-- `y` is reachable from `x`. -/
def Reach (E : V → V → Prop) (x y : V) : Prop := Nonempty (Walk E x y)

/-- `d` dominates `w` from the root `r`: every path from `r` to `w` contains `d`. -/
def Dominates (E : V → V → Prop) (r d w : V) : Prop :=
  ∀ p : Walk E r w, d ∈ p.support

/-- `u` is the immediate dominator of the reachable vertex `w`: a strict dominator of `w` that every strict
dominator of `w` dominates. -/
def IsIdom (E : V → V → Prop) (r u w : V) : Prop :=
  Reach E r w ∧ u ≠ w ∧ Dominates E r u w ∧ ∀ d, d ≠ w → Dominates E r d w → Dominates E r d u

/-- The edge `(u, v)` is on every path from `r` to `v`. -/
def OnAllPaths (E : V → V → Prop) (r u v : V) : Prop :=
  ∀ p : Walk E r v, (u, v) ∈ p.edges

/-- A bridge of the flow graph `(E, r)`: an edge, with reachable head, on every path from `r` to its head. -/
def IsBridge (E : V → V → Prop) (r u v : V) : Prop :=
  E u v ∧ Reach E r v ∧ OnAllPaths E r u v

/-- The reverse graph. -/
abbrev rev (E : V → V → Prop) : V → V → Prop := fun x y => E y x

/-- `E` without the edge `(u, v)`. -/
def delEdge (E : V → V → Prop) (u v : V) : V → V → Prop :=
  fun x y => E x y ∧ ¬(x = u ∧ y = v)

/-- `E` without the vertex `d`, on the remaining vertices. -/
abbrev delVertex (E : V → V → Prop) (d : V) : {x : V // x ≠ d} → {x : V // x ≠ d} → Prop :=
  fun x y => E x.1 y.1

/-- Every vertex reaches every vertex. -/
def StrongConn (E : V → V → Prop) : Prop := ∀ x y, Reach E x y

/-- `x` and `y` are in the same strongly connected component. -/
def Mutual (E : V → V → Prop) (x y : V) : Prop := Reach E x y ∧ Reach E y x

theorem Reach.refl (E : V → V → Prop) (x : V) : Reach E x x := ⟨.nil x⟩

theorem Reach.trans {E : V → V → Prop} {x y z : V} (h : Reach E x y) (h' : Reach E y z) : Reach E x z := by
  obtain ⟨p⟩ := h
  obtain ⟨q⟩ := h'
  exact ⟨p.append q⟩

/-- Being in the same strongly connected component, as a setoid. -/
def sccSetoid (E : V → V → Prop) : Setoid V where
  r := Mutual E
  iseqv :=
    { refl := fun x => ⟨Reach.refl E x, Reach.refl E x⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h h' => ⟨h.1.trans h'.1, h'.2.trans h.2⟩ }

/-- The number of strongly connected components. -/
noncomputable def sccCount (E : V → V → Prop) : ℕ := Nat.card (Quotient (sccSetoid E))

/-- A strong bridge: an edge whose removal increases the number of strongly connected components. -/
def IsStrongBridge (E : V → V → Prop) (u v : V) : Prop :=
  E u v ∧ sccCount E < sccCount (delEdge E u v)

/-- A strong articulation point: a vertex whose removal increases the number of strongly connected
components. -/
def IsSAP (E : V → V → Prop) (d : V) : Prop :=
  sccCount E < sccCount (delVertex E d)

/-! ## Quantum query algorithms -/

/-- What a basis state queries: one test of one input entry, or a constant. The constant case makes a gate
that needs no query, which is what a reduction needs for the fixed part of a gadget. -/
abbrev QueryTarget (ι α : Type*) := (ι × (α → Bool)) ⊕ Bool

/-- The value of a query target on the input `x`. -/
def QueryTarget.val {ι α : Type*} (x : ι → α) : QueryTarget ι α → Bool
  | .inl (i, g) => g (x i)
  | .inr b => b

/-- A `T`-query quantum algorithm on the basis `S`, reading an input `x : ι → α`. The matrix model has
`α = Bool`; the array model has `α` the list entries. The unitaries do not depend on the input. -/
structure QAlg (ι α S β : Type*) [Fintype S] [DecidableEq S] (T : ℕ) where
  /-- The initial basis state. -/
  init : S
  /-- The unitaries between queries. -/
  U : ℕ → Matrix S S ℂ
  unitary : ∀ t, U t ∈ Matrix.unitaryGroup S ℂ
  /-- What each basis state queries. -/
  query : S → QueryTarget ι α
  /-- The output read from a basis state at the end. -/
  out : S → β

namespace QAlg

variable {ι α S β : Type*} [Fintype S] [DecidableEq S] {T : ℕ}

/-- The phase of the query on basis state `s`. -/
noncomputable def phase (A : QAlg ι α S β T) (x : ι → α) (s : S) : ℂ :=
  if QueryTarget.val x (A.query s) = true then -1 else 1

/-- The amplitudes after `t` queries. -/
noncomputable def amp (A : QAlg ι α S β T) (x : ι → α) : ℕ → S → ℂ
  | 0 => (A.U 0).mulVec (Pi.single A.init 1)
  | t + 1 => (A.U (t + 1)).mulVec (fun s => A.phase x s * amp A x t s)

open Classical in
/-- The probability that the output satisfies `P`. -/
noncomputable def prob (A : QAlg ι α S β T) (x : ι → α) (P : β → Prop) : ℝ :=
  ∑ s, if P (A.out s) then ‖A.amp x T s‖ ^ 2 else 0

/-- The algorithm's output satisfies the relation `R x`, with probability at least `2/3`, on every input. -/
def Solves (A : QAlg ι α S β T) (R : (ι → α) → β → Prop) : Prop :=
  ∀ x, 2 / 3 ≤ A.prob x (R x)

end QAlg

/-! ## Classical randomized query algorithms -/

/-- An adaptive decision tree on bits `x : ι → Bool`, with constants allowed as in `QueryTarget`. -/
structure DetAlg (ι β : Type*) where
  query : List Bool → ι ⊕ Bool
  output : List Bool → β

/-- The value of a classical query. -/
def bitVal {ι : Type*} (x : ι → Bool) : ι ⊕ Bool → Bool
  | .inl i => x i
  | .inr b => b

/-- The answers after `t` queries, most recent last. -/
def DetAlg.answers {ι β : Type*} (A : DetAlg ι β) (x : ι → Bool) : ℕ → List Bool
  | 0 => []
  | t + 1 => A.answers x t ++ [bitVal x (A.query (A.answers x t))]

/-- A randomized algorithm: a probability distribution on decision trees. -/
structure RandAlg (ι β Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : ∑ ω, p ω = 1
  alg : Ω → DetAlg ι β

open Classical in
/-- The probability that, with `T` queries, the output satisfies `P`. -/
noncomputable def RandAlg.prob {ι β Ω : Type*} [Fintype Ω] (A : RandAlg ι β Ω) (T : ℕ) (x : ι → Bool)
    (P : β → Prop) : ℝ :=
  ∑ ω, if P ((A.alg ω).output ((A.alg ω).answers x T)) then A.p ω else 0

/-- The output satisfies `R x`, with probability at least `2/3`, on every input. -/
def RandAlg.Solves {ι β Ω : Type*} [Fintype Ω] (A : RandAlg ι β Ω) (T : ℕ)
    (R : (ι → Bool) → β → Prop) : Prop :=
  ∀ x, 2 / 3 ≤ A.prob T x (R x)

/-! ## Connectivity -/

/-- Unordered pairs of `Fin n`, the input bits of an undirected graph. -/
abbrev UEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The undirected graph of a bit string, as a symmetric relation. So a digraph query on the bidirected graph
is one query on the bit string. -/
def ugraph {n : ℕ} (x : UEdge n → Bool) (a b : Fin n) : Prop :=
  (∃ h : a < b, x ⟨(a, b), h⟩ = true) ∨ (∃ h : b < a, x ⟨(b, a), h⟩ = true)

/-- The output `b` answers Connectivity correctly on `x`. -/
def ConnAnswer {n : ℕ} (x : UEdge n → Bool) (b : Bool) : Prop :=
  b = true ↔ StrongConn (ugraph x)

/-! ## The named hypotheses -/

/-- **DHHM Theorem 23** (Dürr, Heiligman, Høyer, Mhalla, quant-ph/0401091): deciding Connectivity of an
`n`-vertex graph in the matrix model needs `Ω(n^{3/2})` quantum queries. Taken as a hypothesis. -/
def DHHM_Thm23 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (S : Type) [Fintype S] [DecidableEq S] (T : ℕ)
    (A : QAlg (UEdge n) Bool S Bool T), A.Solves ConnAnswer → c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ T

/-- Deciding Connectivity needs `Ω(n²)` randomized queries in the matrix model. Taken as a hypothesis. -/
def ClassicalConnectivity : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (Ω : Type) [Fintype Ω] (T : ℕ)
    (A : RandAlg (UEdge n) Bool Ω), A.Solves T ConnAnswer → c * (n : ℝ) ^ 2 ≤ T

open Classical in
/-- The number of marked entries. -/
noncomputable def markedCount {N : ℕ} {α : Type*} (marked : Fin N → α → Bool) (x : Fin N → α) : ℕ :=
  (univ.filter fun i => marked i (x i) = true).card

/-- **BBHT** (Boyer, Brassard, Høyer, Tapp) in the form "expected `O(√(N/t))` queries", for an unknown number
`t ≥ 1` of marked entries. A run stopped at budget `k` is the algorithm `A k`. So `1 - P_k`, with `P_k` the
probability of having found a marked entry within `k` queries, is the probability of stopping after `k`, and
its sum over `k` is the expected number of queries. An answer is verified by a query, so it is never wrong,
and with nothing marked the answer is always `none`. Being marked may depend on the index and the entry: in the
matrix model the entry is a bit and the index a vertex. Taken as a hypothesis. -/
def BBHT : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (α : Type) (marked : Fin N → α → Bool), ∃ d : ℕ → ℕ,
    ∃ A : ∀ k, QAlg (Fin N) α (Fin (d k)) (Option (Fin N)) k,
    ∀ x : Fin N → α,
      (∀ k, (A k).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = false) = 0) ∧
      (∀ k, (A k).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = true) ≤
        (A (k + 1)).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = true)) ∧
      (1 ≤ markedCount marked x →
        Summable (fun k => 1 - (A k).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = true)) ∧
        ∑' k, (1 - (A k).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = true)) ≤
          C * Real.sqrt ((N : ℝ) / markedCount marked x))

/-- **Dürr-Høyer** minimum finding: `O(√N log(1/δ))` queries find an entry of least key with error `δ`.
The key is classical data, as the `f_w` of `README.md` are, and may depend on the index and the entry.
Taken as a hypothesis. -/
def DurrHoyer : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 1 ≤ N) (α : Type) (key : Fin N → α → WithTop ℕ) (δ : ℝ) (_ : 0 < δ) (_ : δ ≤ 1 / 2),
    ∃ (d T : ℕ) (A : QAlg (Fin N) α (Fin d) (Option (Fin N)) T),
      (T : ℝ) ≤ C * Real.sqrt N * (1 + Real.log (1 / δ)) ∧
      ∀ x : Fin N → α, 1 - δ ≤ A.prob x (fun o => ∃ i, o = some i ∧ ∀ j, key i (x i) ≤ key j (x j))

end Dominators
