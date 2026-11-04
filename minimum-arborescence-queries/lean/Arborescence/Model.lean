import Mathlib

/-!
# The model

Rooted weighted digraphs, spanning arborescences as parent functions, their cost, minimum
arborescences, and the TopK specification (DHHM Problem 3, section 1 of `README.md`).

The quantum subroutine is not modelled as quantum mechanics. TopK is a predicate `IsTopK` on outputs, and a call with
budget `K` on `N` items is charged `topKCost K N = √(K N)`. Correctness and accounting assume no DHHM theorem: they say
what happens if every list is `IsTopK`-correct, and what the sum of the charges is. The one DHHM statement used is
`DHHMTheorem6`, a named hypothesis of `solve_queries`, which turns charges into queries.
-/

open Finset

namespace Arborescence

/-- A digraph on `V` with integer weights and a root. `adj u v` says that `(u, v)` is an edge. The
weight of a non-edge is irrelevant. -/
structure Graph (V : Type*) where
  adj : V → V → Bool
  w : V → V → ℤ
  root : V

variable {V : Type*}

/-- `p` is a spanning arborescence: `p` fixes the root, each other `(p v, v)` is an edge, and every vertex
reaches the root by following `p`. The value `p root = root` only normalizes the total function. -/
structure IsArb (g : Graph V) (p : V → V) : Prop where
  root_fix : p g.root = g.root
  edge : ∀ v, v ≠ g.root → g.adj (p v) v = true
  reach : ∀ v, ∃ k : ℕ, p^[k] v = g.root

/-- The cost of a parent function: the sum of `w (p v, v)` over `v ≠ root`. -/
def cost [Fintype V] [DecidableEq V] (g : Graph V) (p : V → V) : ℤ :=
  ∑ v ∈ univ.erase g.root, g.w (p v) v

/-- `p` is an arborescence of minimum cost. -/
def IsMinArb [Fintype V] [DecidableEq V] (g : Graph V) (p : V → V) : Prop :=
  IsArb g p ∧ ∀ q, IsArb g q → cost g p ≤ cost g q

/-- `e` enters `X`: its head lies in `X` and its source does not. -/
def Enters [DecidableEq V] (X : Finset V) (u v : V) : Prop := v ∈ X ∧ u ∉ X

/-! ## TopK -/

/-- DHHM Problem 3, the specification of TopK. Given `f : items → ℤ ∪ {∞}`, a type function `ty`, and `d'`:
with `e` the number of types and `d = min d' e`, the output `I ⊆ items` has `|I| = d`, has distinct types,
and for all `j ∉ I`, `i ∈ I`: if `f j < f i`, then `f i' ≤ f j` for some `i' ∈ I` of the type of `j`. -/
structure IsTopK {ι T : Type*} [DecidableEq T] (items : Finset ι) (f : ι → WithTop ℤ) (ty : ι → T)
    (d' : ℕ) (I : Finset ι) : Prop where
  subset : I ⊆ items
  card_eq : I.card = min d' (items.image ty).card
  inj : Set.InjOn ty (I : Set ι)
  spec : ∀ j ∈ items, j ∉ I → ∀ i ∈ I, f j < f i → ∃ i' ∈ I, ty i' = ty j ∧ f i' ≤ f j

/-- The charge for a TopK call with budget `K` on `N` items. -/
noncomputable def topKCost (K N : ℕ) : ℝ := Real.sqrt (K * N)

/-! ## The list data of `Build`, section 3 of the notes -/

/-- The `N(G)` edges entering the vertices of `G`, the items of a call `Build(G, K)`. -/
def inEdges [Fintype V] [DecidableEq V] (g : Graph V) (G : Finset V) : Finset (V × V) :=
  univ.filter fun e => g.adj e.1 e.2 = true ∧ e.2 ∈ G

/-- The function handed to TopK by `Build`: `f (u, v) = w (u, v) - y v` if `(u, v)` is an edge and
`u ∉ C`, and `∞` otherwise. -/
def buildF [DecidableEq V] (g : Graph V) (C : Finset V) (y : V → ℤ) (e : V × V) : WithTop ℤ :=
  if g.adj e.1 e.2 = true ∧ e.1 ∉ C then ((g.w e.1 e.2 - y e.2 : ℤ) : WithTop ℤ) else ⊤

/-- The in-degree of `v`. -/
def indeg [Fintype V] (g : Graph V) (v : V) : ℕ := (univ.filter fun u => g.adj u v = true).card

/-- The number of edges of `g`. -/
def numEdges [Fintype V] (g : Graph V) : ℕ := ∑ v, indeg g v

/-- DHHM Theorem 6 as a statement about an abstract count `q K N` of the queries of a call: at most a constant times
`√(K N)`. The theorem has `√(d N)` with `d = min K e ≤ K`, and the read-all branch of the notes costs `N ≤ √(2 K N)`.
This is the hypothesis of `solve_queries`. The error probability of a call is not modelled. -/
def DHHMTheorem6 (q : ℕ → ℕ → ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ K N, q K N ≤ C * topKCost K N

end Arborescence
