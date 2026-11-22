/-!
# A symmetric paving matroid congestion game with price of anarchy at least 16/11

Ground set `{0, 1, 2, 3, 4}` with parallel classes `{0, 1}`, `{2, 3}`, `{4}`. The bases are the pairs of elements
from different classes, so the matroid has rank 2. Three players, each picks a basis. Element `e` has the affine
delay `d e x = a e * x + b e` with `a = (2, 2, 1, 0, 2)` and `b = (0, 0, 0, 2, 0)`. The social cost of a profile is
`∑ e, x e * d e (x e)`, where `x e` is the number of players using `e`.

* `bases_sub`, `bases_norm`, `exchange`: the bases satisfy the basis exchange axiom, so they are the bases of a matroid.
* `rank_two`: every basis has 2 elements, so the matroid has rank 2.
* `paving`: every element lies in a basis, so every set of at most one element is independent (no loops). A circuit
  is a dependent set, hence every circuit has at least 2 elements, the rank. For rank 2 this is exactly the
  definition of paving (every circuit has size rank or rank + 1; circuits have at most rank + 1 elements anyway).
* `ne_isNE`: the profile `{0, 2}, {0, 2}, {1, 4}` is a pure Nash equilibrium: no player has a cheaper basis.
* `ne_cost`, `opt_cost`, `opt_ge`: the equilibrium costs 16, and 11 is the minimum cost over all profiles.
* `ratio_gt`: `16 / 11 > 13 / 9`.
-/

namespace PavingCert

def n : Nat := 5

def cls : List Nat := [0, 0, 1, 1, 2]

/-- The bases: pairs `[i, j]` with `i < j` in different parallel classes. -/
def bases : List (List Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter fun j => i < j ∧ cls.getD i 0 ≠ cls.getD j 0).map fun j => [i, j]

def a : List Nat := [2, 2, 1, 0, 2]
def b : List Nat := [0, 0, 0, 2, 0]

def d (e x : Nat) : Nat := a.getD e 0 * x + b.getD e 0

/-- Number of players using element `e` in a profile (a list of bases). -/
def load (P : List (List Nat)) (e : Nat) : Nat := (P.filter fun B => e ∈ B).length

def cost (P : List (List Nat)) : Nat := ((List.range n).map fun e => load P e * d e (load P e)).sum

/-- Cost of a player on basis `p` in profile `P`. -/
def own (P : List (List Nat)) (p : List Nat) : Nat := (p.map fun e => d e (load P e)).sum

/-- Cost of that player after switching to `q`. -/
def dev (P : List (List Nat)) (p q : List Nat) : Nat :=
  (q.map fun e => d e (if e ∈ p then load P e else load P e + 1)).sum

def isNE (P : List (List Nat)) : Bool := P.all fun p => bases.all fun q => own P p ≤ dev P p q

def ne : List (List Nat) := [[0, 2], [0, 2], [1, 4]]
def opt : List (List Nat) := [[0, 2], [1, 3], [3, 4]]

/-- All ordered profiles of three bases. -/
def profiles : List (List (List Nat)) :=
  bases.flatMap fun B₁ => bases.flatMap fun B₂ => bases.map fun B₃ => [B₁, B₂, B₃]

theorem bases_eq : bases = [[0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 4], [3, 4]] := by decide

/-- Every basis is a subset of the ground set `{0, ..., n - 1}`. -/
theorem bases_sub : ∀ B ∈ bases, ∀ z ∈ B, z < n := by decide

/-- The subset of the ground set with the same elements as `l`, listed in increasing order. -/
def norm (l : List Nat) : List Nat := (List.range n).filter fun z => z ∈ l

/-- Every basis is listed in normal form, so two bases with the same elements are equal as lists. -/
theorem bases_norm : ∀ B ∈ bases, norm B = B := by decide

/-- Basis exchange: for bases `A`, `B` and `x ∈ A \ B` there is `y ∈ B \ A` with `(A \ {x}) ∪ {y}` a basis. -/
theorem exchange : ∀ A ∈ bases, ∀ B ∈ bases, ∀ x ∈ A, x ∉ B →
    ∃ y ∈ B, y ∉ A ∧ norm (y :: A.erase x) ∈ bases := by
  rw [bases_eq]; decide

theorem rank_two : ∀ B ∈ bases, B.length = 2 := by decide

/-- No loops: every set of at most one element lies in a basis, so every circuit has at least 2 = rank elements. -/
theorem paving : ∀ e < n, ∃ B ∈ bases, e ∈ B := by decide

theorem ne_mem : ∀ p ∈ ne, p ∈ bases := by decide
theorem opt_mem : ∀ p ∈ opt, p ∈ bases := by decide

theorem ne_isNE : isNE ne = true := by decide
theorem ne_cost : cost ne = 16 := by decide
theorem opt_cost : cost opt = 11 := by decide
theorem opt_ge : ∀ P ∈ profiles, 11 ≤ cost P := by decide +kernel

theorem ratio_gt : 13 * 11 < 9 * 16 := by decide

end PavingCert
