import GHMatrix.Cut

/-! Content of `GHMatrix.lemma4`: the hard family with `h = 4`, `s = 3` and `B = ∅` on 14 vertices
satisfies all hypotheses, the bound `2h + s − 1 = 10` is attained by a cut with two vertices of `L₁`
on one side, and it fails for a cut with a single vertex on one side. -/

namespace GHMatrix

/-- `L = {0, ..., 6}` with `L₂ = {3, ..., 6}`, `R = {7, ..., 13}` with `R₂ = {10, ..., 13}`. -/
def L₀ : Finset (Fin 14) := Finset.univ.filter (fun x => x.val < 7)
def R₀ : Finset (Fin 14) := Finset.univ.filter (fun x => 7 ≤ x.val)
def L₂₀ : Finset (Fin 14) := Finset.univ.filter (fun x => 3 ≤ x.val ∧ x.val < 7)
def R₂₀ : Finset (Fin 14) := Finset.univ.filter (fun x => 10 ≤ x.val)

/-- Cliques on `L` and `R` and the complete join of `L₂` and `R₂`. -/
def adj₀ (x y : Fin 14) : Prop :=
  x ≠ y ∧ ((x.val < 7 ↔ y.val < 7) ∨ (x ∈ L₂₀ ∧ y ∈ R₂₀) ∨ (x ∈ R₂₀ ∧ y ∈ L₂₀))

instance : DecidableRel adj₀ := fun x y => by unfold adj₀; infer_instance

example : L₂₀ ⊆ L₀ ∧ R₂₀ ⊆ R₀ ∧ L₀.card = 4 + 3 ∧ R₀.card = 4 + 3 ∧ L₂₀.card = 4 ∧
    R₂₀.card = 4 ∧ Disjoint L₀ R₀ ∧ L₀ ∪ R₀ = Finset.univ := by decide

example : (∀ x ∈ L₀, ∀ y ∈ L₀, x ≠ y → adj₀ x y) ∧ (∀ x ∈ R₀, ∀ y ∈ R₀, x ≠ y → adj₀ x y) ∧
    (∀ x ∈ L₂₀, ∀ y ∈ R₂₀, adj₀ x y ∧ adj₀ y x) := by decide

/-- The bound of `lemma4` is attained: `S = {0, 1}` has exactly `10` crossing edges. -/
example : (crossing adj₀ {0, 1}).card = 2 * 4 + 3 - 1 := by decide

/-- Without two vertices on each side the bound fails: `S = {0}` has `6 < 10` crossing edges. -/
example : (crossing adj₀ {0}).card = 6 := by decide

end GHMatrix
