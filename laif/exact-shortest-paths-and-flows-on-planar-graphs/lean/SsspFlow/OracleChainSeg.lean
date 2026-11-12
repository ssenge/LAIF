import SsspFlow.OracleChainSum

/-!
# Segments of the parent chains of an oracle

Along valid parent steps from a node `v`, the nodes `j + d` and `j` steps above `v` are joined by a
walk down the chain whose edges are exactly the parent steps between them, and whose length is the
sum of the lengths of these steps.

* `Walk.AllEdges`, `Walk.HasEdge`: every edge of a walk satisfies a relation; a walk takes an edge.
* `Walk.edgeFlat`: lists read off the edges of a walk, in order, joined.
* `Net.ExactSpec.chain_seg`: the walk down the chain between two nodes of it.
-/

set_option autoImplicit false

namespace SsspFlow

open scoped ENNReal

namespace Walk

variable {V : Type*} {adj : V → V → Prop}

/-- Every edge of a walk satisfies `P`. -/
def AllEdges (P : V → V → Prop) : ∀ {a b : V}, Walk adj a b → Prop
  | _, _, .nil _ => True
  | a, _, .cons (b := b) _ p => P a b ∧ AllEdges P p

/-- The walk takes the edge from `y` to `y'`. -/
def HasEdge (y y' : V) : ∀ {a b : V}, Walk adj a b → Prop
  | _, _, .nil _ => False
  | a, _, .cons (b := b) _ p => (a = y ∧ b = y') ∨ HasEdge y y' p

/-- The lists `f a b` over the edges `a → b` of a walk, in order, joined. -/
def edgeFlat {α : Type*} (f : V → V → List α) : ∀ {a b : V}, Walk adj a b → List α
  | _, _, .nil _ => []
  | a, _, .cons (b := b) _ p => f a b ++ edgeFlat f p

theorem AllEdges.append {P : V → V → Prop} {a b c : V} (p : Walk adj a b) (q : Walk adj b c)
    (hp : p.AllEdges P) (hq : q.AllEdges P) : (p.append q).AllEdges P := by
  induction p with
  | nil => exact hq
  | cons e p ih => exact ⟨hp.1, ih q hp.2 hq⟩

theorem AllEdges.mono {P Q : V → V → Prop} (hPQ : ∀ a b, P a b → Q a b) {a b : V} (p : Walk adj a b)
    (hp : p.AllEdges P) : p.AllEdges Q := by
  induction p with
  | nil => trivial
  | cons e p ih => exact ⟨hPQ _ _ hp.1, ih hp.2⟩

end Walk

namespace Congest

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Segments of a parent chain.** Along `K` valid parent steps from `v`, the nodes `j + d` and `j`
steps above `v`, for `j + d ≤ K`, are joined by a walk whose edges are exactly the parent steps
between them and whose length is the sum of their lengths. Lists read off its edges are those of the
parent steps, from the top down. -/
theorem Net.ExactSpec.chain_seg {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (v : V) {K : ℕ} (hs : Net.ParSteps r v K) :
    ∀ d j, j + d ≤ K → ∃ q : SsspFlow.Walk N.G.Adj ((Net.parOf r)^[j + d] v) ((Net.parOf r)^[j] v),
      q.AllEdges (fun y y' => ∃ l, j ≤ l ∧ l < j + d ∧ y = (Net.parOf r)^[l + 1] v ∧
        y' = (Net.parOf r)^[l] v) ∧
      (∀ l, j ≤ l → l < j + d → q.HasEdge ((Net.parOf r)^[l + 1] v) ((Net.parOf r)^[l] v)) ∧
      q.wt (lenTop ℓ) =
        ((∑ l ∈ Finset.Ico j (j + d), ℓ ((Net.parOf r)^[l + 1] v) ((Net.parOf r)^[l] v) : ℕ∞) : ℝ≥0∞) ∧
      ∀ {α : Type} (f : V → V → List α), q.edgeFlat f =
        ((List.range d).reverse.map fun l => f ((Net.parOf r)^[j + l + 1] v) ((Net.parOf r)^[j + l] v)).flatten
  | 0, j, _ => ⟨.nil _, trivial, fun l h1 h2 => absurd h2 (by omega), by simp [SsspFlow.Walk.wt],
      fun f => by simp [Walk.edgeFlat]⟩
  | d + 1, j, hd => by
    obtain ⟨q, hq, hh, hw, hf⟩ := h.chain_seg v hs d j (by omega)
    have e : N.G.Adj ((Net.parOf r)^[j + d + 1] v) ((Net.parOf r)^[j + d] v) :=
      (h.adj_par (hs (j + d) (by omega))).symm
    refine ⟨.cons e q, ⟨⟨j + d, by omega, by omega, rfl, rfl⟩,
      Walk.AllEdges.mono (fun y y' ⟨l, h1, h2, h3, h4⟩ => ⟨l, h1, by omega, h3, h4⟩) q hq⟩,
      fun l h1 h2 => ?_, ?_, fun f => ?_⟩
    · rcases Nat.lt_or_ge l (j + d) with hl | hl
      · exact .inr (hh l h1 hl)
      · obtain rfl : l = j + d := by omega
        exact .inl ⟨rfl, rfl⟩
    · rw [SsspFlow.Walk.wt_cons, hw, show j + (d + 1) = j + d + 1 from rfl,
        Finset.sum_Ico_succ_top (by omega), ENat.toENNReal_add, add_comm]
      rfl
    · rw [Walk.edgeFlat, hf, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, List.flatten_cons]
      rfl

end Congest

end SsspFlow
