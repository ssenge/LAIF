import SsspFlow.OracleMark

/-!
# Sums along the parent chains of an oracle

With length `f a` on the arc from a node `a` to its parent and `⊤` on every other arc, a walk of
finite length follows the parents, and its length is the sum of `f` over its nodes but the last. So
one more run of the oracle from a set of targets gives, at each node of their chains, the least sum
of `f` from a target up to the node.

* `Net.markLenW`: the lengths `f a` on the arcs to the parents.
* `Net.walk_markW`: a walk of finite length follows the parents, with the sum of `f` as length.
* `Net.ExactSpec.walk_parW`: the chain from a node, along valid parent steps, is such a walk.
* `Net.ExactSpec.dsrcTop_markW`: the distance from the targets is the least sum of `f` along the
  parent steps from a target up to the node.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The lengths `f a` on the arc from each node `a` to its parent, `⊤` elsewhere. -/
def Net.markLenW (r : V → ℕ∞ × Option V) (f : V → ℕ∞) (a b : V) : ℕ∞ :=
  if (r a).2 = some b then f a else ⊤

/-- The parent steps from `a` are valid for `i` steps. -/
def Net.ParSteps (r : V → ℕ∞ × Option V) (a : V) (i : ℕ) : Prop :=
  ∀ k < i, (r ((Net.parOf r)^[k] a)).2 = some ((Net.parOf r)^[k + 1] a)

/-- **Walks follow the parents.** A walk of finite length for `markLenW` from `a` to `b` takes valid
parent steps from `a` to `b`, and its length is the sum of `f` over the nodes before `b`. -/
theorem Net.walk_markW {N : Net V} {r : V → ℕ∞ × Option V} {f : V → ℕ∞} :
    ∀ {a b : V} (q : SsspFlow.Walk N.G.Adj a b), q.wt (lenTop (Net.markLenW r f)) ≠ ⊤ →
      ∃ i, Net.ParSteps r a i ∧ (Net.parOf r)^[i] a = b ∧
        q.wt (lenTop (Net.markLenW r f)) = ((∑ k ∈ Finset.range i, f ((Net.parOf r)^[k] a) : ℕ∞) : ℝ≥0∞)
  | _, _, .nil _, _ => ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k), rfl, by simp [SsspFlow.Walk.wt]⟩
  | a, _, .cons (b := b) _ q, hq => by
    rw [SsspFlow.Walk.wt_cons] at hq ⊢
    have h1 : lenTop (Net.markLenW r f) a b ≠ ⊤ := fun e => hq (by rw [e, top_add])
    have h2 : (r a).2 = some b := by
      by_contra hc
      exact h1 (by simp [lenTop, Net.markLenW, hc])
    have hpar : Net.parOf r a = b := Net.parOf_some h2
    have hit : ∀ k, (Net.parOf r)^[k + 1] a = (Net.parOf r)^[k] b := fun k => by
      rw [Function.iterate_succ_apply, hpar]
    obtain ⟨i, hi, he, hw⟩ := Net.walk_markW q (fun e => hq (by rw [e, add_top]))
    refine ⟨i + 1, fun k hk => ?_, by rw [hit]; exact he, ?_⟩
    · cases k with
      | zero => simpa [hpar] using h2
      | succ k =>
        rw [hit, hit (k + 1)]
        exact hi k (by omega)
    · rw [hw, Finset.sum_range_succ', ENat.toENNReal_add]
      simp only [hit, Function.iterate_zero, id_eq]
      rw [add_comm]
      simp [lenTop, Net.markLenW, h2]

/-- A node with a parent is adjacent to it. -/
theorem Net.ExactSpec.adj_par {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) {y p : V} (hy : (r y).2 = some p) : N.G.Adj y p := by
  obtain ⟨rank, hrank⟩ := h.parent
  rcases hrank y with ⟨p', hp', hadj, -⟩ | ⟨hn, -⟩
  · rw [hy] at hp'
    cases hp'
    exact hadj.symm
  · rw [hy] at hn
    cases hn

/-- **The chain is a walk.** Along `i` valid parent steps from `y` there is a walk to
`parOf^[i] y` whose length is the sum of `f` over the nodes before the last. -/
theorem Net.ExactSpec.walk_parW {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (f : V → ℕ∞) :
    ∀ (i : ℕ) (y : V), Net.ParSteps r y i → ∃ p : SsspFlow.Walk N.G.Adj y ((Net.parOf r)^[i] y),
      p.wt (lenTop (Net.markLenW r f)) = ((∑ k ∈ Finset.range i, f ((Net.parOf r)^[k] y) : ℕ∞) : ℝ≥0∞)
  | 0, y, _ => ⟨.nil y, by simp [SsspFlow.Walk.wt]⟩
  | i + 1, y, hs => by
    have h0 : (r y).2 = some (Net.parOf r y) := by simpa using hs 0 (by omega)
    have hit : ∀ k, (Net.parOf r)^[k + 1] y = (Net.parOf r)^[k] (Net.parOf r y) := fun k =>
      Function.iterate_succ_apply _ _ _
    have hs' : Net.ParSteps r (Net.parOf r y) i := fun k hk => by
      rw [← hit, ← hit (k + 1)]
      exact hs (k + 1) (by omega)
    obtain ⟨q, hq⟩ := h.walk_parW f i (Net.parOf r y) hs'
    let q' : SsspFlow.Walk N.G.Adj y ((Net.parOf r)^[i] (Net.parOf r y)) := .cons (h.adj_par h0) q
    have hw : q'.wt (lenTop (Net.markLenW r f)) =
        ((∑ k ∈ Finset.range (i + 1), f ((Net.parOf r)^[k] y) : ℕ∞) : ℝ≥0∞) := by
      simp only [q']
      rw [SsspFlow.Walk.wt_cons, hq, Finset.sum_range_succ', ENat.toENNReal_add, add_comm]
      simp only [hit, Function.iterate_zero, id_eq]
      simp [lenTop, Net.markLenW, h0]
    exact ⟨q', hw⟩

open Classical in
/-- **Sums along the chains.** With length `f a` on the arc from each node to its parent and offset
`0` at the targets, the distance from the virtual source at `x` is the least sum of `f` along valid
parent steps from a target to `x`, over the nodes before `x`. -/
theorem Net.ExactSpec.dsrcTop_markW {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (f : V → ℕ∞) (isT : V → Bool) (x : V) :
    N.dsrcTop (Net.markLenW r f) (Net.markOffB isT) x =
      ⨅ t, ⨅ (_ : isT t = true), ⨅ i, ⨅ (_ : Net.ParSteps r t i ∧ (Net.parOf r)^[i] t = x),
        ((∑ k ∈ Finset.range i, f ((Net.parOf r)^[k] t) : ℕ∞) : ℝ≥0∞) := by
  unfold Net.dsrcTop dsrc
  apply le_antisymm
  · refine le_iInf fun t => le_iInf fun ht => le_iInf fun i => le_iInf fun ⟨hs, hx⟩ => ?_
    subst hx
    obtain ⟨p, hp⟩ := h.walk_parW f i t hs
    refine iInf_le_of_le t ?_
    have h0 : offTop (Net.markOffB isT) t = 0 := by simp [offTop, Net.markOffB, ht]
    rw [h0, zero_add]
    unfold dist
    exact iInf₂_le_of_le p (fun _ _ => Set.mem_univ _) hp.le
  · refine le_iInf fun a => ?_
    by_cases ha : isT a = true
    · have h0 : offTop (Net.markOffB isT) a = 0 := by simp [offTop, Net.markOffB, ha]
      rw [h0, zero_add]
      unfold dist
      refine le_iInf₂ fun p _ => ?_
      by_cases hp : p.wt (lenTop (Net.markLenW r f)) = ⊤
      · rw [hp]
        exact le_top
      · obtain ⟨i, hs, hx, hw⟩ := Net.walk_markW p hp
        rw [hw]
        exact iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le i (iInf_le_of_le ⟨hs, hx⟩ le_rfl)))
    · simp [offTop, Net.markOffB, ha]

end Congest

end SsspFlow
