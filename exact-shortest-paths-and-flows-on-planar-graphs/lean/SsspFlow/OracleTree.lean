import SsspFlow.LabelHypothesis

/-!
# The parent chains of an exact shortest-path oracle

An output that meets `Net.ExactSpec` gives every node a distance and, unless it is a root, a parent.
Following the parents (`Net.parOf`) from a node of finite distance never cycles, since the rank drops
at every step.

* `Net.ExactSpec.chain`: the chain from a node of finite distance reaches a root after finitely many
  steps; consecutive nodes of the chain are adjacent, the root has distance equal to its offset, and
  the offset of the root plus the lengths along the chain is the distance of the node. So the chain,
  read from the root, is a shortest walk from the virtual source.
* `Net.ExactSpec.dsrcTop_mark`: with length `0` on the arc from a node to its parent and `⊤` on every
  other arc, the distance from a virtual source at `t` is `0` at the nodes `parOf^[i] t` and `⊤`
  elsewhere. So one more run of the oracle marks the chain of `t`.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The parent of a node in an output of the oracle, the node itself at a root. -/
def Net.parOf (r : V → ℕ∞ × Option V) (v : V) : V := (r v).2.getD v

omit [Fintype V] [DecidableEq V] in
theorem Net.parOf_some {r : V → ℕ∞ × Option V} {v p : V} (h : (r v).2 = some p) : Net.parOf r v = p := by
  simp [Net.parOf, h]

/-- **The parent chain.** From a node of finite distance, the parents lead to a root after `k` steps;
the root has distance equal to its offset, and this offset plus the lengths along the chain is the
distance of the node. -/
theorem Net.ExactSpec.chain {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (v : V) (hv : (r v).1 ≠ ⊤) :
    ∃ k, (r ((Net.parOf r)^[k] v)).2 = none ∧ (r ((Net.parOf r)^[k] v)).1 = φ ((Net.parOf r)^[k] v) ∧
      (∀ i < k, (r ((Net.parOf r)^[i] v)).2 = some ((Net.parOf r)^[i + 1] v) ∧
        N.G.Adj ((Net.parOf r)^[i + 1] v) ((Net.parOf r)^[i] v)) ∧
      φ ((Net.parOf r)^[k] v) +
        ∑ i ∈ Finset.range k, ℓ ((Net.parOf r)^[i + 1] v) ((Net.parOf r)^[i] v) = (r v).1 := by
  obtain ⟨rank, hrank⟩ := h.parent
  induction hn : rank v using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    rcases hrank v with ⟨p, hp, hadj, -, hsum, hlt⟩ | ⟨hnone, htop | hφ⟩
    · have hpar : Net.parOf r v = p := Net.parOf_some hp
      have hpt : (r p).1 ≠ ⊤ := fun e => hv (by rw [← hsum, e, top_add])
      obtain ⟨k, h1, h2, h3, h4⟩ := ih (rank p) (hn ▸ hlt) p hpt rfl
      have hit : ∀ i, (Net.parOf r)^[i + 1] v = (Net.parOf r)^[i] p := fun i => by
        rw [Function.iterate_succ_apply, hpar]
      refine ⟨k + 1, by rw [hit]; exact h1, by rw [hit]; exact h2, fun i hi => ?_, ?_⟩
      · cases i with
        | zero =>
          simp only [Function.iterate_zero, id_eq, zero_add, Function.iterate_one, hpar]
          exact ⟨hp, hadj⟩
        | succ i =>
          rw [hit, hit (i + 1)]
          exact h3 i (by omega)
      · rw [Finset.sum_range_succ', hit k]
        simp only [hit, Function.iterate_zero, id_eq, zero_add]
        rw [← add_assoc, h4, hsum]
    · exact absurd htop hv
    · exact ⟨0, hnone, hφ, fun i hi => absurd hi (Nat.not_lt_zero i), by simp [hφ]⟩

/-- The lengths of the marking run: `0` on the arc from a node to its parent, `⊤` elsewhere. -/
def Net.markLen (r : V → ℕ∞ × Option V) (a b : V) : ℕ∞ := if (r a).2 = some b then 0 else ⊤

/-- The offsets of the marking run: `0` at `t`, `⊤` elsewhere. -/
def Net.markOff (t a : V) : ℕ∞ := if a = t then 0 else ⊤

theorem Net.ExactSpec.walk_par {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) :
    ∀ (i : ℕ) (y : V), ∃ p : SsspFlow.Walk N.G.Adj y ((Net.parOf r)^[i] y),
      p.wt (lenTop (Net.markLen r)) = 0
  | 0, y => ⟨.nil y, rfl⟩
  | i + 1, y => by
    rw [Function.iterate_succ_apply]
    cases hy : (r y).2 with
    | none =>
      have hp : Net.parOf r y = y := by simp [Net.parOf, hy]
      rw [hp]
      exact h.walk_par i y
    | some p =>
      have hadj : N.G.Adj y p := by
        obtain ⟨rank, hrank⟩ := h.parent
        rcases hrank y with ⟨p', hp', hadj, -⟩ | ⟨hn, -⟩
        · rw [hy] at hp'
          cases hp'
          exact hadj.symm
        · rw [hy] at hn
          cases hn
      rw [Net.parOf_some hy]
      obtain ⟨q, hq⟩ := h.walk_par i p
      exact ⟨.cons hadj q, by simp [lenTop, Net.markLen, hy, hq]⟩

theorem Net.mark_closed {N : Net V} {r : V → ℕ∞ × Option V} {t : V} :
    ∀ {a b : V} (q : SsspFlow.Walk N.G.Adj a b), q.wt (lenTop (Net.markLen r)) ≠ ⊤ →
      (∃ i, (Net.parOf r)^[i] t = a) → ∃ i, (Net.parOf r)^[i] t = b
  | _, _, .nil _, _, ha => ha
  | a, _, .cons (b := b) _ q, hq, ⟨i, hi⟩ => by
    rw [SsspFlow.Walk.wt_cons] at hq
    have h1 : lenTop (Net.markLen r) a b ≠ ⊤ := fun e => hq (by rw [e, top_add])
    have h2 : (r a).2 = some b := by
      by_contra hc
      exact h1 (by simp [lenTop, Net.markLen, hc])
    refine Net.mark_closed q (fun e => hq (by rw [e, add_top])) ⟨i + 1, ?_⟩
    rw [Function.iterate_succ_apply', hi, Net.parOf_some h2]

open Classical in
/-- **The marking run.** With length `0` on the arc from each node to its parent and offset `0` at
`t` only, the distance from the virtual source is `0` on the chain of `t` and `⊤` elsewhere. -/
theorem Net.ExactSpec.dsrcTop_mark {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (t x : V) :
    N.dsrcTop (Net.markLen r) (Net.markOff t) x = if ∃ i, (Net.parOf r)^[i] t = x then (0 : ℝ≥0∞) else ⊤ := by
  unfold Net.dsrcTop dsrc
  split_ifs with hx
  · obtain ⟨i, rfl⟩ := hx
    obtain ⟨p, hp⟩ := h.walk_par i t
    refine le_antisymm (iInf_le_of_le t ?_) zero_le
    have h0 : offTop (Net.markOff t) t = 0 := by simp [offTop, Net.markOff]
    rw [h0, zero_add]
    unfold dist
    exact iInf₂_le_of_le p (fun _ _ => Set.mem_univ _) hp.le
  · refine top_le_iff.1 (le_iInf fun a => ?_)
    by_cases ha : a = t
    · subst ha
      unfold dist
      refine le_trans (le_iInf₂ fun p _ => ?_) le_add_self
      by_contra hc
      exact hx (Net.mark_closed p (ne_top_of_lt (not_le.1 hc)) ⟨0, rfl⟩)
    · simp [offTop, Net.markOff, ha]

end Congest

end SsspFlow
