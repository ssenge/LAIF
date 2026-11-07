import SsspFlow.Crossing

/-!
# The exchange at a common vertex

For corners `a, b, c, d, e` in this cyclic order on one face of a planar map, let `P` be a shortest
walk from the tail of `b` to the tail of `c` through the tail of `e`. A walk `W` from the tail of `a`
to the tail of `d` crosses both parts of `P` (`FaceDrawn.crossing`), and replacing the part of `W`
between the two crossings by the part of `P` between them gives a walk through the tail of `e` that
is no longer than `W`. So the distance from `a` to `d` is the distance from `a` to `e` plus the
distance from `e` to `d` (`FaceDrawn.exchange`). This is the form of (C23) of Lemma O in which the
copies of `p_μ` are `a` and `d`, the copies of `p_i` are `b` and `c`, and `e` is a common corner of
`P_i` and a bounding path.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D} {l : List D}

/-- A walk has one end. -/
theorem IsWalk.end_eq {u v v' : R.Vertex} {p : List D} (h : R.IsWalk u p v)
    (h' : R.IsWalk u p v') : v = v' := by
  induction p generalizing u with
  | nil => exact (show u = v from h).symm.trans h'
  | cons x p ih => exact ih h.2 h'.2

/-- The reversal of a walk has its length, for weights that agree on the two darts of each edge. -/
theorem sum_map_reverseCycle (g : D → ℝ≥0∞) (hg : ∀ x, g (R.rev x) = g x) (p : List D) :
    ((R.reverseCycle p).map g).sum = (p.map g).sum := by
  simp only [reverseCycle, List.map_reverse, List.sum_reverse, List.map_map]
  congr 2
  funext x
  exact hg x

/-- **Exchange.** For corners `a, b, c, d, e` in this cyclic order on one face of a planar map, and
a shortest walk `P₁ ++ P₂` from the tail of `b` through the tail of `e` to the tail of `c`, of finite
length, the distance from the tail of `a` to the tail of `d` is at least the distance from `a` to
`e` plus the distance from `e` to `d`. -/
theorem FaceDrawn.exchange (h : R.FaceDrawn l) (g : D → ℝ≥0∞) (hg : ∀ x, g (R.rev x) = g x)
    {a b c d e : D} (hl : [a, b, c, d, e].Sublist l) {P₁ P₂ : List D}
    (h1 : R.IsWalk (R.tail b) P₁ (R.tail e)) (h2 : R.IsWalk (R.tail e) P₂ (R.tail c))
    (hfin : ((P₁ ++ P₂).map g).sum ≠ ⊤)
    (hP : ∀ q, R.IsWalk (R.tail b) q (R.tail c) → ((P₁ ++ P₂).map g).sum ≤ (q.map g).sum) :
    R.walkDist g (R.tail a) (R.tail e) + R.walkDist g (R.tail e) (R.tail d) ≤
      R.walkDist g (R.tail a) (R.tail d) := by
  refine le_iInf₂ fun W hW => ?_
  have hl1 : [a, b, d, e].Sublist l :=
    (List.Sublist.cons_cons a (List.Sublist.cons_cons b ((List.Sublist.cons c
      (List.Sublist.refl [d, e]))))).trans hl
  have hl2 : [a, c, d, e].Sublist l :=
    (List.Sublist.cons_cons a ((List.Sublist.cons b (List.Sublist.refl [c, d, e])))).trans hl
  obtain ⟨t₁, W₁, W₂, Q₁, Q₂, rfl, rfl, hW₁, hW₂, hQ₁, hQ₂⟩ :=
    h.crossing hl1 (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hW h1
  obtain ⟨t₂, V₁, V₂, S₁, S₂, hV, rfl, hV₁, hV₂, hS₁, hS₂⟩ :=
    h.crossing hl2 (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hW h2
  have hfin' : (Q₁.map g).sum + (S₂.map g).sum ≠ ⊤ := by
    simp only [List.map_append, List.sum_append] at hfin
    exact ENNReal.add_ne_top.2 ⟨fun h => hfin (by simp [h]), fun h => hfin (by simp [h])⟩
  -- a walk between the two crossings is at least as long as the part of `P` between them
  have key : ∀ M : List D, R.IsWalk t₁ M t₂ ∨ R.IsWalk t₂ M t₁ →
      (Q₂.map g).sum + (S₁.map g).sum ≤ (M.map g).sum := by
    intro M hM
    have hq : ∃ q, R.IsWalk (R.tail b) q (R.tail c) ∧
        (q.map g).sum = (Q₁.map g).sum + (M.map g).sum + (S₂.map g).sum := by
      rcases hM with hM | hM
      · exact ⟨Q₁ ++ M ++ S₂, (hQ₁.append hM).append hS₂, by
          simp only [List.map_append, List.sum_append]⟩
      · exact ⟨Q₁ ++ R.reverseCycle M ++ S₂, (hQ₁.append hM.reverse).append hS₂, by
          simp only [List.map_append, List.sum_append, sum_map_reverseCycle g hg]⟩
    obtain ⟨q, hq, hqs⟩ := hq
    have hle := hP q hq
    rw [hqs] at hle
    simp only [List.map_append, List.sum_append] at hle
    refine (ENNReal.add_le_add_iff_left hfin').1 ?_
    calc (Q₁.map g).sum + (S₂.map g).sum + ((Q₂.map g).sum + (S₁.map g).sum)
        = (Q₁.map g).sum + (Q₂.map g).sum + ((S₁.map g).sum + (S₂.map g).sum) := by ring
      _ ≤ (Q₁.map g).sum + (M.map g).sum + (S₂.map g).sum := hle
      _ = (Q₁.map g).sum + (S₂.map g).sum + (M.map g).sum := by ring
  rcases List.append_eq_append_iff.1 hV with ⟨M, rfl, rfl⟩ | ⟨M, rfl, rfl⟩
  · obtain ⟨s, hs1, hs2⟩ := isWalk_append_iff.1 hV₁
    obtain rfl := hW₁.end_eq hs1
    have hk := key M (Or.inl hs2)
    calc _ ≤ ((W₁ ++ Q₂).map g).sum + ((S₁ ++ V₂).map g).sum :=
          add_le_add (walkDist_le g (hW₁.append hQ₂)) (walkDist_le g (hS₁.append hV₂))
      _ = (W₁.map g).sum + ((Q₂.map g).sum + (S₁.map g).sum) + (V₂.map g).sum := by
          simp only [List.map_append, List.sum_append]
          ring
      _ ≤ (W₁.map g).sum + (M.map g).sum + (V₂.map g).sum := by gcongr
      _ = ((W₁ ++ (M ++ V₂)).map g).sum := by
          simp only [List.map_append, List.sum_append]
          ring
  · obtain ⟨s, hs1, hs2⟩ := isWalk_append_iff.1 hW₁
    obtain rfl := hV₁.end_eq hs1
    have hk := key M (Or.inr hs2)
    calc _ ≤ ((V₁ ++ R.reverseCycle S₁).map g).sum + ((R.reverseCycle Q₂ ++ W₂).map g).sum :=
          add_le_add (walkDist_le g (hV₁.append hS₁.reverse))
            (walkDist_le g (hQ₂.reverse.append hW₂))
      _ = (V₁.map g).sum + ((Q₂.map g).sum + (S₁.map g).sum) + (W₂.map g).sum := by
          simp only [List.map_append, List.sum_append, sum_map_reverseCycle g hg]
          ring
      _ ≤ (V₁.map g).sum + (M.map g).sum + (W₂.map g).sum := by gcongr
      _ = ((V₁ ++ M ++ W₂).map g).sum := by
          simp only [List.map_append, List.sum_append]

end RotSystem

end SsspFlow
