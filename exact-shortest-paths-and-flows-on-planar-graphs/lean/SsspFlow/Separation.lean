import SsspFlow.WitnessInterval
import SsspFlow.Crossing

/-!
# The separation step (S_1) from planarity

The separation step (S_1) of Lemma S1 in `notes/RECURSION.md`, for a level-one annulus drawn as a
planar map: cutting along the dual path `P` leaves its two copies on one face, in the order
`p_0^0, …, p_m^0, p_m^1, …, p_0^1`.

* `RotSystem.adjGraph`: the simple graph of a rotation system, in which two distinct vertices are
  adjacent if a dart joins them. `RotSystem.exists_isWalk`: each of its walks is a walk of darts
  through the same vertices.
* `Annulus.sep_of_faceDrawn`: if every edge of `A_1` joins the ends of a dart of a planar map, and
  the copies of `P` are the tails of corners of one face in the order above, then `Sep` holds. For
  `x < t < y` the corners of `p_x^0, p_t^0, p_y^1, p_t^1` lie in this cyclic order, and for
  `y < t < x` those of `p_t^0, p_x^0, p_t^1, p_y^1`, so `FaceDrawn.crossing` gives a common vertex.
* `Annulus.witness_interval_of_faceDrawn`: Lemma S1 for such an annulus, with no further hypothesis.
-/

set_option autoImplicit false

namespace SsspFlow

open SimpleGraph

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- The simple graph of a rotation system: two distinct vertices are adjacent if a dart joins
them. -/
def adjGraph : SimpleGraph R.Vertex where
  Adj u v := u ≠ v ∧ ∃ x, R.tail x = u ∧ R.head x = v
  symm := ⟨fun _ _ ⟨h, x, hx, hy⟩ => ⟨h.symm, R.rev x, hy, by rw [R.head_rev, hx]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A walk of `adjGraph` is a walk of darts through the same vertices. -/
theorem exists_isWalk : ∀ {u v : R.Vertex} (p : R.adjGraph.Walk u v),
    ∃ q : List D, R.IsWalk u q v ∧ p.support = u :: q.map R.head
  | _, _, .nil => ⟨[], rfl, rfl⟩
  | _, _, .cons h p => by
      obtain ⟨q, hq, hs⟩ := exists_isWalk p
      obtain ⟨x, hx, hy⟩ := h.2
      refine ⟨x :: q, ⟨hx, by rw [hy]; exact hq⟩, ?_⟩
      rw [Walk.support_cons, hs, List.map_cons, hy]

variable {R}

/-- The end of a walk of darts is its start or the head of one of its darts. -/
theorem IsWalk.mem_heads {u t : R.Vertex} : ∀ {p : List D}, R.IsWalk u p t →
    t = u ∨ t ∈ p.map R.head
  | [], h => Or.inl (show u = t from h).symm
  | x :: p, h => by
      rcases IsWalk.mem_heads h.2 with e | e
      · exact Or.inr (by rw [e, List.map_cons]; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ e)

end RotSystem

namespace Recursion

open RotSystem

variable {D : Type*}

theorem pair_sublist_range {a b n : ℕ} (hab : a < b) (hbn : b < n) :
    [a, b].Sublist (List.range n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ]
    rcases Nat.lt_or_ge b n with h | h
    · exact (ih h).trans (List.sublist_append_left _ _)
    · obtain rfl : b = n := by omega
      exact List.Sublist.append (List.singleton_sublist.2 (List.mem_range.2 hab))
        (List.Sublist.refl _)

/-- The corners of the copies of `P` along one face: `p_0^0, …, p_m^0`, then `p_m^1, …, p_0^1`. -/
def copyCorners (k : Fin 2 → ℕ → D) (m : ℕ) : List D :=
  (List.range (m + 1)).map (k 0) ++ ((List.range (m + 1)).reverse).map (k 1)

theorem copyCorners_sublist (k : Fin 2 → ℕ → D) {m a b c d : ℕ} (hab : a < b) (hb : b ≤ m)
    (hcd : d < c) (hc : c ≤ m) : [k 0 a, k 0 b, k 1 c, k 1 d].Sublist (copyCorners k m) := by
  have h0 : [k 0 a, k 0 b].Sublist ((List.range (m + 1)).map (k 0)) :=
    (pair_sublist_range hab (by omega)).map (k 0)
  have h1 : [k 1 c, k 1 d].Sublist ((List.range (m + 1)).reverse.map (k 1)) :=
    (List.reverse_sublist.2 (pair_sublist_range hcd (by omega))).map (k 1)
  exact h0.append h1

variable [Fintype D] [DecidableEq D]

namespace Annulus

/-- A vertex where a walk of darts splits lies on the vertex list of the walk. -/
theorem mem_of_split {R : RotSystem D} {u u' τ : R.Vertex} {S : List R.Vertex}
    {r r₁ r₂ : List D} (hs : S = u' :: r.map R.head) (hu : u = u') (hr : r = r₁ ++ r₂)
    (h₁ : R.IsWalk u r₁ τ) : τ ∈ S := by
  rw [hs]
  rcases h₁.mem_heads with e | e
  · rw [e, hu]
    exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (by rw [hr, List.map_append]; exact List.mem_append_left _ e)

/-- **(S_1) from planarity.** If every edge of `A_1` joins the ends of a dart of a planar map, and
the copies of `P` are the tails of corners of one face in the order `p_0^0, …, p_m^0, p_m^1, …,
p_0^1`, then every walk from `p_x^0` to `p_y^1` meets every walk between the two copies of a face
strictly between `p_x` and `p_y`. -/
theorem sep_of_faceDrawn {R : RotSystem D} (A : Annulus R.Vertex) (hG : A.G ≤ R.adjGraph)
    (k : Fin 2 → ℕ → D) (hk : ∀ σ t, t ≤ A.m → R.tail (k σ t) = A.c σ t)
    (hl : R.FaceDrawn (copyCorners k A.m)) : A.Sep := by
  intro x y hx hy Q _ t h1 h2 W
  obtain ⟨q, hq, hqs⟩ := R.exists_isWalk (Q.mapLe hG)
  obtain ⟨r, hr, hrs⟩ := R.exists_isWalk (W.mapLe hG)
  rw [Walk.support_mapLe_eq_support] at hqs hrs
  have ht : t ≤ A.m := by omega
  have hq' : R.IsWalk (R.tail (k 0 x)) q (R.tail (k 1 y)) := by
    rw [hk 0 x hx, hk 1 y hy]
    exact hq
  have hr' : R.IsWalk (R.tail (k 0 t)) r (R.tail (k 1 t)) := by
    rw [hk 0 t ht, hk 1 t ht]
    exact hr
  rcases lt_or_gt_of_ne (show x ≠ y by omega) with hxy | hxy
  · obtain ⟨τ, q₁, q₂, r₁, r₂, hq₀, hr₀, hq₁, -, hr₁, -⟩ :=
      hl.crossing (copyCorners_sublist k (show x < t by omega) (by omega) (show t < y by omega) hy)
        (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hq' hr'
    exact ⟨τ, mem_of_split hrs (hk 0 t ht) hr₀ hr₁, mem_of_split hqs (hk 0 x hx) hq₀ hq₁⟩
  · obtain ⟨τ, r₁, r₂, q₁, q₂, hr₀, hq₀, hr₁, -, hq₁, -⟩ :=
      hl.crossing (copyCorners_sublist k (show t < x by omega) hx (show y < t by omega) (by omega))
        (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hr' hq'
    exact ⟨τ, mem_of_split hrs (hk 0 t ht) hr₀ hr₁, mem_of_split hqs (hk 0 x hx) hq₀ hq₁⟩

/-- **Lemma S1** for an annulus drawn as a planar map with the copies of `P` on one face. -/
theorem witness_interval_of_faceDrawn {R : RotSystem D} (A : Annulus R.Vertex)
    (hG : A.G ≤ R.adjGraph) (k : Fin 2 → ℕ → D) (hk : ∀ σ t, t ≤ A.m → R.tail (k σ t) = A.c σ t)
    (hl : R.FaceDrawn (copyCorners k A.m)) {i : ℕ} (hi : i ≤ A.m)
    (P : A.G.Walk (A.c 0 i) (A.c 1 i)) (hP : wlen A.w P = A.lam i) :
    ∃ i1 i2, IsLeast (A.copies P) i1 ∧ IsGreatest (A.copies P) i2 ∧ i1 ≤ i ∧ i ≤ i2 ∧
      ∀ t, i1 < t → t < i2 →
        (∀ q, i1 ≤ q → q ≤ t → A.lam q ≤ A.lam t) ∨ (∀ q, t ≤ q → q ≤ i2 → A.lam q ≤ A.lam t) :=
  A.witness_interval (A.sep_of_faceDrawn hG k hk hl) hi P hP

end Annulus

end Recursion

end SsspFlow
