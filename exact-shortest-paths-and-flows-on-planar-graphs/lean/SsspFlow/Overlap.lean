import SsspFlow.Exchange

/-!
# The overlap rule

A live annulus of the recursion is drawn with its boundary on one face, in the cyclic order

  `κ0 xa, …, κ0 xb, Lb, κ1 yb, …, κ1 ya, La`,

where `κ0 t` and `κ1 t` are the corners of its pieces of `p_t^0` and `p_t^1`, `La` holds the
corners of the inner vertices of the bounding path `P_a` from the piece of `p_{x_a}^0` to the piece
of `p_{y_a}^1`, and `Lb` those of `P_b` from the piece of `p_{x_b}^0` to the piece of `p_{y_b}^1`.

If a shortest walk `P_i` from the piece of `p_i^0` to the piece of `p_i^1` meets `P_a` at a vertex
`z`, then for every `μ` with `max xa ya ≤ μ ≤ i` the distance between the pieces of `p_μ^0` and
`p_μ^1` is the distance from the first to `z` plus the distance from `z` to the second
(`FaceDrawn.overlap_a`). This is (C23) of Lemma O. If `P_i` meets `P_b`, the same holds for every `μ`
with `i ≤ μ ≤ min xb yb` (`FaceDrawn.overlap_b`). Both follow from `FaceDrawn.exchange`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor List
open scoped ENNReal

/-- The list `f a, f (a + 1), …, f b`. -/
def cornerSeg {α : Type*} (f : ℕ → α) (a b : ℕ) : List α := (List.range' a (b + 1 - a)).map f

/-- Values of `f` at increasing indices between `a` and `b` form a sublist of `cornerSeg f a b`. -/
theorem sublist_cornerSeg {α : Type*} (f : ℕ → α) {a b : ℕ} {l : List ℕ}
    (hl : l.Pairwise (· < ·)) (h : ∀ s ∈ l, a ≤ s ∧ s ≤ b) : l.map f <+ cornerSeg f a b :=
  (List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hl.nodup fun s hs => by
    have := h s hs
    exact List.mem_range'_1.2 ⟨this.1, by omega⟩) hl List.pairwise_lt_range').map f

theorem cornerSeg_cons {α : Type*} (f : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    cornerSeg f a b = f a :: cornerSeg f (a + 1) b := by
  rw [cornerSeg, show b + 1 - a = (b - a) + 1 by omega, List.range'_succ, List.map_cons, cornerSeg,
    show b + 1 - (a + 1) = b - a by omega]

/-- Two parts of a sublist in the other order are a sublist of a rotation. -/
theorem exists_isRotated_sublist {α : Type*} {xs ys l : List α} (h : (xs ++ ys) <+ l) :
    ∃ l', l ~r l' ∧ (ys ++ xs) <+ l' := by
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.append_sublist_iff.1 h
  exact ⟨l₂ ++ l₁, List.isRotated_append, h2.append h1⟩

namespace RotSystem

variable {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E} {l : List E}

theorem FaceDrawn.rotate (h : M.FaceDrawn l) (n : ℕ) : M.FaceDrawn (l.rotate n) where
  planar := h.planar
  tails_nodup := by
    rw [List.map_rotate]
    exact List.nodup_rotate.2 h.tails_nodup
  order := by
    have hS : (l.rotate n).toFinset = l.toFinset := by
      ext x
      simp
    rw [hS, List.formPerm_rotate l h.nodup n, h.order]

theorem FaceDrawn.of_isRotated {l' : List E} (h : M.FaceDrawn l) (hr : l ~r l') :
    M.FaceDrawn l' := by
  obtain ⟨n, rfl⟩ := hr
  exact h.rotate n

/-- Distances are symmetric for weights that agree on the two darts of each edge. -/
theorem walkDist_comm (g : E → ℝ≥0∞) (hg : ∀ x, g (M.rev x) = g x) (u v : M.Vertex) :
    M.walkDist g u v = M.walkDist g v u := by
  have key : ∀ u v : M.Vertex, M.walkDist g v u ≤ M.walkDist g u v := fun u v =>
    le_iInf₂ fun p hp => (walkDist_le g hp.reverse).trans_eq (sum_map_reverseCycle g hg p)
  exact le_antisymm (key v u) (key u v)

/-- **The distance through a common vertex.** For corners `a, b, c, d, e` in this cyclic order on
one face of a planar map and a shortest walk from the tail of `b` through the tail of `e` to the
tail of `c`, the distance from `a` to `d` is the distance from `a` to `e` plus the distance from
`e` to `d`. -/
theorem FaceDrawn.dist_through (h : M.FaceDrawn l) (g : E → ℝ≥0∞) (hg : ∀ x, g (M.rev x) = g x)
    {a b c d e : E} (hl : [a, b, c, d, e].Sublist l) {P₁ P₂ : List E}
    (h1 : M.IsWalk (M.tail b) P₁ (M.tail e)) (h2 : M.IsWalk (M.tail e) P₂ (M.tail c))
    (hfin : ((P₁ ++ P₂).map g).sum ≠ ⊤)
    (hP : ∀ q, M.IsWalk (M.tail b) q (M.tail c) → ((P₁ ++ P₂).map g).sum ≤ (q.map g).sum) :
    M.walkDist g (M.tail a) (M.tail e) + M.walkDist g (M.tail e) (M.tail d) =
      M.walkDist g (M.tail a) (M.tail d) :=
  le_antisymm (h.exchange g hg hl h1 h2 hfin hP) (walkDist_triangle g _ _ _)

/-- A shortest walk through a vertex: the two distances to it add up to the distance of the
ends. -/
theorem dist_through_ends (g : E → ℝ≥0∞) {u v w : M.Vertex} {P₁ P₂ : List E}
    (h1 : M.IsWalk u P₁ w) (h2 : M.IsWalk w P₂ v)
    (hP : ∀ q, M.IsWalk u q v → ((P₁ ++ P₂).map g).sum ≤ (q.map g).sum) :
    M.walkDist g u w + M.walkDist g w v = M.walkDist g u v := by
  refine le_antisymm ?_ (walkDist_triangle g _ _ _)
  calc _ ≤ (P₁.map g).sum + (P₂.map g).sum := add_le_add (walkDist_le g h1) (walkDist_le g h2)
    _ = ((P₁ ++ P₂).map g).sum := by rw [List.map_append, List.sum_append]
    _ ≤ _ := le_iInf₂ fun q hq => hP q hq

variable {κ0 κ1 : ℕ → E} {xa xb ya yb : ℕ} {La Lb : List E}

/-- **(C23) on the side of `P_a`.** Let the boundary of a planar map read
`κ0 xa, …, κ0 xb, Lb, κ1 yb, …, κ1 ya, La`, and let a shortest walk from the tail of `κ0 i` to the
tail of `κ1 i` pass through the tail of a corner `c` of `κ0 xa, La` or `κ1 ya`. Then for
`max xa ya ≤ μ ≤ i` the distance from `κ0 μ` to `κ1 μ` is the distance from `κ0 μ` to `c` plus the
distance from `c` to `κ1 μ`. -/
theorem FaceDrawn.overlap_a
    (h : M.FaceDrawn (cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La))
    (g : E → ℝ≥0∞) (hg : ∀ x, g (M.rev x) = g x) {i μ : ℕ} (hxμ : xa ≤ μ) (hyμ : ya ≤ μ)
    (hμi : μ ≤ i) (hix : i ≤ xb) (hiy : i ≤ yb) {c : E} (hc : c = κ0 xa ∨ c ∈ La ∨ c = κ1 ya)
    {P₁ P₂ : List E} (h1 : M.IsWalk (M.tail (κ0 i)) P₁ (M.tail c))
    (h2 : M.IsWalk (M.tail c) P₂ (M.tail (κ1 i))) (hfin : ((P₁ ++ P₂).map g).sum ≠ ⊤)
    (hP : ∀ q, M.IsWalk (M.tail (κ0 i)) q (M.tail (κ1 i)) →
      ((P₁ ++ P₂).map g).sum ≤ (q.map g).sum) :
    M.walkDist g (M.tail (κ0 μ)) (M.tail c) + M.walkDist g (M.tail c) (M.tail (κ1 μ)) =
      M.walkDist g (M.tail (κ0 μ)) (M.tail (κ1 μ)) := by
  rcases hμi.lt_or_eq with hlt | rfl
  · have s0 : [κ0 μ, κ0 i] <+ cornerSeg κ0 xa xb :=
      sublist_cornerSeg κ0 (l := [μ, i]) (by simp; omega) (by simp; omega)
    have s1 : [κ1 i, κ1 μ] <+ (cornerSeg κ1 ya yb).reverse :=
      (sublist_cornerSeg κ1 (l := [μ, i]) (by simp; omega) (by simp; omega)).reverse
    rcases hc with rfl | hc | rfl
    · rcases hxμ.lt_or_eq with hxlt | rfl
      · have s0' : [κ0 xa, κ0 μ, κ0 i] <+ cornerSeg κ0 xa xb :=
          sublist_cornerSeg κ0 (l := [xa, μ, i]) (by simp; omega) (by simp; omega)
        have hs : ([κ0 xa] ++ [κ0 μ, κ0 i, κ1 i, κ1 μ]) <+
            cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La :=
          ((s0'.append (List.nil_sublist Lb)).append s1).append (List.nil_sublist La)
        obtain ⟨l', hr, hs'⟩ := exists_isRotated_sublist hs
        exact (h.of_isRotated hr).dist_through g hg hs' h1 h2 hfin hP
      · rw [walkDist_self, zero_add]
    · exact h.dist_through g hg (((s0.append (List.nil_sublist Lb)).append s1).append
        (List.singleton_sublist.2 hc)) h1 h2 hfin hP
    · rcases hyμ.lt_or_eq with hylt | rfl
      · have s1' : [κ1 i, κ1 μ, κ1 ya] <+ (cornerSeg κ1 ya yb).reverse :=
          (sublist_cornerSeg κ1 (l := [ya, μ, i]) (by simp; omega) (by simp; omega)).reverse
        exact h.dist_through g hg (((s0.append (List.nil_sublist Lb)).append s1').append
          (List.nil_sublist La)) h1 h2 hfin hP
      · rw [walkDist_self, add_zero]
  · exact dist_through_ends g h1 h2 hP

/-- **(C23) on the side of `P_b`.** The same with a corner `c` of `κ0 xb, Lb` or `κ1 yb` and
`i ≤ μ ≤ min xb yb`. -/
theorem FaceDrawn.overlap_b
    (h : M.FaceDrawn (cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La))
    (g : E → ℝ≥0∞) (hg : ∀ x, g (M.rev x) = g x) {i μ : ℕ} (hxi : xa ≤ i) (hyi : ya ≤ i)
    (hiμ : i ≤ μ) (hμx : μ ≤ xb) (hμy : μ ≤ yb) {c : E} (hc : c = κ0 xb ∨ c ∈ Lb ∨ c = κ1 yb)
    {P₁ P₂ : List E} (h1 : M.IsWalk (M.tail (κ0 i)) P₁ (M.tail c))
    (h2 : M.IsWalk (M.tail c) P₂ (M.tail (κ1 i))) (hfin : ((P₁ ++ P₂).map g).sum ≠ ⊤)
    (hP : ∀ q, M.IsWalk (M.tail (κ0 i)) q (M.tail (κ1 i)) →
      ((P₁ ++ P₂).map g).sum ≤ (q.map g).sum) :
    M.walkDist g (M.tail (κ0 μ)) (M.tail c) + M.walkDist g (M.tail c) (M.tail (κ1 μ)) =
      M.walkDist g (M.tail (κ0 μ)) (M.tail (κ1 μ)) := by
  rcases hiμ.lt_or_eq with hlt | rfl
  · -- the walk read backwards, from `κ1 i` through `c` to `κ0 i`
    have h1' := h2.reverse
    have h2' := h1.reverse
    have hsum : ((M.reverseCycle P₂ ++ M.reverseCycle P₁).map g).sum = ((P₁ ++ P₂).map g).sum := by
      simp only [List.map_append, List.sum_append, sum_map_reverseCycle g hg]
      exact add_comm _ _
    have hfin' : ((M.reverseCycle P₂ ++ M.reverseCycle P₁).map g).sum ≠ ⊤ := hsum ▸ hfin
    have hP' : ∀ q, M.IsWalk (M.tail (κ1 i)) q (M.tail (κ0 i)) →
        ((M.reverseCycle P₂ ++ M.reverseCycle P₁).map g).sum ≤ (q.map g).sum := fun q hq => by
      rw [hsum, ← sum_map_reverseCycle g hg q]
      exact hP _ hq.reverse
    have key : ∀ {l'}, M.FaceDrawn l' → [κ1 μ, κ1 i, κ0 i, κ0 μ, c] <+ l' →
        M.walkDist g (M.tail (κ0 μ)) (M.tail c) + M.walkDist g (M.tail c) (M.tail (κ1 μ)) =
          M.walkDist g (M.tail (κ0 μ)) (M.tail (κ1 μ)) := fun hl' hs => by
      have := hl'.dist_through g hg hs h1' h2' hfin' hP'
      rw [walkDist_comm g hg (M.tail (κ1 μ)) (M.tail c),
        walkDist_comm g hg (M.tail c) (M.tail (κ0 μ)),
        walkDist_comm g hg (M.tail (κ1 μ)) (M.tail (κ0 μ)), add_comm] at this
      exact this
    have s1 : [κ1 μ, κ1 i] <+ (cornerSeg κ1 ya yb).reverse :=
      (sublist_cornerSeg κ1 (l := [i, μ]) (by simp; omega) (by simp; omega)).reverse
    rcases hc with rfl | hc | rfl
    · rcases hμx.lt_or_eq with hxlt | rfl
      · have s0 : [κ0 i, κ0 μ, κ0 xb] <+ cornerSeg κ0 xa xb :=
          sublist_cornerSeg κ0 (l := [i, μ, xb]) (by simp; omega) (by simp; omega)
        have hs : ([κ0 i, κ0 μ, κ0 xb] ++ [κ1 μ, κ1 i]) <+
            cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La :=
          ((s0.append (List.nil_sublist Lb)).append s1).append (List.nil_sublist La)
        obtain ⟨l', hr, hs'⟩ := exists_isRotated_sublist hs
        exact key (h.of_isRotated hr) hs'
      · rw [walkDist_self, zero_add]
    · have s0 : [κ0 i, κ0 μ] <+ cornerSeg κ0 xa xb :=
        sublist_cornerSeg κ0 (l := [i, μ]) (by simp; omega) (by simp; omega)
      have hs : ([κ0 i, κ0 μ, c] ++ [κ1 μ, κ1 i]) <+
          cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La :=
        ((s0.append (List.singleton_sublist.2 hc)).append s1).append (List.nil_sublist La)
      obtain ⟨l', hr, hs'⟩ := exists_isRotated_sublist hs
      exact key (h.of_isRotated hr) hs'
    · rcases hμy.lt_or_eq with hylt | rfl
      · have s0 : [κ0 i, κ0 μ] <+ cornerSeg κ0 xa xb :=
          sublist_cornerSeg κ0 (l := [i, μ]) (by simp; omega) (by simp; omega)
        have s1' : [κ1 yb, κ1 μ, κ1 i] <+ (cornerSeg κ1 ya yb).reverse :=
          (sublist_cornerSeg κ1 (l := [i, μ, yb]) (by simp; omega) (by simp; omega)).reverse
        have hs : ([κ0 i, κ0 μ, κ1 yb] ++ [κ1 μ, κ1 i]) <+
            cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La :=
          ((s0.append (List.nil_sublist Lb)).append s1').append (List.nil_sublist La)
        obtain ⟨l', hr, hs'⟩ := exists_isRotated_sublist hs
        exact key (h.of_isRotated hr) hs'
      · rw [walkDist_self, add_zero]
  · exact dist_through_ends g h1 h2 hP

end RotSystem

end SsspFlow
