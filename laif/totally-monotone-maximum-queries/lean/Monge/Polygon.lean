import Monge.TotallyMonotone
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Distances between arcs of a convex polygon (Section 4 of the README, the monotonicity part)

The quadrilateral inequality follows from the triangle inequality at the crossing point. Crossing is
then derived from convexity, stated through orientations. The distance matrix between two arcs
has the reverse quadrangle inequality, and squared distances are totally monotone.
-/

namespace Monge

/-- The plane with its usual distance. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- **Quadrilateral inequality.** If the segments `a b` and `a' b'` share a point, the sum of their
lengths is at least the sum of the two other pairings. This holds in any normed space. -/
theorem quadrilateral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a a' b b' P : E}
    (h : P ∈ segment ℝ a b) (h' : P ∈ segment ℝ a' b') :
    dist a b' + dist a' b ≤ dist a b + dist a' b' := by
  have h1 := dist_add_dist_of_mem_segment h
  have h2 := dist_add_dist_of_mem_segment h'
  have h3 := dist_triangle a P b'
  have h4 := dist_triangle a' P b
  linarith

/-- The reverse quadrangle inequality for two families of points whose segments cross. Crossing is a hypothesis here. -/
theorem inverseMonge_of_crossing {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LT ι]
    [LT κ] {a : ι → E} {b : κ → E}
    (hcross : ∀ ⦃i i' : ι⦄ ⦃j j' : κ⦄, i < i' → j < j' →
      ∃ P, P ∈ segment ℝ (a i) (b j) ∧ P ∈ segment ℝ (a i') (b j')) :
    InverseMonge fun i j => dist (a i) (b j) := by
  intro i i' j j' hi hj
  obtain ⟨P, h1, h2⟩ := hcross hi hj
  exact quadrilateral h1 h2

/-- Twice the signed area of the triangle `p q r`. It is positive when `p q r` turn left. -/
def orient (p q r : Pt) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- Four points in counterclockwise convex position: the diagonals `w y` and `x z` cross. -/
theorem diagonals_cross {w x y z : Pt} (h1 : 0 < orient w x y) (h2 : 0 < orient w y z)
    (h3 : 0 < orient x y z) (h4 : 0 < orient w x z) :
    ∃ P, P ∈ segment ℝ w y ∧ P ∈ segment ℝ x z := by
  have harea : orient w x y + orient w y z = orient x y z + orient w x z := by
    unfold orient
    ring
  have hS : orient x y z + orient w x z ≠ 0 := by positivity
  have hS' : orient w x y + orient w y z ≠ 0 := by positivity
  refine ⟨(orient x y z / (orient x y z + orient w x z)) • w +
      (orient w x z / (orient x y z + orient w x z)) • y, ?_, ?_⟩
  · exact ⟨_, _, by positivity, by positivity, by field_simp, rfl⟩
  · refine ⟨orient w y z / (orient w x y + orient w y z),
      orient w x y / (orient w x y + orient w y z), by positivity, by positivity,
      by field_simp; ring, ?_⟩
    rw [harea]
    ext i
    fin_cases i <;>
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
        Fin.isValue]
      field_simp
      unfold orient
      ring

/-- Vertices `v_0, …, v_{n-1}` of a strictly convex polygon in counterclockwise order: every ordered
triple of vertices turns left. -/
def StrictlyConvexCCW {n : ℕ} (v : Fin n → Pt) : Prop :=
  ∀ ⦃i j k : Fin n⦄, i < j → j < k → 0 < orient (v i) (v j) (v k)

/-- **Arcs.** Take two increasing index sequences of a strictly convex polygon, the first one
entirely before the second. This covers two consecutive arcs. The distance matrix has the reverse quadrangle inequality,
with crossing derived from convexity. -/
theorem arc_inverseMonge {n s t : ℕ} {v : Fin n → Pt} (hv : StrictlyConvexCCW v) {a : Fin s → Fin n}
    {b : Fin t → Fin n} (ha : StrictMono a) (hb : StrictMono b) (hab : ∀ i j, a i < b j) :
    InverseMonge fun i j => dist (v (a i)) (v (b j)) := by
  apply inverseMonge_of_crossing (a := fun i => v (a i)) (b := fun j => v (b j))
  intro i i' j j' hi hj
  have h1 := ha hi
  have h2 := hb hj
  have h3 := hab i' j
  exact diagonals_cross (hv h1 h3) (hv (h1.trans h3) h2) (hv h3 h2) (hv h1 (h3.trans h2))

/-- Distances between arcs are totally monotone. -/
theorem arc_totallyMonotone {n s t : ℕ} {v : Fin n → Pt} (hv : StrictlyConvexCCW v)
    {a : Fin s → Fin n} {b : Fin t → Fin n} (ha : StrictMono a) (hb : StrictMono b)
    (hab : ∀ i j, a i < b j) : TotallyMonotone fun i j => dist (v (a i)) (v (b j)) :=
  (arc_inverseMonge hv ha hb hab).totallyMonotone

/-- Squared distances between arcs are totally monotone. -/
theorem arc_sq_totallyMonotone {n s t : ℕ} {v : Fin n → Pt} (hv : StrictlyConvexCCW v)
    {a : Fin s → Fin n} {b : Fin t → Fin n} (ha : StrictMono a) (hb : StrictMono b)
    (hab : ∀ i j, a i < b j) : TotallyMonotone fun i j => dist (v (a i)) (v (b j)) ^ 2 :=
  (arc_totallyMonotone hv ha hb hab).sq fun _ _ => dist_nonneg

/-- The squared distance as a polynomial in the coordinates, so it is an integer on integer
coordinates. -/
theorem dist_sq_eq (p q : Pt) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

/-- A concrete instance: points on a parabola are in strictly convex counterclockwise position, so
the convexity hypothesis is satisfiable for every `n`. -/
noncomputable def parabola {n : ℕ} (i : Fin n) : Pt := !₂[(i : ℝ), (i : ℝ) ^ 2]

theorem parabola_convex {n : ℕ} : StrictlyConvexCCW (parabola (n := n)) := by
  intro i j k hij hjk
  have h1 : (0 : ℝ) < (j : ℝ) - i := sub_pos.mpr (by exact_mod_cast hij)
  have h2 : (0 : ℝ) < (k : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjk)
  have h3 : (0 : ℝ) < (k : ℝ) - i := by linarith
  have : orient (parabola i) (parabola j) (parabola k) =
      ((j : ℝ) - i) * ((k : ℝ) - j) * ((k : ℝ) - i) := by
    simp only [orient, parabola]
    simp
    ring
  rw [this]
  positivity

end Monge
