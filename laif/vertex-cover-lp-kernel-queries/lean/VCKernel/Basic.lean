import Mathlib

/-!
# Vertex cover with a parameter: the combinatorial steps

The bipartite double cover H of a graph on V has the vertices v_L and v_R, and v_L w_R is an edge of H
when v w is an edge of the graph. A set C of vertices of H is given by the two predicates `L v`
(v_L ∈ C) and `R v` (v_R ∈ C), and `cnt L R v ∈ {0, 1, 2}` is twice the LP value x_v = |C ∩ {v_L, v_R}|/2.

* `cnt_feasible`: if C covers H, then x_v + x_w ≥ 1 on every edge of the graph.
* `cover_of_kernel`: if S covers the edges inside V_{1/2}, then V_1 ∪ S covers the graph.
* `search_cost`: the second phase of the alternating search costs at most √2 · p^{3/2}.
-/

namespace VCKernel

variable {V : Type*}

/-- Twice the LP value of v: the number of copies of v in the cover C of the double cover. -/
def cnt (L R : V → Prop) [DecidablePred L] [DecidablePred R] (v : V) : ℕ :=
  (if L v then 1 else 0) + (if R v then 1 else 0)

theorem cnt_le_two (L R : V → Prop) [DecidablePred L] [DecidablePred R] (v : V) :
    cnt L R v ≤ 2 := by
  unfold cnt; split_ifs <;> omega

/-- A cover of the double cover gives a feasible point of the vertex cover LP. -/
theorem cnt_feasible (adj : V → V → Prop) (hsymm : ∀ v w, adj v w → adj w v)
    (L R : V → Prop) [DecidablePred L] [DecidablePred R]
    (hC : ∀ v w, adj v w → L v ∨ R w) {v w : V} (h : adj v w) :
    2 ≤ cnt L R v + cnt L R w := by
  have h1 := hC v w h
  have h2 := hC w v (hsymm v w h)
  unfold cnt
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2] <;> split_ifs <;> omega

/-- If S covers every edge with both ends in V_{1/2}, then V_1 ∪ S is a vertex cover. -/
theorem cover_of_kernel (adj : V → V → Prop) (hsymm : ∀ v w, adj v w → adj w v)
    (L R : V → Prop) [DecidablePred L] [DecidablePred R]
    (hC : ∀ v w, adj v w → L v ∨ R w) (S : V → Prop)
    (hS : ∀ v w, adj v w → cnt L R v = 1 → cnt L R w = 1 → S v ∨ S w) {v w : V} (h : adj v w) :
    (cnt L R v = 2 ∨ S v) ∨ (cnt L R w = 2 ∨ S w) := by
  have hf := cnt_feasible adj hsymm L R hC h
  have hv := cnt_le_two L R v
  have hw := cnt_le_two L R w
  by_cases a : cnt L R v = 2
  · exact Or.inl (Or.inl a)
  by_cases b : cnt L R w = 2
  · exact Or.inr (Or.inl b)
  rcases hS v w h (by omega) (by omega) with s | s
  · exact Or.inl (Or.inr s)
  · exact Or.inr (Or.inr s)

theorem sum_sqrt_le {ι : Type*} (I : Finset ι) (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    ∑ i ∈ I, Real.sqrt (l i) ≤ Real.sqrt (I.card * ∑ i ∈ I, l i) := by
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => Real.sqrt (l i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc (∑ i ∈ I, Real.sqrt (l i)) ^ 2 ≤ I.card * ∑ i ∈ I, Real.sqrt (l i) ^ 2 := hcs
    _ = I.card * ∑ i ∈ I, l i := by
      congr 1; exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hl i))

/-- Second phase of the search: at most p searching vertices, at most p vertices added in total,
each search over a set of at most p vertices. -/
theorem search_cost {ι : Type*} (I : Finset ι) (t : ι → ℕ) (p : ℕ) (hI : I.card ≤ p)
    (ht : ∑ i ∈ I, t i ≤ p) :
    ∑ i ∈ I, Real.sqrt (p * ((t i : ℝ) + 1)) ≤ Real.sqrt 2 * p * Real.sqrt p := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have h1 := sum_sqrt_le I (fun i => (p : ℝ) * ((t i : ℝ) + 1))
    (fun i => mul_nonneg hp (by positivity))
  have hsum : ∑ i ∈ I, (p : ℝ) * ((t i : ℝ) + 1) ≤ 2 * (p : ℝ) * p := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have a : (∑ i ∈ I, (t i : ℝ)) ≤ p := by exact_mod_cast ht
    have b : (I.card : ℝ) ≤ p := by exact_mod_cast hI
    nlinarith
  have hc : (I.card : ℝ) ≤ p := by exact_mod_cast hI
  have h2 : (I.card : ℝ) * ∑ i ∈ I, (p : ℝ) * ((t i : ℝ) + 1) ≤ 2 * (p : ℝ) * p * p := by
    have hs0 : 0 ≤ ∑ i ∈ I, (p : ℝ) * ((t i : ℝ) + 1) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg hp (by positivity))
    calc (I.card : ℝ) * ∑ i ∈ I, (p : ℝ) * ((t i : ℝ) + 1)
        ≤ p * ∑ i ∈ I, (p : ℝ) * ((t i : ℝ) + 1) := mul_le_mul_of_nonneg_right hc hs0
      _ ≤ p * (2 * p * p) := mul_le_mul_of_nonneg_left hsum hp
      _ = 2 * (p : ℝ) * p * p := by ring
  calc ∑ i ∈ I, Real.sqrt (p * ((t i : ℝ) + 1))
      ≤ Real.sqrt (I.card * ∑ i ∈ I, (p : ℝ) * ((t i : ℝ) + 1)) := h1
    _ ≤ Real.sqrt (2 * (p : ℝ) * p * p) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt 2 * p * Real.sqrt p := by
      rw [show (2 : ℝ) * p * p * p = (2 * p) * (p * p) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_mul_self hp, Real.sqrt_mul (by norm_num)]
      ring

end VCKernel
