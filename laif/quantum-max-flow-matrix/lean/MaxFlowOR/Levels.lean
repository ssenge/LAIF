import Mathlib

/-!
# Level sizes and the cut between two consecutive levels

Breadth-first levels of a residual graph with distance at least `d` from `s` to `t` give `d + 1`
nonempty levels. The first lemma shows that some two consecutive levels are both small; the second
bounds the residual capacity of the cut between levels `≤ i` and levels `≥ i + 1` by the product of
the two level sizes, when every residual arc rises by at most one level and every ordered pair
carries residual capacity at most `2`.
-/

namespace MaxFlowOR

/-- Among levels `a 0, ..., a d` of total size at most `n`, some two consecutive levels both have
`d · size ≤ 2 n`. -/
theorem exists_small_pair (a : ℕ → ℕ) (d n : ℕ) (hd : 1 ≤ d)
    (hsum : ∑ i ∈ Finset.range (d + 1), a i ≤ n) :
    ∃ i < d, d * a i ≤ 2 * n ∧ d * a (i + 1) ≤ 2 * n := by
  classical
  by_contra hno
  push Not at hno
  set B := (Finset.range (d + 1)).filter (fun i => 2 * n < d * a i) with hB
  -- every index below `d` lies in `B` or has its successor in `B`
  have hcover : Finset.range d ⊆ B ∪ B.image (fun i => i - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases h : d * a i ≤ 2 * n
    · have h2 := hno i hi' h
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i + 1, ?_, by simp⟩)
      simp [hB]; omega
    · exact Finset.mem_union_left _ (by simp [hB]; omega)
  have hcard : d ≤ 2 * B.card := by
    have := Finset.card_le_card hcover
    have h2 := Finset.card_union_le B (B.image (fun i => i - 1))
    have h3 := Finset.card_image_le (s := B) (f := fun i => i - 1)
    simp at this; omega
  have hne : B.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B with h | h
    · rw [h] at hcard; simp at hcard; omega
    · exact h
  -- sum over `B` of `d · a i` exceeds `2 n |B| ≥ d n`
  have hlow : 2 * n * B.card < ∑ i ∈ B, d * a i := by
    have : ∑ _i ∈ B, 2 * n < ∑ i ∈ B, d * a i :=
      Finset.sum_lt_sum_of_nonempty hne (fun i hi => (Finset.mem_filter.mp hi).2)
    simpa [mul_comm] using this
  have hup : ∑ i ∈ B, d * a i ≤ d * n := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _
      (le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) hsum)
  have : d * n ≤ 2 * n * B.card := by nlinarith
  omega

/-- The residual capacity leaving the set of levels `≤ i` is carried by pairs from level `i` to level
`i + 1`, so it is at most `2 · |level i| · |level (i+1)|`. -/
theorem cut_le_levels {V : Type*} [Fintype V] [DecidableEq V] (lev : V → ℕ) (c : V → V → ℕ)
    (hc : ∀ u v, c u v ≤ 2) (hrise : ∀ u v, 0 < c u v → lev v ≤ lev u + 1) (i : ℕ) :
    ∑ p ∈ (Finset.univ.filter (fun u => lev u ≤ i)) ×ˢ (Finset.univ.filter (fun v => ¬ lev v ≤ i)),
        c p.1 p.2
      ≤ 2 * ((Finset.univ.filter (fun u => lev u = i)).card *
          (Finset.univ.filter (fun v => lev v = i + 1)).card) := by
  classical
  set L := Finset.univ.filter (fun u => lev u = i)
  set L' := Finset.univ.filter (fun v => lev v = i + 1)
  have hsub : L ×ˢ L' ⊆ (Finset.univ.filter (fun u => lev u ≤ i)) ×ˢ
      (Finset.univ.filter (fun v => ¬ lev v ≤ i)) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, L, L'] at hp ⊢
    omega
  rw [← Finset.sum_subset hsub (by
    intro p hp hnot
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, L, L'] at hp hnot
    by_contra h
    have := hrise p.1 p.2 (Nat.pos_of_ne_zero h)
    omega)]
  calc ∑ p ∈ L ×ˢ L', c p.1 p.2 ≤ ∑ _p ∈ L ×ˢ L', 2 := Finset.sum_le_sum (fun p _ => hc p.1 p.2)
    _ = 2 * (L.card * L'.card) := by simp [Finset.card_product, mul_comm]

/-- With both levels of size at most `2n/d`, the cut has capacity at most `8 n² / d²`. -/
theorem cut_bound (d n x y C : ℕ) (hx : d * x ≤ 2 * n) (hy : d * y ≤ 2 * n) (hC : C ≤ 2 * (x * y)) :
    d ^ 2 * C ≤ 8 * n ^ 2 := by
  have h1 : (d * x) * (d * y) ≤ (2 * n) * (2 * n) := Nat.mul_le_mul hx hy
  nlinarith

end MaxFlowOR
