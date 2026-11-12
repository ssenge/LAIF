import GraphClasses.Chain

/-!
# The hard family

Vertices `0, …, n - 1` with creation sequence `0, 1, 0, 1, …`: an odd vertex `j` is adjacent to all `i < j`, and an
even vertex to none of them. So two vertices are adjacent iff the larger one is odd.
-/

open Finset

namespace GraphClasses

/-- The undeleted graph: `u ~ v` iff the larger of them is odd. -/
def hardG (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u.val ≠ v.val ∧ max u.val v.val % 2 = 1
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [max_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- The graph with the single edge `ij` deleted. -/
def hardDel (n : ℕ) (i j : Fin n) : SimpleGraph (Fin n) := (hardG n).deleteEdges {s(i, j)}

theorem hardDel_adj {n : ℕ} {i j u v : Fin n} :
    (hardDel n i j).Adj u v ↔ (hardG n).Adj u v ∧ ¬ ((u = i ∧ v = j) ∨ (u = j ∧ v = i)) := by
  simp [hardDel, SimpleGraph.deleteEdges_adj, Sym2.eq_iff]

/-- The undeleted graph has no alternating 4-cycle: the largest of the four vertices would be both odd and even. -/
theorem hardG_noAlt (n : ℕ) : NoAlt (hardG n) := by
  rintro a b c d ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7, h8⟩
  have h9 : a.val ≠ c.val := fun e => h7 (Fin.ext e)
  have h10 : b.val ≠ d.val := fun e => h8 (Fin.ext e)
  have h5' : max a.val c.val % 2 ≠ 1 := fun e => h5 ⟨h9, e⟩
  have h6' : max b.val d.val % 2 ≠ 1 := fun e => h6 ⟨h10, e⟩
  rcases le_total a.val b.val with e1 | e1 <;> rcases le_total c.val d.val with e2 | e2 <;>
    rcases le_total a.val c.val with e3 | e3 <;> rcases le_total b.val d.val with e4 | e4 <;>
    simp only [max_eq_left, max_eq_right, e1, e2, e3, e4] at h2 h4 h5' h6' <;> omega

/-- The undeleted graph is a threshold graph, by the characterization. -/
theorem hardG_threshold (n : ℕ) [DecidableRel (hardG n).Adj] : IsThreshold (hardG n) :=
  (threshold_iff_noAlt _).2 (hardG_noAlt n)

/-- **Hard family.** For even `i` and odd `j ≥ i + 3`, deleting `ij` creates the alternating 4-cycle
`j, i + 2, i, i + 1`: `j ~ i + 2`, `i ~ i + 1`, `j ≁ i`, `i + 2 ≁ i + 1`. -/
theorem hardDel_alt {n : ℕ} (i j : Fin n) (hi : i.val % 2 = 0) (hj : j.val % 2 = 1) (hij : i.val + 3 ≤ j.val) :
    AltCycle (hardDel n i j) j ⟨i.val + 2, by omega⟩ i ⟨i.val + 1, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hardDel_adj]
    refine ⟨⟨by simp only; omega, ?_⟩, ?_⟩
    · simp only
      rw [max_eq_left (by omega)]
      exact hj
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · rw [h1] at hij; omega
      · have := congrArg Fin.val h2
        simp only at this
        omega
  · rw [hardDel_adj]
    refine ⟨⟨by simp only; omega, ?_⟩, ?_⟩
    · simp only
      rw [max_eq_right (by omega)]
      omega
    · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · have := congrArg Fin.val h2
        simp only at this
        omega
      · rw [h1] at hij; omega
  · rw [hardDel_adj]
    rintro ⟨_, h⟩
    exact h (Or.inr ⟨rfl, rfl⟩)
  · rw [hardDel_adj]
    rintro ⟨⟨_, h⟩, _⟩
    simp only at h
    rw [max_eq_left (by omega)] at h
    omega
  · intro h
    rw [h] at hij
    omega
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega

/-- The pairs of the hard family. -/
def hardPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter fun e => e.1.val % 2 = 0 ∧ e.2.val % 2 = 1 ∧ e.1.val + 3 ≤ e.2.val

/-- There are at most `n²` pairs. -/
theorem hardPairs_card_le (n : ℕ) : (hardPairs n).card ≤ n ^ 2 := by
  calc (hardPairs n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_filter_le _ _
    _ = n ^ 2 := by simp [sq]

/-- There are at least `(n / 4)²` pairs: with `k = n / 4`, take `i = 2 s` and `j = 2 (k + t) + 1` for `s, t < k`. -/
theorem hardPairs_card_ge (n : ℕ) : (n / 4) ^ 2 ≤ (hardPairs n).card := by
  set k := n / 4 with hk
  have hk4 : 4 * k ≤ n := by omega
  let f : Fin k × Fin k → Fin n × Fin n := fun e =>
    (⟨2 * e.1.val, by have := e.1.isLt; omega⟩, ⟨2 * (k + e.2.val) + 1, by have := e.2.isLt; omega⟩)
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [f, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : a = c := Fin.ext (by omega)
    have e2 : b = d := Fin.ext (by omega)
    rw [e1, e2]
  have hmaps : ∀ e ∈ (univ : Finset (Fin k × Fin k)), f e ∈ hardPairs n := by
    rintro ⟨a, b⟩ _
    simp only [hardPairs, mem_filter, mem_univ, true_and, f]
    have := a.isLt
    omega
  have := card_le_card_of_injOn f hmaps (hinj.injOn)
  simpa [sq] using this

/-- **The count.** `Θ(n²)`: for `n ≥ 4`, between `n² / 64` and `n²`. -/
theorem hardPairs_theta {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 64 * (hardPairs n).card ∧ (hardPairs n).card ≤ n ^ 2 := by
  refine ⟨?_, hardPairs_card_le n⟩
  have h1 := hardPairs_card_ge n
  have h2 : n ≤ 8 * (n / 4) := by omega
  calc n ^ 2 ≤ (8 * (n / 4)) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 64 * (n / 4) ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h1

/-! ## The bipartite part: nested matrices and chain graphs -/

/-- The matrix between even rows and odd columns: `1` iff `i < j`. -/
def hardMat (n : ℕ) (i j : Fin n) : Bool := decide (i.val < j.val)

/-- The matrix with the entry `(i, j)` set to `0`. -/
def hardMatDel (n : ℕ) (i j : Fin n) (u v : Fin n) : Bool := hardMat n u v && !(decide (u = i) && decide (v = j))

/-- The even rows. -/
def evens (n : ℕ) : Finset (Fin n) := univ.filter fun u => u.val % 2 = 0

/-- The odd columns. -/
def odds (n : ℕ) : Finset (Fin n) := univ.filter fun u => u.val % 2 = 1

/-- The undeleted matrix is nested on even rows and odd columns. -/
theorem hardMat_nested (n : ℕ) : NestedOn (hardMat n) (evens n) (odds n) := by
  intro r _ s _
  rcases le_total s.val r.val with h | h
  · left
    intro c _ hm
    simp only [hardMat, decide_eq_true_eq] at hm ⊢
    omega
  · right
    intro c _ hm
    simp only [hardMat, decide_eq_true_eq] at hm ⊢
    omega

/-- Deleting a pair of the hard family makes the block not nested: rows `i, i + 2`, columns `i + 1, j`. -/
theorem hardMatDel_not_nested {n : ℕ} (i j : Fin n) (hi : i.val % 2 = 0) (hj : j.val % 2 = 1)
    (hij : i.val + 3 ≤ j.val) : ¬ NestedOn (hardMatDel n i j) (evens n) (odds n) := by
  intro h
  let i2 : Fin n := ⟨i.val + 2, by omega⟩
  let i1 : Fin n := ⟨i.val + 1, by omega⟩
  have hi2 : i2 ∈ evens n := mem_filter.2 ⟨mem_univ _, by simp only [i2]; omega⟩
  have hi0 : i ∈ evens n := mem_filter.2 ⟨mem_univ _, hi⟩
  have hc1 : i1 ∈ odds n := mem_filter.2 ⟨mem_univ _, by simp only [i1]; omega⟩
  have hcj : j ∈ odds n := mem_filter.2 ⟨mem_univ _, hj⟩
  have hne1 : i1 ≠ j := by
    intro e
    have := congrArg Fin.val e
    simp only [i1] at this
    omega
  have hne2 : i2 ≠ i := by
    intro e
    have := congrArg Fin.val e
    simp only [i2] at this
    omega
  rcases h i hi0 i2 hi2 with g | g
  · have := g i1 hc1 (by simp [hardMatDel, hardMat, i1, hne1])
    simp [hardMatDel, hardMat, i1, i2] at this
  · have := g j hcj (by
      simp only [hardMatDel, hardMat, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not, i2]
      exact ⟨by omega, Or.inl hne2⟩)
    simp [hardMatDel] at this

/-- The bipartite part of the hard graph, between odd and even vertices. -/
def hardChain (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u.val % 2 ≠ v.val % 2 ∧ max u.val v.val % 2 = 1
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [max_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- The undeleted bipartite part is a chain graph. -/
theorem hardChain_isChain (n : ℕ) : IsChain (hardChain n) := by
  refine ⟨fun u => decide (u.val % 2 = 1), ?_, ?_⟩
  · intro u v h hs
    have h1 := h.1
    simp only [decide_eq_decide] at hs
    omega
  · intro u v hu hv
    simp only [decide_eq_false_iff_not] at hu hv
    rcases le_total v.val u.val with h | h
    · left
      rintro t ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rcases le_total v.val t.val with e1 | e1 <;> rcases le_total u.val t.val with e2 | e2 <;>
        simp only [max_eq_left, max_eq_right, e1, e2] at h2 ⊢ <;> omega
    · right
      rintro t ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rcases le_total v.val t.val with e1 | e1 <;> rcases le_total u.val t.val with e2 | e2 <;>
        simp only [max_eq_left, max_eq_right, e1, e2] at h2 ⊢ <;> omega

/-- Deleting a pair of the hard family makes the bipartite part not a chain graph: `i, i + 1` and `i + 2, j` form an
induced `2K₂`. -/
theorem hardChain_del_not_chain {n : ℕ} (i j : Fin n) (hi : i.val % 2 = 0) (hj : j.val % 2 = 1)
    (hij : i.val + 3 ≤ j.val) : ¬ IsChain ((hardChain n).deleteEdges {s(i, j)}) := by
  intro h
  let i2 : Fin n := ⟨i.val + 2, by omega⟩
  let i1 : Fin n := ⟨i.val + 1, by omega⟩
  have hadj : ∀ u v : Fin n, ((hardChain n).deleteEdges {s(i, j)}).Adj u v ↔
      (hardChain n).Adj u v ∧ ¬ ((u = i ∧ v = j) ∨ (u = j ∧ v = i)) := by
    intro u v
    simp [SimpleGraph.deleteEdges_adj, Sym2.eq_iff]
  have hval : ∀ {a b : Fin n}, a = b → a.val = b.val := fun e => congrArg Fin.val e
  refine h.no_two_K2 (a := i) (b := i1) (c := i2) (d := j) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hadj]
    refine ⟨⟨by simp only [i1]; omega, ?_⟩, ?_⟩
    · simp only [i1]
      rw [max_eq_right (by omega)]
      omega
    · rintro (⟨_, e⟩ | ⟨e, _⟩)
      · have := hval e
        simp only [i1] at this
        omega
      · have := hval e
        omega
  · rw [hadj]
    refine ⟨⟨by simp only [i2]; omega, ?_⟩, ?_⟩
    · simp only [i2]
      rw [max_eq_right (by omega)]
      exact hj
    · rintro (⟨e, _⟩ | ⟨e, _⟩)
      · have := hval e
        simp only [i2] at this
        omega
      · have := hval e
        simp only [i2] at this
        omega
  · rw [hadj]
    rintro ⟨⟨h1, _⟩, _⟩
    simp only [i2] at h1
    omega
  · rw [hadj]
    rintro ⟨_, e⟩
    exact e (Or.inl ⟨rfl, rfl⟩)
  · rw [hadj]
    rintro ⟨⟨_, h2⟩, _⟩
    simp only [i1, i2] at h2
    rw [max_eq_right (by omega)] at h2
    omega
  · rw [hadj]
    rintro ⟨⟨h1, _⟩, _⟩
    simp only [i1] at h1
    omega

end GraphClasses
