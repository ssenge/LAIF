import Arborescence.AlgoCorrect

/-!
# An exact classical TopK, and a run of the algorithm

`exactTopK vs` reads all items and returns, by increasing `f`, the cheapest entry of each type, cut at the budget.
`exactTopK_correct` proves that it satisfies `IsTopK`, so the hypothesis `Oracle.Correct` of `solve_correct` can be
satisfied. With this oracle `solve` is an ordinary executable classical algorithm, which the `#guard`s below run.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The first entry of each type in a list. -/
def firstPer : List (V × V) → List (V × V)
  | [] => []
  | a :: l => a :: (firstPer l).filter fun b => decide (b.1 ≠ a.1)

theorem firstPer_sublist : ∀ l : List (V × V), (firstPer l).Sublist l
  | [] => .refl _
  | a :: l => (List.filter_sublist.trans (firstPer_sublist l)).cons₂ a

theorem firstPer_distinct : ∀ l : List (V × V), (firstPer l).Pairwise fun a b => a.1 ≠ b.1
  | [] => .nil
  | a :: l => by
    simp only [firstPer]
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, (firstPer_distinct l).filter _⟩
    exact (by simpa using (List.mem_filter.mp hb).2 : b.1 ≠ a.1).symm

theorem firstPer_min (f : V × V → WithTop ℤ) : ∀ l : List (V × V), l.Pairwise (fun a b => f a ≤ f b) →
    ∀ j ∈ l, ∃ i ∈ firstPer l, i.1 = j.1 ∧ f i ≤ f j
  | [], _, j, hj => by simp at hj
  | a :: l, hs, j, hj => by
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨j, by simp [firstPer], rfl, le_rfl⟩
    · obtain ⟨i, hi, hty, hle⟩ := firstPer_min f l hs.2 j hj
      by_cases h : i.1 = a.1
      · exact ⟨a, by simp [firstPer], h.symm.trans hty, hs.1 j hj⟩
      · exact ⟨i, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hi, by simpa using h⟩), hty, hle⟩

/-- An exact TopK: `vs` lists the vertices. -/
def exactTopK (vs : List V) : Oracle V := fun items f K =>
  (firstPer (((vs.flatMap fun u => vs.map fun v => (u, v)).filter fun e => decide (e ∈ items)).insertionSort
    fun a b => f a ≤ f b)).take K

/-- **The exact oracle satisfies the specification**, so `Oracle.Correct` is satisfiable. -/
theorem exactTopK_correct {vs : List V} (hall : ∀ v, v ∈ vs) : (exactTopK vs).Correct := by
  intro items f K
  set l := ((vs.flatMap fun u => vs.map fun v => (u, v)).filter fun e => decide (e ∈ items)).insertionSort
    fun a b => f a ≤ f b with hl
  have hO : exactTopK vs items f K = (firstPer l).take K := rfl
  have hmem : ∀ e, e ∈ l ↔ e ∈ items := fun e => by
    rw [hl, (List.perm_insertionSort _ _).mem_iff, List.mem_filter]
    simp [List.mem_flatMap, hall]
  haveI : Std.Total fun a b : V × V => f a ≤ f b := ⟨fun a b => le_total _ _⟩
  haveI : IsTrans (V × V) fun a b => f a ≤ f b := ⟨fun a b c => le_trans⟩
  have hsort : l.Pairwise fun a b => f a ≤ f b := List.pairwise_insertionSort _ _
  have hsub := firstPer_sublist l
  have hdist : ((firstPer l).map Prod.fst).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact firstPer_distinct l
  have hnd : (firstPer l).Nodup := List.Nodup.of_map _ hdist
  have htake := List.take_sublist K (firstPer l)
  have hinj := List.inj_on_of_nodup_map hdist
  rw [hO]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    exact (hmem e).mp (hsub.subset (htake.subset (List.mem_toFinset.mp he)))
  · rw [List.toFinset_card_of_nodup (hnd.sublist htake), List.length_take]
    congr 1
    have himg : ((firstPer l).map Prod.fst).toFinset = items.image Prod.fst := by
      ext u
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨e, (hmem e).mp (hsub.subset he), rfl⟩
      · rintro ⟨e, he, rfl⟩
        obtain ⟨i, hi, hty, _⟩ := firstPer_min f l hsort e ((hmem e).mpr he)
        exact ⟨i, hi, hty⟩
    rw [← himg, List.toFinset_card_of_nodup hdist, List.length_map]
  · intro a ha b hb hab
    exact hinj (htake.subset (List.mem_toFinset.mp ha)) (htake.subset (List.mem_toFinset.mp hb)) hab
  · intro j hj hjI i hi hlt
    obtain ⟨m, hm, hty, hle⟩ := firstPer_min f l hsort j ((hmem j).mpr hj)
    refine ⟨m, ?_, hty, hle⟩
    rw [← List.take_append_drop K (firstPer l), List.mem_append] at hm
    rcases hm with hm | hm
    · exact List.mem_toFinset.mpr hm
    · exfalso
      have hsort2 := hsort.sublist hsub
      rw [← List.take_append_drop K (firstPer l), List.pairwise_append] at hsort2
      have := hsort2.2.2 i (List.mem_toFinset.mp hi) m hm
      exact absurd (lt_of_le_of_lt (this.trans hle) hlt) (lt_irrefl _)

/-! ## A run -/

/-- The parent list and the number of builds, for a graph on `Fin n`. -/
def demo {n : ℕ} (g : Graph (Fin n)) : Option (List (Fin n)) × ℕ :=
  let vs := List.finRange n
  let r := solve (exactTopK vs) g vs
  (r.1.map fun p => vs.map p, r.2.length)

/-- A graph from a list of weighted edges. -/
def ofEdges {n : ℕ} (r : Fin n) (es : List (Fin n × Fin n × ℤ)) : Graph (Fin n) where
  adj u v := es.any fun e => e.1 = u && e.2.1 = v
  w u v := ((es.find? fun e => e.1 = u && e.2.1 = v).map fun e => e.2.2).getD 0
  root := r

/-- The cycle `1 → 2 → 3 → 1` has the cheapest edges, but the optimum breaks it: cost 11, against 14 for the
arborescence that enters at `1`. -/
def exampleCycle : Graph (Fin 5) :=
  ofEdges 0 [(0, 1, 10), (1, 2, 1), (2, 3, 1), (3, 1, 1), (0, 3, 8), (3, 4, 2), (4, 2, 0)]

#eval demo exampleCycle
#guard (demo exampleCycle).1 = some [0, 3, 4, 0, 3]

-- Negative weights are allowed.
#guard (demo (ofEdges (0 : Fin 3) [(0, 1, -5), (1, 2, -7), (2, 1, -9), (0, 2, 3)])).1 = some [0, 0, 1]

-- No edge enters {2, 3}, so there is no arborescence.
#guard (demo (ofEdges (0 : Fin 4) [(0, 1, 1), (2, 3, 1), (3, 2, 1)])).1 = none

end Arborescence
