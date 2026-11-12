import ClusterRec.Graph
import ClusterRec.Query

/-!
# The lower bound for cluster graphs

The complete graph is a cluster graph, and the complete graph minus one edge of the hard family is not: the vertex
between the two ends gives an induced path. So the reduction from OR on `Θ(n²)` bits applies.
-/

open Finset

namespace ClusterRec

theorem top_cluster (n : ℕ) : IsCluster (⊤ : SimpleGraph (Fin n)) :=
  ⟨fun _ => ∅, fun u v huv => by simp [huv]⟩

theorem del_not_cluster {n : ℕ} (e : Fin n × Fin n) (he : e ∈ hardPairs n) :
    ¬ IsCluster ((⊤ : SimpleGraph (Fin n)).deleteEdges {s(e.1, e.2)}) := by
  obtain ⟨h1, h2, h3⟩ := (mem_filter.1 he).2
  have hw : e.1.val + 1 < n := by have := e.2.isLt; omega
  set w : Fin n := ⟨e.1.val + 1, hw⟩
  have hw1 : e.1 ≠ w := fun h => by have := congrArg Fin.val h; simp [w] at this
  have hw2 : w ≠ e.2 := fun h => by have := congrArg Fin.val h; simp [w] at this; omega
  have h12 : e.1 ≠ e.2 := fun h => by have := congrArg Fin.val h; omega
  apply not_cluster_of_p3 (a := e.1) (b := w) (c := e.2)
  refine ⟨?_, ?_, h12, ?_⟩
  · simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.top_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    refine ⟨hw1, ?_⟩
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hw2 h
    · exact h12 h
  · simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.top_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    refine ⟨hw2, ?_⟩
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hw1 h.symm
    · exact h12 h.symm
  · simp [SimpleGraph.deleteEdges_adj]

/-- **The lower bound.** Given the OR lower bound, deciding cluster graphs needs `Ω(n)` quantum queries. -/
theorem cluster_lower_bound (hOR : ORLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (A : QAlg (Fin n × Fin n) T S Bool),
      4 ≤ n → DecidesGraphs A IsCluster → c * n ≤ T := by
  classical
  obtain ⟨c, hc0, hc⟩ := hOR
  refine ⟨c / 8, by positivity, fun n T S _ _ A hn hA => ?_⟩
  have h := graph_lower_bound hc A IsCluster ⊤ ?_ (top_cluster n) ?_ hA
  · have h2 := mul_le_mul_of_nonneg_left (sqrt_hardPairs hn) hc0.le
    linarith [h2, h, show c / 8 * (n : ℝ) = c * ((n : ℝ) / 8) by ring]
  · intro e he
    obtain ⟨-, -, h3⟩ := (mem_filter.1 he).2
    simp only [SimpleGraph.top_adj, ne_eq]
    intro h
    have := congrArg Fin.val h
    omega
  · intro e he
    exact del_not_cluster e he

end ClusterRec
