import SmallCut.Scan

/-!
# Content of the certificate statements

* The bound `hmax` of `certificate` is needed: without it the inequality fails for one edge and empty
  forests.
* The scan rule `hscan` holds non-trivially on the triangle, and forest `1` of that scan has an edge,
  so `scan_hmax` at `i = 1` speaks about a non-empty forest.
-/

open Classical

namespace SmallCut

/-- Without `hmax` the inequality of `certificate` fails: one edge, empty forests. -/
theorem certificate_needs_hmax : ¬ (min 1 (cross (⊤ : SimpleGraph (Fin 2)).Adj {0}).card ≤
    (cross (fun u v => ∃ i < 1, (⊥ : SimpleGraph (Fin 2)).Adj u v) {0}).card) := by
  have h1 : cross (⊤ : SimpleGraph (Fin 2)).Adj {0} = {(0, 1)} := by
    ext ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [mem_cross]
  have h2 : cross (fun u v => ∃ i < 1, (⊥ : SimpleGraph (Fin 2)).Adj u v) {0} = ∅ := by
    ext ⟨a, b⟩; simp [mem_cross]
  rw [h1, h2]; simp

/-- The scan rule `hscan` holds on the triangle with the identity order and `k = 2`. -/
theorem triangle_scan_rule : ∀ x y : Fin 3, (x : ℕ) < y →
    min 2 (cnt (⊤ : SimpleGraph (Fin 3)) (fun v => (v : ℕ)) x y) ≤
    min 2 (cnt (⊤ : SimpleGraph (Fin 3)) (fun v => (v : ℕ)) x x) := by
  simp only [cnt, Finset.filter_congr_decidable]
  first | decide | (intro x y; fin_cases x <;> fin_cases y <;> simp <;> rfl)

/-- Forest `1` of that scan has the edge `1 2`. -/
theorem triangle_forest_one_adj : (scanF (⊤ : SimpleGraph (Fin 3)) (fun v => (v : ℕ)) 1).Adj 1 2 := by
  rw [scan_adj_iff (by decide)]; refine ⟨by decide, ?_⟩
  simp only [cnt, Finset.filter_congr_decidable]
  first | decide | rfl

end SmallCut
