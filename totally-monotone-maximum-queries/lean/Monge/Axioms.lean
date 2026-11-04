import Monge

/-! Prints the axioms of the main theorems. Run with `lake env lean Monge/Axioms.lean`. -/

-- Goal 1: total monotonicity
#print axioms Monge.InverseMonge.totallyMonotone
#print axioms Monge.TotallyMonotone.rowMax_monotone
#print axioms Monge.TotallyMonotone.window
-- Goal 2: the hard family
#print axioms Monge.hard_inverseMonge
#print axioms Monge.hard_isGreatest
-- Goal 3: the algorithm and the window sums
#print axioms Monge.globalMax_spec
#print axioms Monge.scanOracle_spec
#print axioms Monge.width_split
#print axioms Monge.levelWidths_sum_le
#print axioms Monge.levelCost_le
#print axioms Monge.totalCost_le
#print axioms Monge.blockWidths_sum
-- Goal 4: polygons
#print axioms Monge.quadrilateral
#print axioms Monge.diagonals_cross
#print axioms Monge.arc_inverseMonge
#print axioms Monge.arc_sq_totallyMonotone
#print axioms Monge.parabola_convex
-- Goal 5: filtered gamma_2, the recurrence and Theorem 3
#print axioms Monge.exists_gammaLE
#print axioms Monge.seqComp_feasible
#print axioms Monge.seqComp_cost
#print axioms Monge.gam_seq_le
#print axioms Monge.orFact_feasible
#print axioms Monge.orFact_cost
#print axioms Monge.gammaLE_or
#print axioms Monge.gam_or_le
#print axioms Monge.gam_or_bits_le
#print axioms Monge.recurrence_solution
#print axioms Monge.gam_rect_le
#print axioms Monge.theorem3_gamma
#print axioms Monge.decision_query_le
#print axioms Monge.theorem3_query_le
#print axioms Monge.theorem3_sqrt_log
-- Goal 6: the exponents of Theorem 1
#print axioms Monge.expo_step
#print axioms Monge.nested_bound
#print axioms Monge.nested_bound_depth_one
-- The corollary on the maximum: everything but the composition in the quantum model
#print axioms Monge.someAbove_query_le
#print axioms Monge.someAbove_sqrt_log
#print axioms Monge.firstTrue_spec
#print axioms Monge.firstTrueCalls_le
#print axioms Monge.visited_spec
#print axioms Monge.visited_finds_max
#print axioms Monge.sum_recordCount_le
#print axioms Monge.mean_rounds_le
#print axioms Monge.maximum_mean_cost
#print axioms Monge.tieMatrix_facts
