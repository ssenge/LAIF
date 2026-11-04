import Dominators

/-! Prints the axioms of the main theorems. Built by `lake env lean Dominators/Axioms.lean`. -/

-- definitions and Lemma 2
#print axioms Dominators.dominates_iff_paths
#print axioms Dominators.onAllPaths_iff_paths
#print axioms Dominators.exists_idom
#print axioms Dominators.IsIdom.unique
#print axioms Dominators.lemma2
#print axioms Dominators.isBridge_iff_test
#print axioms Dominators.isBridge_iff_cuts
-- Lemma 3 and Theorem 3's reduction
#print axioms Dominators.lemma3_edge
#print axioms Dominators.lemma3_vertex
#print axioms Dominators.isSAP_self_iff
#print axioms Dominators.isStrongBridge_iff_mutual
#print axioms Dominators.isSAP_iff_separates
#print axioms Dominators.sccCount_delEdge_eq
#print axioms Dominators.sccCount_delVertex_of_alone
#print axioms Dominators.theorem3_edge
#print axioms Dominators.theorem3_vertex
-- depth-first search
#print axioms Dominators.dfs_visited_iff
#print axioms Dominators.dfs_searches_le
#print axioms Dominators.dfs_stack_nil
#print axioms Dominators.forest_searches_le
#print axioms Dominators.run_stack_nil
#print axioms Dominators.dfs_isDfsTree
-- Kosaraju
#print axioms Dominators.round1_order
#print axioms Dominators.kosaraju_correct
#print axioms Dominators.kosaraju_same_iff
-- cost
#print axioms Dominators.expected_search_sum
#print axioms Dominators.vertex_cost_le
#print axioms Dominators.lemma1_cauchy
#print axioms Dominators.lemma1_array
#print axioms Dominators.lemma1_matrix
#print axioms Dominators.sum_sqrt_inDeg_le
#print axioms Dominators.partition_sum_le
#print axioms Dominators.partition_matrix_sum
#print axioms Dominators.union_error_le
#print axioms Dominators.runCharge_total
#print axioms Dominators.dfs_charge_array
#print axioms Dominators.dfs_charge_matrix
#print axioms Dominators.dominator_charge_total
#print axioms Dominators.minFind_calls_le
#print axioms Dominators.minFind_charge_le
#print axioms Dominators.bbht_budget
#print axioms Dominators.durrHoyer_total
-- gadgets
#print axioms Dominators.sink_bridge_iff
#print axioms Dominators.sink_connected_iff
#print axioms Dominators.sb_bridge_iff
#print axioms Dominators.sb_strongConn
#print axioms Dominators.sb_isolated
#print axioms Dominators.sb_no_change
#print axioms Dominators.sb_connected_iff
#print axioms Dominators.sb_edge_always_bridge
#print axioms Dominators.sap_iff
#print axioms Dominators.sap_b_alone
#print axioms Dominators.sap_a_alone
#print axioms Dominators.sap_count_conn
#print axioms Dominators.sap_count_not
#print axioms Dominators.or_idom_no_edge
#print axioms Dominators.or_idom_edge
#print axioms Dominators.or_of_output
-- lower bounds
#print axioms Dominators.QAlg.sim_solves
#print axioms Dominators.RandAlg.sim_solves
#print axioms Dominators.dominators_lower_bound
#print axioms Dominators.bridges_lower_bound
#print axioms Dominators.strongBridges_lower_bound
#print axioms Dominators.saps_lower_bound
#print axioms Dominators.classical_bridges_lower_bound
#print axioms Dominators.classical_strongBridges_lower_bound
#print axioms Dominators.classical_saps_lower_bound
#print axioms Dominators.or_lower_bound
#print axioms Dominators.classical_dominators_lower_bound
-- semidominators and the dominator algorithm
#print axioms Dominators.IsDfsTree.sdom_formula
#print axioms Dominators.IsDfsTree.sdom_key
#print axioms Dominators.IsDfsTree.idom_iff_nca
#print axioms Dominators.sdomTable_spec
#print axioms Dominators.nca_spec
#print axioms Dominators.idomOfTree_spec
#print axioms Dominators.dominators_correct
#print axioms Dominators.dominators_none_iff
