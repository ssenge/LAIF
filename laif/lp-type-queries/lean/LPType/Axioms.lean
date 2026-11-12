import LPType

/-! Prints the axioms of the main theorems. Run with `lake env lean LPType/Axioms.lean`. -/

-- Item 1: definitions and the dimension
#print axioms LPType.Problem.exists_isBasis
#print axioms LPType.Problem.IsBasis.card_le
#print axioms LPType.Problem.exists_isBasis_card_eq_combDim
-- Item 2: Facts 1 to 4
#print axioms LPType.Problem.fact1
#print axioms LPType.Problem.fact2
#print axioms LPType.Problem.fact3
#print axioms LPType.Problem.fact4
#print axioms LPType.Problem.fact4_of_no_violator
#print axioms LPType.Problem.exists_violates_iff
#print axioms LPType.Problem.stopping_correct
-- Item 3: Lemma 1
#print axioms LPType.prodWeight_sum
#print axioms LPType.prodWeight_swap
#print axioms LPType.prodExp_htSum
#print axioms LPType.Problem.prob_violator_identity
#print axioms LPType.Problem.prodExp_violators_core
#print axioms LPType.Problem.lemma1_general
#print axioms LPType.Problem.lemma1
-- Item 4: the potential argument, deterministic
#print axioms LPType.Problem.histTotal_cons
#print axioms LPType.Problem.histTotal_cons_le
#print axioms LPType.Problem.pigeonhole
#print axioms LPType.Problem.exists_many_violations
#print axioms LPType.Problem.two_rpow_le_histTotal
-- Item 4: the finite probability space
#print axioms LPType.Kernel.expect_eq_sum_paths
#print axioms LPType.Kernel.pathWeight_sum
#print axioms LPType.Kernel.markov
#print axioms LPType.Kernel.expect_potential_le_on
#print axioms LPType.Kernel.sum_conditioned_le
-- Item 4: the potential argument, expectation
#print axioms LPType.expect_estimate
#print axioms LPType.Problem.clarkson_W_next
#print axioms LPType.Problem.clarkson_expected_violators
#print axioms LPType.Problem.clarkson_step
#print axioms LPType.Problem.expected_W_le
#print axioms LPType.Problem.expected_W_le_exp
#print axioms LPType.Problem.two_rpow_le_of_notStopped
#print axioms LPType.Problem.prob_notStopped_mul_le
-- Item 4: the first moment arithmetic and the failure probability
#print axioms LPType.markov_arith
#print axioms LPType.markov_arith_half
#print axioms LPType.Problem.failure_prob_le
#print axioms LPType.Problem.failure_prob_le_sharp
#print axioms LPType.Problem.conditioned_step
#print axioms LPType.Problem.failure_prob_le_redraw
-- Item 5: the instance
#print axioms LPType.maxProblem
#print axioms LPType.maxProblem_violates_iff
#print axioms LPType.maxProblem_combDim
#print axioms LPType.maxProblem_failure_prob
-- Item 6: the query count, with the cost of quantum search as a hypothesis
#print axioms LPType.sum_mul_sqrt_le
#print axioms LPType.prodExp_sqrt_card_le
#print axioms LPType.sum_inclProb_le
#print axioms LPType.findAll_expected_cost_le
#print axioms LPType.search_cost_le_roundCost
#print axioms LPType.round_bound_le
#print axioms LPType.queryCount_le
#print axioms LPType.Problem.expected_queries_le
#print axioms LPType.Problem.expected_queries_le_log
