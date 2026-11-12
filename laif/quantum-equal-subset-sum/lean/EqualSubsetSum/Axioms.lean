import EqualSubsetSum

/-! Prints the axioms of the main theorems. Run with `lake env lean EqualSubsetSum/Axioms.lean`. -/

-- Lemma 1 and the sign flip
#print axioms EqualSubsetSum.sub_trinary
#print axioms EqualSubsetSum.ne_of_zero_on_B
#print axioms EqualSubsetSum.exists_zero_on_B
#print axioms EqualSubsetSum.validity
#print axioms EqualSubsetSum.MinimalSolution.flip
-- Lemma 2
#print axioms EqualSubsetSum.good_cnt
#print axioms EqualSubsetSum.repX_isX
#print axioms EqualSubsetSum.repY_isY
#print axioms EqualSubsetSum.repOf_bijOn
#print axioms EqualSubsetSum.card_reps
#print axioms EqualSubsetSum.value_eq
#print axioms EqualSubsetSum.card_free_lt_supp
#print axioms EqualSubsetSum.value_injOn
#print axioms EqualSubsetSum.choose_of_empty
#print axioms EqualSubsetSum.value_injOn_of_empty
-- Lemma 3
#print axioms EqualSubsetSum.count_above
#print axioms EqualSubsetSum.averaging
#print axioms EqualSubsetSum.markov
#print axioms EqualSubsetSum.sum_sq_classes
#print axioms EqualSubsetSum.cauchy_classes
#print axioms EqualSubsetSum.classes_lower_bound
#print axioms EqualSubsetSum.card_prime_divisors_le
#print axioms EqualSubsetSum.primeHit_of_card
#print axioms EqualSubsetSum.filter_lemma
#print axioms EqualSubsetSum.card_repValues
#print axioms EqualSubsetSum.filter_lists
-- Lemma 4
#print axioms EqualSubsetSum.card_firstIndices
#print axioms EqualSubsetSum.exists_mem_lt
#print axioms EqualSubsetSum.card_firstWindow
#print axioms EqualSubsetSum.firstWindow_subset
#print axioms EqualSubsetSum.cap_lemma
-- Lemmas 3 and 4 composed on the actual lists
#print axioms EqualSubsetSum.pairFound_of_good
#print axioms EqualSubsetSum.marked_fraction
-- A uniform number of iterations
#print axioms EqualSubsetSum.two_sin_mul_sum_cos
#print axioms EqualSubsetSum.grover_average
#print axioms EqualSubsetSum.grover_uniform
-- The accounting
#print axioms EqualSubsetSum.hypotheses_satisfiable
#print axioms EqualSubsetSum.balance
#print axioms EqualSubsetSum.totalExp_balanced
#print axioms EqualSubsetSum.balance_optimal
#print axioms EqualSubsetSum.window_exp_balanced
#print axioms EqualSubsetSum.baseCost_le
#print axioms EqualSubsetSum.total_softO
#print axioms EqualSubsetSum.choose_half_bounds
#print axioms EqualSubsetSum.softO_choose
#print axioms EqualSubsetSum.schedule_exponents
#print axioms EqualSubsetSum.total_exponent
#print axioms EqualSubsetSum.total_exponent_balanced
#print axioms EqualSubsetSum.softO_inv_const
#print axioms EqualSubsetSum.primeHit_of_primeCount
#print axioms EqualSubsetSum.filter_parameters
-- The empty label
#print axioms EqualSubsetSum.listExp_empty
#print axioms EqualSubsetSum.empty_label_exponent
#print axioms EqualSubsetSum.emptyExp_one_third
#print axioms EqualSubsetSum.total_exponent_empty
-- The coin
#print axioms EqualSubsetSum.mean_chain
#print axioms EqualSubsetSum.coin_success
#print axioms EqualSubsetSum.coin_mean
#print axioms EqualSubsetSum.coin_mean_minimal
#print axioms EqualSubsetSum.coin_mean_empty
#print axioms EqualSubsetSum.coin_cost
