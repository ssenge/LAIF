import Arborescence

/-!
# Axioms check

Run with `lake env lean Arborescence/Axioms.lean`. Every headline theorem may depend only on `propext`,
`Classical.choice` and `Quot.sound`. Hypotheses of cited theorems appear as named Props in their statements.
-/

-- Goal 2: weak duality, certificate, no entering edge
#print axioms Arborescence.weak_duality
#print axioms Arborescence.weak_duality_list
#print axioms Arborescence.isMinArb_of_cost_eq
#print axioms Arborescence.certificate
#print axioms Arborescence.no_arb_of_no_entering

-- Goal 3: Lemma 1 and Lemma 3
#print axioms Arborescence.IsTopK.min_of_type
#print axioms Arborescence.IsTopK.finite_entry
#print axioms Arborescence.lemma3a
#print axioms Arborescence.lemma3b
#print axioms Arborescence.lemma3c

-- Goal 4: Lemma 4 and Lemma 5 on an abstract trace
#print axioms Arborescence.lemma4a
#print axioms Arborescence.lemma4b
#print axioms Arborescence.lemma4c
#print axioms Arborescence.lemma4d
#print axioms Arborescence.lemma4e
#print axioms Arborescence.sum_wt_le
#print axioms Arborescence.lemma5_cs
#print axioms Arborescence.lemma5

-- Goal 5: reductions of Theorem 2
#print axioms Arborescence.exists_arb_iff_connected
#print axioms Arborescence.isMinArb_to_isMST
#print axioms Arborescence.isMST_to_isMinArb
#print axioms Arborescence.or_iff_cost_lt
#print axioms Arborescence.or_iff_ne_star
#print axioms Arborescence.star_unique
#print axioms Arborescence.hidden_isMinArb_iff
#print axioms Arborescence.hidden_reveals

-- Goal 6: the algorithm
#print axioms Arborescence.solve_reach
#print axioms Arborescence.solve_run
#print axioms Arborescence.solve_sum_K
#print axioms Arborescence.solve_sum_N
#print axioms Arborescence.solve_cost
#print axioms Arborescence.solve_some
#print axioms Arborescence.solve_none
#print axioms Arborescence.solve_correct
#print axioms Arborescence.solve_queries
#print axioms Arborescence.exactTopK_correct
