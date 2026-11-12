import Covers

/-! Run with `lake env lean Covers/Axioms.lean`. Every theorem below should depend on at most `propext`, `Classical.choice`
and `Quot.sound`. The hypotheses `GroverCost`, `MinCost`, `ORBound` are arguments, not axioms. -/

-- Definitions and Section 1
#print axioms Strings.occursAt_iff_isPrefix_drop
#print axioms Strings.Covers.isBorder
#print axioms Strings.not_isBorder_of_covers_nil
#print axioms Strings.covers_self
#print axioms Strings.Covers.trans
#print axioms Strings.lemma1
#print axioms Strings.IsShortestCover.eq_rangeMin
#print axioms Strings.IsShortestCover.no_cover_below
#print axioms Strings.corollary_shortest
#print axioms Strings.first_covering_rangeMin_isShortest
#print axioms Strings.covers_downward_in_range
#print axioms Strings.coverLengths_eq_takeWhile
#print axioms Strings.mem_borderLengths
#print axioms Strings.firstCover_correct

-- Lemma 3 and the sampling process
#print axioms Strings.vishkin_exclusion
#print axioms Strings.OccursAt.passes
#print axioms Strings.two_extremes
#print axioms Strings.two_extremes_block
#print axioms Strings.IsPhase.isSample
#print axioms Strings.isSample_example
#print axioms Strings.period_of_agree
#print axioms Strings.smaller_class_le_half

-- Lemma 5
#print axioms Strings.covers_iff_no_gap
#print axioms Strings.lemma5_at
#print axioms Strings.lemma5
#print axioms Strings.lemma5_blocks
#print axioms Strings.numBlocks_le

-- Section 2
#print axioms Strings.fine_wilf
#print axioms Strings.smallest_dvd
#print axioms Strings.gcd_restart
#print axioms Strings.IsPhase.invariant
#print axioms Strings.IsPhase.exists_pair
#print axioms Strings.lemma2_le
#print axioms Strings.lemma2_eq
#print axioms Strings.exists_column_of_lt_smallest
#print axioms Strings.hasPeriod_of_prefix
#print axioms Strings.smallest_period_take
#print axioms Strings.not_four_blocks
#print axioms Strings.blocks_le_six
#print axioms Strings.blocks_le_four
#print axioms Strings.lemma4_case1
#print axioms Strings.exists_Q_occurrence
#print axioms Strings.Q_occurrence_unique
#print axioms Strings.output_sound
#print axioms Strings.output_complete
#print axioms Strings.lemma4_case2
#print axioms Strings.lemma4_case2_below
#print axioms Strings.no_occurrence_of_no_Q

-- Section 4
#print axioms Strings.border_start_range
#print axioms Strings.border_occurs_prefix
#print axioms Strings.isBorder_drop_iff
#print axioms Strings.border_iff_of_run_to_end
#print axioms Strings.border_start_of_run_break
#print axioms Strings.cap_reaches_end
#print axioms Strings.capped_stop_is_not_break

-- Lower bound
#print axioms Strings.replicate_shortestCover
#print axioms Strings.oneB_cover_eq
#print axioms Strings.oneB_shortestCover
#print axioms Strings.oneB_shortest_length_ne_one
#print axioms Strings.oneB_shortest_length_gt_third
#print axioms Strings.shortest_lengths_differ
#print axioms Strings.oneB_isBorder_take_iff
#print axioms Strings.cover_lower_bound

-- Model and query counts
#print axioms Strings.primitives_consistent
#print axioms Strings.occQ_le
#print axioms Strings.sampleQ_le
#print axioms Strings.testQ_le
#print axioms Strings.rangeQ_le
#print axioms Strings.total_le
#print axioms Strings.theorem1_cost
#print axioms Strings.theorem2_cost
#print axioms Strings.coherent_error_le
#print axioms Strings.union_bound_failure
