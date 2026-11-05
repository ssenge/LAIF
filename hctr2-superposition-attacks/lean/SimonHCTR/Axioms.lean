import SimonHCTR

open SimonHCTR

-- Shift identities (Lemmas 1, 2, 3)
#print axioms HCTR2Key.enc_shift
#print axioms HCTR2Key.dec_shift
#print axioms HCTR2Key.dec_enc
#print axioms HCTR2Key.enc_dec
#print axioms chctrEnc_shift
#print axioms chctrDec_shift
#print axioms HCTRppKey.enc_shift
#print axioms HCTRppKey.enc_rest_shift
#print axioms HCTRppKey.dec_enc
#print axioms HCTRppKey.dec_shift
#print axioms HCTRppKey.dec_rest_shift

-- Key recovery
#print axioms recover_one
#print axioms recover_one'
#print axioms lamPoly_two_eq_iff
#print axioms lamPoly_two_of
#print axioms quadratic_roots
#print axioms recover_two
#print axioms recover_two_roots
#print axioms quotMap_eq_zero_iff
#print axioms quotMap_surjective

-- Collisions (Propositions 7, 8, 9, deterministic parts)
#print axioms HCTR2Key.g_eq
#print axioms HCTR2Key.Gfun_injective
#print axioms HCTR2Key.g_collision_iff
#print axioms chctr_g_eq
#print axioms chctr_collision_cases
#print axioms HCTRppKey.enc_rest_add
#print axioms HCTRppKey.collision_cases

-- Simon sampling (Section 2, Lemma 4, Theorem 5)
#print axioms Simon.simonProb_eq
#print axioms Simon.sum_simonProb
#print axioms Simon.card_mul_card_perp
#print axioms Simon.simonProb_eq_zero
#print axioms Simon.sum_simonProb_le
#print axioms Simon.sum_simonProb_le'
#print axioms Simon.lasVegas_sum_le
#print axioms Simon.lasVegas_sum_le_two

-- Tail bounds (Lemma 6)
#print axioms Tail.tail_delta
#print axioms Tail.tail_cross
#print axioms Tail.tail_hctrpp
