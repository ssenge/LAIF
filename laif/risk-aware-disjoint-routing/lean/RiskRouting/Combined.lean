import RiskRouting.QUBO

/-!
# The penalty weight for the reduced encoding

The reduced encoding of E. G. Dalla Torre, B.-E. Friedman, D. Porat, Encoding matters: a
qubit-efficient reformulation for quantum resilient routing, arXiv:2610.13621 (2026), merges the
links through inner vertices of degree 2, solves "exactly one link" at each terminal for one dependent
link `x = 1 - Σ q` (with the pair penalty `Σ_{i<j} q_i q_j` when at least two others remain), and keeps
a node variable only where the degree cannot be substituted. A dependent link can take negative values
when its pair penalty is positive, so the objective is not nonnegative on all assignments.

- `minimizer_of_gap`, `infeasible_of_gap`: if every assignment of nonzero penalty has `H > U`, every
  minimizer has penalty zero and gives an optimal feasible pair, and without a feasible pair `min H > U`.
- `gap_of_neg`: if the objective is at least `-D` times the total negative part, and the negative part
  is at most the penalty, then `A > U + D` gives the gap.
- `gap_of_neg_double`: if the negative part is at most half the penalty (pair penalties counted
  twice) and `D ≤ U`, then `A > U` gives the gap.
- `reduced_minimizer`, `reduced_infeasible`, `reduced_minimizer_double`, `reduced_infeasible_double`:
  the two weights combined with `minimizer_of_gap` and `infeasible_of_gap`.
- `dep_neg_le_pairs`, `dep_le_one_of_pairs_zero`: the negative part of `1 - Σ q` is at most the pair
  penalty, and a zero pair penalty gives `Σ q ≤ 1`, so the dependent link is 0 or 1.
- `obj_ge_neg_D`, `link_weight_le_U`: with values at most 1, the objective is at least `-D` times the
  total negative part, where `D` bounds `c(e) + B Σ_f p(e, f)` over the links with a negative value;
  for symmetric `p ≥ 0` with zero diagonal, each `c(e) + B Σ_f p(e, f)` is at most `U`.
-/

namespace RiskRouting.Combined

open Finset

/-! ## A minimizer statement from a gap -/

section Abstract

variable {X : Type*} (obj : X → ℚ) (pen : X → ℕ) (Feas : X → Prop) (U A : ℚ)

/-- **Minimizers from a gap.** If feasible assignments have penalty zero and objective at most `U`,
every assignment of nonzero penalty has `H > U`, and every assignment of penalty zero contains a
feasible one of no larger objective, then a minimizer of `H = obj + A · pen` has penalty zero and
gives a feasible assignment of the same objective that is optimal among feasible assignments. -/
theorem minimizer_of_gap (hFpen : ∀ x, Feas x → pen x = 0) (hFU : ∀ x, Feas x → obj x ≤ U)
    (hgap : ∀ x, pen x ≠ 0 → U < obj x + A * pen x)
    (hred : ∀ x, pen x = 0 → ∃ y, Feas y ∧ obj y ≤ obj x)
    (x : X) (hmin : ∀ z, obj x + A * pen x ≤ obj z + A * pen z) (hex : ∃ z, Feas z) :
    pen x = 0 ∧ ∃ y, Feas y ∧ obj y = obj x ∧ ∀ z, Feas z → obj y ≤ obj z := by
  obtain ⟨z, hz⟩ := hex
  have hpx : pen x = 0 := by
    by_contra h
    have h1 := hgap x h
    have h2 := hmin z
    rw [hFpen z hz] at h2
    simp only [Nat.cast_zero, mul_zero, add_zero] at h2
    linarith [hFU z hz]
  refine ⟨hpx, ?_⟩
  obtain ⟨y, hy, hyx⟩ := hred x hpx
  have hxy : obj x ≤ obj y := by
    have := hmin y
    rw [hpx, hFpen y hy] at this
    simpa using this
  refine ⟨y, hy, le_antisymm hyx hxy, fun w hw => ?_⟩
  have := hmin w
  rw [hpx, hFpen w hw] at this
  simp only [Nat.cast_zero, mul_zero, add_zero] at this
  linarith

/-- **Infeasibility from a gap.** If no assignment has penalty zero, `H > U` everywhere. -/
theorem infeasible_of_gap (hgap : ∀ x, pen x ≠ 0 → U < obj x + A * pen x)
    (hnone : ∀ x, pen x ≠ 0) (x : X) : U < obj x + A * pen x :=
  hgap x (hnone x)

variable (neg : X → ℕ) (D : ℚ)

/-- **Gap with the penalties of the reduced encoding.** If `obj ≥ -D · neg` and `neg ≤ pen`, then
`A > U + D` gives `H > U` at every assignment of nonzero penalty. -/
theorem gap_of_neg (hU : 0 ≤ U) (hD : 0 ≤ D) (hlow : ∀ x, -(D * neg x) ≤ obj x)
    (hneg : ∀ x, neg x ≤ pen x) (hA : U + D < A) (x : X) (hx : pen x ≠ 0) :
    U < obj x + A * pen x := by
  have h1 : (1 : ℚ) ≤ pen x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx
  have h2 : (neg x : ℚ) ≤ pen x := by exact_mod_cast hneg x
  have h3 := hlow x
  have h4 : D * neg x ≤ D * pen x := mul_le_mul_of_nonneg_left h2 hD
  have h5 : (A - D) * 1 ≤ (A - D) * pen x := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

/-- **Gap with doubled pair penalties.** If `obj ≥ -D · neg` with `D ≤ U` and `2 · neg ≤ pen`, then
`A > U` gives `H > U` at every assignment of nonzero penalty. -/
theorem gap_of_neg_double (hU : 0 ≤ U) (hDU : D ≤ U)
    (hlow : ∀ x, -(D * neg x) ≤ obj x) (hneg : ∀ x, 2 * neg x ≤ pen x) (hA : U < A) (x : X)
    (hx : pen x ≠ 0) : U < obj x + A * pen x := by
  have h1 : (1 : ℚ) ≤ pen x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx
  have h2 : 2 * (neg x : ℚ) ≤ pen x := by exact_mod_cast hneg x
  have h3 := hlow x
  have hA0 : 0 ≤ A := by linarith
  rcases Nat.eq_zero_or_pos (neg x) with h0 | hpos
  · rw [h0] at h3
    simp only [Nat.cast_zero, mul_zero, neg_zero] at h3
    have : A * 1 ≤ A * pen x := mul_le_mul_of_nonneg_left h1 hA0
    linarith
  · have h6 : (1 : ℚ) ≤ neg x := by exact_mod_cast hpos
    have h4 : D * neg x ≤ U * neg x := mul_le_mul_of_nonneg_right hDU (by linarith)
    have h5 : A * (2 * neg x) ≤ A * pen x := mul_le_mul_of_nonneg_left h2 hA0
    have h7 : (2 * A - U) * 1 ≤ (2 * A - U) * neg x := mul_le_mul_of_nonneg_left h6 (by linarith)
    nlinarith

/-- **Theorem (reduced encoding, `A > U + D`).** With `obj ≥ -D · neg`, `neg ≤ pen` and
`A > U + D`, a minimizer of `H` has penalty zero and gives an optimal feasible assignment. -/
theorem reduced_minimizer (hU : 0 ≤ U) (hD : 0 ≤ D) (hlow : ∀ x, -(D * neg x) ≤ obj x)
    (hneg : ∀ x, neg x ≤ pen x) (hA : U + D < A) (hFpen : ∀ x, Feas x → pen x = 0)
    (hFU : ∀ x, Feas x → obj x ≤ U) (hred : ∀ x, pen x = 0 → ∃ y, Feas y ∧ obj y ≤ obj x)
    (x : X) (hmin : ∀ z, obj x + A * pen x ≤ obj z + A * pen z) (hex : ∃ z, Feas z) :
    pen x = 0 ∧ ∃ y, Feas y ∧ obj y = obj x ∧ ∀ z, Feas z → obj y ≤ obj z :=
  minimizer_of_gap obj pen Feas U A hFpen hFU (gap_of_neg obj pen U A neg D hU hD hlow hneg hA)
    hred x hmin hex

/-- **Theorem (reduced encoding, infeasibility).** Under the same conditions, if no assignment has
penalty zero, `H > U` everywhere. -/
theorem reduced_infeasible (hU : 0 ≤ U) (hD : 0 ≤ D) (hlow : ∀ x, -(D * neg x) ≤ obj x)
    (hneg : ∀ x, neg x ≤ pen x) (hA : U + D < A) (hnone : ∀ x, pen x ≠ 0) (x : X) :
    U < obj x + A * pen x :=
  gap_of_neg obj pen U A neg D hU hD hlow hneg hA x (hnone x)

/-- **Theorem (doubled pair penalties, `A > U`).** With `obj ≥ -D · neg`, `D ≤ U`,
`2 · neg ≤ pen` and `A > U`, a minimizer of `H` has penalty zero and gives an optimal feasible
assignment. -/
theorem reduced_minimizer_double (hU : 0 ≤ U) (hDU : D ≤ U) (hlow : ∀ x, -(D * neg x) ≤ obj x)
    (hneg : ∀ x, 2 * neg x ≤ pen x) (hA : U < A) (hFpen : ∀ x, Feas x → pen x = 0)
    (hFU : ∀ x, Feas x → obj x ≤ U) (hred : ∀ x, pen x = 0 → ∃ y, Feas y ∧ obj y ≤ obj x)
    (x : X) (hmin : ∀ z, obj x + A * pen x ≤ obj z + A * pen z) (hex : ∃ z, Feas z) :
    pen x = 0 ∧ ∃ y, Feas y ∧ obj y = obj x ∧ ∀ z, Feas z → obj y ≤ obj z :=
  minimizer_of_gap obj pen Feas U A hFpen hFU
    (gap_of_neg_double obj pen U A neg D hU hDU hlow hneg hA) hred x hmin hex

/-- **Theorem (doubled pair penalties, infeasibility).** Under the same conditions, if no assignment
has penalty zero, `H > U` everywhere. -/
theorem reduced_infeasible_double (hU : 0 ≤ U) (hDU : D ≤ U) (hlow : ∀ x, -(D * neg x) ≤ obj x)
    (hneg : ∀ x, 2 * neg x ≤ pen x) (hA : U < A) (hnone : ∀ x, pen x ≠ 0) (x : X) :
    U < obj x + A * pen x :=
  gap_of_neg_double obj pen U A neg D hU hDU hlow hneg hA x (hnone x)

end Abstract

/-! ## The dependent link at a terminal -/

section Dependent

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- With 0/1 values, the sum counts the active indices. -/
theorem sum_eq_card_active (S : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ S, q i ≤ 1) :
    ∑ i ∈ S, q i = (S.filter fun i => q i = 1).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := hq i hi
  split_ifs with h
  · exact h
  · omega

/-- With 0/1 values, the pair penalty `Σ_{i<j} q_i q_j` is `C(k, 2)` for `k` active indices. -/
theorem sum_pairs_eq_choose (S : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ S, q i ≤ 1) :
    ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, q i = ((S.filter fun i => q i = 1).card).choose 2 := by
  rw [← Finset.card_powersetCard]
  have hprod : ∀ T ∈ S.powersetCard 2,
      ∏ i ∈ T, q i = if T ⊆ S.filter (fun i => q i = 1) then 1 else 0 := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    split_ifs with h
    · exact Finset.prod_eq_one fun i hi => (Finset.mem_filter.mp (h hi)).2
    · rw [Finset.not_subset] at h
      obtain ⟨i, hi, hni⟩ := h
      apply Finset.prod_eq_zero hi
      have h1 := hq i (hT.1 hi)
      have h2 : ¬ q i = 1 := fun h => hni (Finset.mem_filter.mpr ⟨hT.1 hi, h⟩)
      omega
  rw [Finset.sum_congr rfl hprod, Finset.sum_boole, Nat.cast_id]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩
    exact ⟨⟨h3.trans (Finset.filter_subset _ _), h2⟩, h3⟩

theorem pred_le_choose_two (k : ℕ) : k - 1 ≤ k.choose 2 := by
  induction k with
  | zero => simp
  | succ k _ =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- The negative part of `1 - k` is at most `C(k, 2)`. -/
theorem neg_le_choose (k : ℕ) : max 0 (-(1 - (k : ℚ))) ≤ (k.choose 2 : ℚ) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; norm_num
  · have h1 : ((k - 1 : ℕ) : ℚ) ≤ k.choose 2 := by exact_mod_cast pred_le_choose_two k
    rw [Nat.cast_sub h] at h1
    rw [max_le_iff]
    exact ⟨Nat.cast_nonneg _, by push_cast at h1 ⊢; linarith⟩

/-- **Lemma.** The negative part of the dependent link `1 - Σ q` is at most its pair penalty. -/
theorem dep_neg_le_pairs (S : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ S, q i ≤ 1) :
    max 0 (-(1 - ((∑ i ∈ S, q i : ℕ) : ℚ))) ≤ ((∑ T ∈ S.powersetCard 2, ∏ i ∈ T, q i : ℕ) : ℚ) := by
  rw [sum_pairs_eq_choose S q hq, sum_eq_card_active S q hq]
  exact neg_le_choose _

/-- **Lemma.** A zero pair penalty leaves at most one active index, so `1 - Σ q` is 0 or 1. -/
theorem dep_le_one_of_pairs_zero (S : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ S, q i ≤ 1)
    (h0 : ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, q i = 0) : ∑ i ∈ S, q i ≤ 1 := by
  rw [sum_pairs_eq_choose S q hq] at h0
  rw [sum_eq_card_active S q hq]
  have := Nat.choose_eq_zero_iff.mp h0
  omega

end Dependent

/-! ## The objective at signed values -/

section Signed

/-- For `a, b ≤ 1`, `a b ≥ -(a⁻ + b⁻)` with `v⁻ = max 0 (-v)`. -/
theorem mul_ge_neg_parts {a b : ℚ} (ha : a ≤ 1) (hb : b ≤ 1) :
    -(max 0 (-a) + max 0 (-b)) ≤ a * b := by
  rcases le_total 0 a with h | h <;> rcases le_total 0 b with h' | h'
  · have := mul_nonneg h h'
    have := le_max_left 0 (-a)
    have := le_max_left 0 (-b)
    linarith
  · rw [max_eq_left (by linarith : -a ≤ 0), max_eq_right (by linarith : 0 ≤ -b)]
    nlinarith
  · rw [max_eq_right (by linarith : 0 ≤ -a), max_eq_left (by linarith : -b ≤ 0)]
    nlinarith
  · have := mul_nonneg_of_nonpos_of_nonpos h h'
    have := le_max_left 0 (-a)
    have := le_max_left 0 (-b)
    linarith

variable {L : Type*} [Fintype L] (c : L → ℚ) (p : L → L → ℚ) (B : ℚ)

/-- **Lemma.** With link values at most 1 on both paths, the objective
`Σ c x + Σ c y + B Σ p(e, f) x_e y_f` is at least
`-(Σ_e x_e⁻ (c(e) + B Σ_f p(e, f)) + Σ_f y_f⁻ (c(f) + B Σ_e p(e, f)))`. -/
theorem obj_lower (hc : ∀ e, 0 ≤ c e) (hp : ∀ e f, 0 ≤ p e f) (hB : 0 ≤ B) (x y : L → ℚ)
    (hx : ∀ e, x e ≤ 1) (hy : ∀ f, y f ≤ 1) :
    -(∑ e, max 0 (-x e) * (c e + B * ∑ f, p e f) + ∑ f, max 0 (-y f) * (c f + B * ∑ e, p e f)) ≤
      ∑ e, c e * x e + ∑ f, c f * y f + B * ∑ e, ∑ f, p e f * (x e * y f) := by
  have h1 : -(∑ e, max 0 (-x e) * c e) ≤ ∑ e, c e * x e := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have := hc e
    have := le_max_right 0 (-x e)
    nlinarith
  have h2 : -(∑ f, max 0 (-y f) * c f) ≤ ∑ f, c f * y f := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun f _ => ?_
    have := hc f
    have := le_max_right 0 (-y f)
    nlinarith
  have h3 : ∑ e, ∑ f, -(p e f * max 0 (-x e) + p e f * max 0 (-y f)) ≤
      ∑ e, ∑ f, p e f * (x e * y f) := by
    refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ => ?_
    have := mul_ge_neg_parts (hx e) (hy f)
    have := hp e f
    nlinarith
  have e3 : ∑ e, ∑ f, -(p e f * max 0 (-x e) + p e f * max 0 (-y f)) =
      -(∑ e, max 0 (-x e) * ∑ f, p e f + ∑ f, max 0 (-y f) * ∑ e, p e f) := by
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun e f => p e f * max 0 (-y f))]
    congr 1
    congr 1
    · exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun e _ => mul_comm _ _
  rw [e3] at h3
  have h4 := mul_le_mul_of_nonneg_left h3 hB
  have e4 : ∑ e, max 0 (-x e) * (c e + B * ∑ f, p e f) + ∑ f, max 0 (-y f) * (c f + B * ∑ e, p e f) =
      ∑ e, max 0 (-x e) * c e + ∑ f, max 0 (-y f) * c f +
        B * (∑ e, max 0 (-x e) * ∑ f, p e f + ∑ f, max 0 (-y f) * ∑ e, p e f) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have ha : ∀ e, ∑ f, max 0 (-x e) * (B * p e f) = ∑ f, B * (max 0 (-x e) * p e f) :=
      fun e => Finset.sum_congr rfl fun f _ => by ring
    have hb : ∀ f, ∑ e, max 0 (-y f) * (B * p e f) = ∑ e, B * (max 0 (-y f) * p e f) :=
      fun f => Finset.sum_congr rfl fun e _ => by ring
    simp only [ha, hb]
    ring
  rw [e4]
  linarith

/-- **Lemma.** If `D` bounds `c(e) + B Σ_f p(e, f)` at every link with a negative value, the
objective is at least `-D` times the total negative part. -/
theorem obj_ge_neg_D (hc : ∀ e, 0 ≤ c e) (hp : ∀ e f, 0 ≤ p e f) (hB : 0 ≤ B) (x y : L → ℚ)
    (hx : ∀ e, x e ≤ 1) (hy : ∀ f, y f ≤ 1) (D : ℚ)
    (hDx : ∀ e, x e < 0 → c e + B * ∑ f, p e f ≤ D)
    (hDy : ∀ f, y f < 0 → c f + B * ∑ e, p e f ≤ D) :
    -(D * (∑ e, max 0 (-x e) + ∑ f, max 0 (-y f))) ≤
      ∑ e, c e * x e + ∑ f, c f * y f + B * ∑ e, ∑ f, p e f * (x e * y f) := by
  refine le_trans ?_ (obj_lower c p B hc hp hB x y hx hy)
  rw [neg_le_neg_iff, mul_add, Finset.mul_sum, Finset.mul_sum]
  apply add_le_add
  · refine Finset.sum_le_sum fun e _ => ?_
    rcases lt_or_ge (x e) 0 with h | h
    · rw [mul_comm D]
      exact mul_le_mul_of_nonneg_left (hDx e h) (le_max_left _ _)
    · rw [max_eq_left (by linarith : -x e ≤ 0)]
      simp
  · refine Finset.sum_le_sum fun f _ => ?_
    rcases lt_or_ge (y f) 0 with h | h
    · rw [mul_comm D]
      exact mul_le_mul_of_nonneg_left (hDy f h) (le_max_left _ _)
    · rw [max_eq_left (by linarith : -y f ≤ 0)]
      simp

/-- **Lemma (`D ≤ U`).** For symmetric `p ≥ 0` with zero diagonal, every link has
`c(e) + B Σ_f p(e, f) ≤ U = c(E) + B Σ_{e ≠ f, unordered} p(e, f)`. -/
theorem link_weight_le_U [DecidableEq L] (hc : ∀ e, 0 ≤ c e) (hp : ∀ e f, 0 ≤ p e f)
    (hsym : ∀ e f, p e f = p f e) (hdiag : ∀ e, p e e = 0) (hB : 0 ≤ B) (e : L) :
    c e + B * ∑ f, p e f ≤
      ∑ e, c e + B * ((1 / 2) * ∑ ef ∈ (Finset.univ : Finset L).offDiag, p ef.1 ef.2) := by
  have hc1 : c e ≤ ∑ e, c e := Finset.single_le_sum (fun e _ => hc e) (Finset.mem_univ e)
  set S1 := ((Finset.univ : Finset L).erase e).image fun f => (e, f)
  set S2 := ((Finset.univ : Finset L).erase e).image fun f => (f, e)
  have hS1 : ∑ ef ∈ S1, p ef.1 ef.2 = ∑ f, p e f := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.mp h).2)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e), hdiag, add_zero]
  have hS2 : ∑ ef ∈ S2, p ef.1 ef.2 = ∑ f, p e f := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.mp h).1)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e), hdiag, add_zero]
    exact Finset.sum_congr rfl fun f _ => hsym f e
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro ef h1 h2
    simp only [S1, S2, Finset.mem_image, Finset.mem_erase] at h1 h2
    obtain ⟨f, ⟨hf, -⟩, rfl⟩ := h1
    obtain ⟨g, ⟨hg, -⟩, hg'⟩ := h2
    exact hg (Prod.ext_iff.mp hg').1
  have hsub : S1 ∪ S2 ⊆ (Finset.univ : Finset L).offDiag := by
    intro ef h
    rw [Finset.mem_offDiag]
    rcases Finset.mem_union.mp h with h | h
    · simp only [S1, Finset.mem_image, Finset.mem_erase] at h
      obtain ⟨f, ⟨hf, -⟩, rfl⟩ := h
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun h => hf h.symm⟩
    · simp only [S2, Finset.mem_image, Finset.mem_erase] at h
      obtain ⟨f, ⟨hf, -⟩, rfl⟩ := h
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, hf⟩
  have hle : ∑ ef ∈ S1 ∪ S2, p ef.1 ef.2 ≤ ∑ ef ∈ (Finset.univ : Finset L).offDiag, p ef.1 ef.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ef _ _ => hp _ _
  rw [Finset.sum_union hdisj, hS1, hS2] at hle
  have : B * ∑ f, p e f ≤ B * ((1 / 2) * ∑ ef ∈ (Finset.univ : Finset L).offDiag, p ef.1 ef.2) :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  linarith

end Signed

end RiskRouting.Combined
