import Mathlib

/-!
# Discrete Fejér weights on `ZMod N`

Write `ω` for `ZMod.stdAddChar`, so that `ω a = e(a / N)` with `e y = exp (2 π i y)`.

* `fejer m a = ‖∑_{j<m} ω (j a)‖² / (m N)` is a probability distribution on `ZMod N` for `m ≤ N`;
* `fejerHat m k` is its Fourier transform, the normalized number of `(j, j')` with `j - j' + k = 0`. It is
  nonnegative, vanishes unless `|valMinAbs k| < m`, and sums to `m`;
* `sum_fejer_tail`, `sum_prod_fejer_tail`: tail bounds for one coordinate and for the product distribution.
-/

open Finset

namespace CutQuery

section Fejer

variable {N : ℕ} [NeZero N]

/-- The sum `∑_{j<m} ω (j a)`. -/
noncomputable def fejerSum (m : ℕ) (a : ZMod N) : ℂ :=
  ∑ j ∈ range m, ZMod.stdAddChar ((j : ZMod N) * a)

/-- The weight `‖∑_{j<m} ω (j a)‖² / (m N)`. -/
noncomputable def fejer (m : ℕ) (a : ZMod N) : ℝ := ‖fejerSum m a‖ ^ 2 / (m * N)

/-- The transform of `fejer`: the number of `(j, j') ∈ [m]²` with `j - j' + k = 0`, divided by `m`. -/
noncomputable def fejerHat (m : ℕ) (k : ZMod N) : ℝ :=
  (((range m ×ˢ range m).filter fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + k = 0).card : ℝ) / m

theorem fejer_nonneg (m : ℕ) (a : ZMod N) : 0 ≤ fejer m a := by
  unfold fejer; positivity

omit [NeZero N] in
theorem fejerHat_nonneg (m : ℕ) (k : ZMod N) : 0 ≤ fejerHat m k := by
  unfold fejerHat; positivity

theorem norm_char (a : ZMod N) : ‖(ZMod.stdAddChar a : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; simp

theorem sq_norm_fejerSum (m : ℕ) (a : ZMod N) :
    ((‖fejerSum m a‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ range m ×ˢ range m, ZMod.stdAddChar (((p.1 : ZMod N) - (p.2 : ZMod N)) * a) := by
  have h : ((‖fejerSum m a‖ ^ 2 : ℝ) : ℂ) = fejerSum m a * (starRingEnd ℂ) (fejerSum m a) := by
    rw [Complex.mul_conj']; push_cast; rfl
  rw [h]
  unfold fejerSum
  rw [map_sum, sum_mul_sum, sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The Fourier transform of `fejer` is `fejerHat`. -/
theorem sum_fejer_mul_char {m : ℕ} (hm : 0 < m) (k : ZMod N) :
    ∑ a, (fejer m a : ℂ) * ZMod.stdAddChar (a * k) = (fejerHat m k : ℂ) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h : ∀ a : ZMod N, (fejer m a : ℂ) * ZMod.stdAddChar (a * k)
      = ((m : ℂ) * N)⁻¹ * ∑ p ∈ range m ×ˢ range m,
          ZMod.stdAddChar (a * ((p.1 : ZMod N) - (p.2 : ZMod N) + k)) := by
    intro a
    have h1 : (fejer m a : ℂ) = ((‖fejerSum m a‖ ^ 2 : ℝ) : ℂ) / ((m : ℂ) * N) := by
      unfold fejer; push_cast; rfl
    rw [h1, sq_norm_fejerSum, div_eq_inv_mul, mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h]
  rw [← mul_sum, sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  have h3 : ∑ x ∈ range m ×ˢ range m, (((if (x.1 : ZMod N) - (x.2 : ZMod N) + k = 0 then N else 0 : ℕ)) : ℂ)
      = (((range m ×ˢ range m).filter fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + k = 0).card : ℂ) * N := by
    push_cast
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  rw [h3]
  unfold fejerHat
  push_cast
  field_simp

omit [NeZero N] in
theorem fejerHat_zero {m : ℕ} (hm : 0 < m) (hmN : m ≤ N) : fejerHat m (0 : ZMod N) = 1 := by
  unfold fejerHat
  have hc : ((range m ×ˢ range m).filter fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + 0 = 0).card = m := by
    have : ((range m ×ˢ range m).filter fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + 0 = 0)
        = (range m).image fun i => (i, i) := by
      ext ⟨i, j⟩
      simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq, add_zero, sub_eq_zero]
      constructor
      · rintro ⟨⟨hi, hj⟩, h⟩
        have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
        rw [Nat.mod_eq_of_lt (hi.trans_le hmN), Nat.mod_eq_of_lt (hj.trans_le hmN)] at h'
        exact ⟨i, hi, rfl, h'⟩
      · rintro ⟨a, ha, rfl, rfl⟩
        exact ⟨⟨ha, ha⟩, rfl⟩
    rw [this, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), card_range]
  rw [hc]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- `fejer` has total mass one. -/
theorem sum_fejer {m : ℕ} (hm : 0 < m) (hmN : m ≤ N) : ∑ a : ZMod N, fejer m a = 1 := by
  have h := sum_fejer_mul_char (N := N) hm 0
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, fejerHat_zero hm hmN] at h
  exact_mod_cast h

/-- `fejerHat` sums to `m`. -/
theorem sum_fejerHat {m : ℕ} (hm : 0 < m) : ∑ k : ZMod N, fejerHat m k = m := by
  unfold fejerHat
  rw [← sum_div]
  have h : ∑ k : ZMod N, (((range m ×ˢ range m).filter
      fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + k = 0).card : ℝ) = (m : ℝ) * m := by
    have h1 : ∀ k : ZMod N, (((range m ×ˢ range m).filter
        fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + k = 0).card : ℝ)
        = ∑ p ∈ range m ×ˢ range m, if k = (p.2 : ZMod N) - p.1 then (1 : ℝ) else 0 := by
      intro k
      rw [card_filter]
      push_cast
      refine sum_congr rfl fun p _ => ?_
      have : ((p.1 : ZMod N) - p.2 + k = 0) ↔ k = (p.2 : ZMod N) - p.1 := by
        constructor
        · intro h; linear_combination h
        · intro h; rw [h]; ring
      simp only [this]
    simp_rw [h1]
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_product, card_range, nsmul_eq_mul,
      mul_one]
    push_cast
    ring
  rw [h]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- `fejerHat m k` vanishes unless `|valMinAbs k| < m`. -/
theorem abs_valMinAbs_lt_of_fejerHat_ne_zero {m : ℕ} (hmN : 2 * m ≤ N) {k : ZMod N}
    (h : fejerHat m k ≠ 0) : |k.valMinAbs| < m := by
  have hc : ((range m ×ˢ range m).filter fun p : ℕ × ℕ => (p.1 : ZMod N) - p.2 + k = 0).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    apply h
    unfold fejerHat
    rw [hne]
    simp
  obtain ⟨⟨i, j⟩, hp⟩ := hc
  simp only [mem_filter, mem_product, mem_range] at hp
  obtain ⟨⟨hi, hj⟩, he⟩ := hp
  have hk : k = (((j : ℤ) - i : ℤ) : ZMod N) := by
    push_cast
    linear_combination he
  have hv : k.valMinAbs = (j : ℤ) - i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨hk, ?_, ?_⟩ <;> omega
  rw [hv, abs_lt]
  constructor <;> omega

theorem char_eq_exp (a : ZMod N) :
    (ZMod.stdAddChar a : ℂ)
      = Complex.exp (Complex.I * ((2 * Real.pi * a.valMinAbs / N : ℝ) : ℂ)) := by
  conv_lhs => rw [← ZMod.coe_valMinAbs a]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- `4 |r| / N ≤ ‖1 - e(r / N)‖` for `r = valMinAbs a`. -/
theorem le_norm_char_sub_one (a : ZMod N) :
    4 * |(a.valMinAbs : ℝ)| / N ≤ ‖(ZMod.stdAddChar a : ℂ) - 1‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpi := Real.pi_pos
  rw [char_eq_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  set r : ℝ := (a.valMinAbs : ℝ) with hr
  have hrle : 2 * |r| ≤ N := by
    have h1 := a.natAbs_valMinAbs_le
    have h2 : 2 * a.valMinAbs.natAbs ≤ N := by omega
    have h3 : |r| = (a.valMinAbs.natAbs : ℝ) := by
      rw [hr, Nat.cast_natAbs]
      push_cast
      rfl
    rw [h3]
    exact_mod_cast h2
  have hy : 2 * Real.pi * r / N / 2 = Real.pi * r / N := by ring
  rw [hy]
  have habs : |Real.pi * r / N| = Real.pi * |r| / N := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hNpos]
  have hle : |Real.pi * r / N| ≤ Real.pi / 2 := by
    rw [habs, div_le_div_iff₀ hNpos (by norm_num)]
    nlinarith
  have h1 := Real.mul_le_sin (abs_nonneg _) hle
  have h2 := Real.abs_sin_eq_sin_abs_of_abs_le_pi (hle.trans (by linarith))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), h2]
  have h3 : 2 / Real.pi * |Real.pi * r / N| = 2 * |r| / N := by
    rw [habs]
    field_simp
  rw [h3] at h1
  have h4 : 4 * |r| / N = 2 * (2 * |r| / N) := by ring
  rw [h4]
  linarith

/-- `‖∑_{j<m} ω (j a)‖ ≤ 2 / ‖1 - ω a‖`. -/
theorem norm_fejerSum_le (m : ℕ) (a : ZMod N) (ha : (ZMod.stdAddChar a : ℂ) ≠ 1) :
    ‖fejerSum m a‖ ≤ 2 / ‖(ZMod.stdAddChar a : ℂ) - 1‖ := by
  have h : fejerSum m a = ∑ j ∈ range m, (ZMod.stdAddChar a : ℂ) ^ j := by
    unfold fejerSum
    refine sum_congr rfl fun j _ => ?_
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  rw [h, geom_sum_eq ha, norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖(ZMod.stdAddChar a : ℂ) ^ m - 1‖ ≤ ‖(ZMod.stdAddChar a : ℂ) ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_char]; norm_num

/-- For `r = valMinAbs a ≠ 0`, `fejer m a ≤ N / (4 m r²)`. -/
theorem fejer_le {m : ℕ} (hm : 0 < m) (a : ZMod N) (hr : a.valMinAbs ≠ 0) :
    fejer m a ≤ N / (4 * m * (a.valMinAbs : ℝ) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hrpos : 0 < |(a.valMinAbs : ℝ)| := abs_pos.mpr (by exact_mod_cast hr)
  set r : ℝ := |(a.valMinAbs : ℝ)| with hrdef
  have hd := le_norm_char_sub_one a
  rw [← hrdef] at hd
  have hdpos : 0 < ‖(ZMod.stdAddChar a : ℂ) - 1‖ := lt_of_lt_of_le (by positivity) hd
  have hne : (ZMod.stdAddChar a : ℂ) ≠ 1 := by
    intro h
    rw [h] at hdpos
    simp at hdpos
  have hS := norm_fejerSum_le m a hne
  have hS2 : ‖fejerSum m a‖ ≤ N / (2 * r) := by
    refine hS.trans ?_
    rw [div_le_div_iff₀ hdpos (by positivity)]
    have : 4 * r ≤ ‖(ZMod.stdAddChar a : ℂ) - 1‖ * N := by
      rwa [div_le_iff₀ hNpos] at hd
    linarith
  have hsq : (a.valMinAbs : ℝ) ^ 2 = r ^ 2 := by rw [hrdef, sq_abs]
  rw [hsq]
  unfold fejer
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ‖fejerSum m a‖ ^ 2 ≤ (N / (2 * r)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS2 2
  have h2 : (N / (2 * r)) ^ 2 * (4 * m * r ^ 2) = N * (m * N) := by
    field_simp
    ring
  calc ‖fejerSum m a‖ ^ 2 * (4 * m * r ^ 2) ≤ (N / (2 * r)) ^ 2 * (4 * m * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = N * (m * N) := h2

theorem sum_Ioc_inv_sq_le {L : ℕ} (hL : 0 < L) (M : ℕ) (hM : L ≤ M) :
    ∑ r ∈ Ioc L M, 1 / (r : ℝ) ^ 2 ≤ 1 / (L : ℝ) - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hL.trans_le hM
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hM, sum_insert (by simp)]
    have h : 1 / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hM0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private theorem sum_one_side {L : ℕ} (hL : 0 < L) (s : Finset (ZMod N)) (hs : ∀ a ∈ s, L < a.valMinAbs.natAbs)
    (hi : Set.InjOn (fun a : ZMod N => a.valMinAbs.natAbs) s) :
    ∑ a ∈ s, 1 / ((a.valMinAbs.natAbs : ℕ) : ℝ) ^ 2 ≤ 1 / (L : ℝ) := by
  have h1 : ∑ a ∈ s, 1 / ((a.valMinAbs.natAbs : ℕ) : ℝ) ^ 2
      = ∑ r ∈ s.image (fun a : ZMod N => a.valMinAbs.natAbs), 1 / (r : ℝ) ^ 2 := by
    rw [sum_image hi]
  rw [h1]
  have hsub : s.image (fun a : ZMod N => a.valMinAbs.natAbs) ⊆ Ioc L (L + N) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
    have := a.natAbs_valMinAbs_le
    have := hs a ha
    simp only [mem_Ioc]
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  refine (sum_Ioc_inv_sq_le hL _ (by omega)).trans ?_
  have : (0 : ℝ) ≤ 1 / ((L + N : ℕ) : ℝ) := by positivity
  linarith

theorem sum_inv_sq_tail {L : ℕ} (hL : 0 < L) :
    ∑ a ∈ univ.filter (fun a : ZMod N => L < a.valMinAbs.natAbs), 1 / ((a.valMinAbs.natAbs : ℕ) : ℝ) ^ 2
      ≤ 2 / (L : ℝ) := by
  set s := univ.filter (fun a : ZMod N => L < a.valMinAbs.natAbs)
  have hsplit := sum_filter_add_sum_filter_not s (fun a : ZMod N => 0 < a.valMinAbs)
    (fun a => 1 / ((a.valMinAbs.natAbs : ℕ) : ℝ) ^ 2)
  rw [← hsplit]
  have hmem : ∀ (p : ZMod N → Prop) [DecidablePred p], ∀ a ∈ s.filter p, L < a.valMinAbs.natAbs := by
    intro p _ a ha
    exact (mem_filter.mp (mem_filter.mp ha).1).2
  have h1 := sum_one_side hL (s.filter fun a : ZMod N => 0 < a.valMinAbs) (hmem _) (by
    intro a ha c hc he
    have ha' := (mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hc' := (mem_filter.mp (Finset.mem_coe.mp hc)).2
    apply ZMod.injective_valMinAbs
    simp only at he
    omega)
  have h2 := sum_one_side hL (s.filter fun a : ZMod N => ¬ 0 < a.valMinAbs) (hmem _) (by
    intro a ha c hc he
    have ha' := (mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hc' := (mem_filter.mp (Finset.mem_coe.mp hc)).2
    apply ZMod.injective_valMinAbs
    simp only at he
    omega)
  have : 2 / (L : ℝ) = 1 / (L : ℝ) + 1 / (L : ℝ) := by ring
  linarith

/-- `Pr[|valMinAbs a| > L] ≤ N / (2 m L)`. -/
theorem sum_fejer_tail {m L : ℕ} (hm : 0 < m) (hL : 0 < L) :
    ∑ a ∈ univ.filter (fun a : ZMod N => L < a.valMinAbs.natAbs), fejer m a ≤ N / (2 * m * L) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : ∀ a ∈ univ.filter (fun a : ZMod N => L < a.valMinAbs.natAbs),
      fejer m a ≤ (N / (4 * m)) * (1 / ((a.valMinAbs.natAbs : ℕ) : ℝ) ^ 2) := by
    intro a ha
    have ha' := (mem_filter.mp ha).2
    have hr : a.valMinAbs ≠ 0 := by
      intro h
      rw [h] at ha'
      simp at ha'
    have h2 := fejer_le hm a hr
    have h3 : ((a.valMinAbs.natAbs : ℕ) : ℝ) ^ 2 = (a.valMinAbs : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs]
      push_cast
      exact sq_abs _
    rw [h3, div_mul_div_comm, mul_one]
    exact h2
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  calc N / (4 * (m : ℝ)) * _ ≤ N / (4 * (m : ℝ)) * (2 / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_tail hL) (by positivity)
    _ = N / (2 * m * L) := by
        field_simp
        ring

end Fejer

section Product

variable {N : ℕ} [NeZero N] {I : Type*} [Fintype I] [DecidableEq I]

/-- A sum over tuples of a product of coordinate functions factors. -/
theorem sum_prod_apply (f : I → ZMod N → ℂ) :
    ∑ c : I → ZMod N, ∏ j, f j (c j) = ∏ j, ∑ a, f j a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem sum_prod_apply_real (f : I → ZMod N → ℝ) :
    ∑ c : I → ZMod N, ∏ j, f j (c j) = ∏ j, ∑ a, f j a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The product distribution has total mass one. -/
theorem sum_prod_fejer {m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ c : I → ZMod N, ∏ j, fejer m (c j) = 1 := by
  rw [sum_prod_apply_real (fun _ a => fejer m a)]
  simp [sum_fejer hm hmN]

omit [DecidableEq I] in
theorem prod_fejer_nonneg (m : ℕ) (c : I → ZMod N) : 0 ≤ ∏ j, fejer m (c j) :=
  prod_nonneg fun _ _ => fejer_nonneg _ _

/-- The mass of `{c : |valMinAbs (c j)| > L}` for one coordinate `j`. -/
theorem sum_prod_fejer_coord {m L : ℕ} (hm : 0 < m) (hmN : m ≤ N) (hL : 0 < L) (j : I) :
    ∑ c : I → ZMod N, (∏ i, fejer m (c i)) * (if L < (c j).valMinAbs.natAbs then 1 else 0)
      ≤ N / (2 * m * L) := by
  have h : ∀ c : I → ZMod N, (∏ i, fejer m (c i)) * (if L < (c j).valMinAbs.natAbs then (1 : ℝ) else 0)
      = ∏ i, (fejer m (c i) * if i = j then (if L < (c i).valMinAbs.natAbs then (1 : ℝ) else 0) else 1) := by
    intro c
    rw [prod_mul_distrib, Finset.prod_ite_eq' univ j]
    simp
  simp_rw [h]
  rw [sum_prod_apply_real (fun i a => fejer m a *
    if i = j then (if L < a.valMinAbs.natAbs then (1 : ℝ) else 0) else 1)]
  have h2 : ∀ i, ∑ a : ZMod N, (fejer m a *
      if i = j then (if L < a.valMinAbs.natAbs then (1 : ℝ) else 0) else 1)
      = if i = j then ∑ a ∈ univ.filter (fun a : ZMod N => L < a.valMinAbs.natAbs), fejer m a else 1 := by
    intro i
    by_cases hi : i = j
    · simp only [hi, ↓reduceIte, sum_filter]
      refine sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    · simp only [hi, ↓reduceIte, mul_one, sum_fejer hm hmN]
  simp_rw [h2]
  rw [Finset.prod_ite_eq' univ j]
  simpa using sum_fejer_tail hm hL

/-- The union bound: `Pr[∃ j, |valMinAbs (c j)| > L] ≤ J N / (2 m L)`. -/
theorem sum_prod_fejer_tail {m L : ℕ} (hm : 0 < m) (hmN : m ≤ N) (hL : 0 < L) :
    ∑ c : I → ZMod N, (∏ i, fejer m (c i)) * (if ∃ j, L < (c j).valMinAbs.natAbs then 1 else 0)
      ≤ Fintype.card I * (N / (2 * m * L)) := by
  have h1 : ∀ c : I → ZMod N,
      (∏ i, fejer m (c i)) * (if ∃ j, L < (c j).valMinAbs.natAbs then (1 : ℝ) else 0)
      ≤ ∑ j, (∏ i, fejer m (c i)) * (if L < (c j).valMinAbs.natAbs then (1 : ℝ) else 0) := by
    intro c
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (prod_fejer_nonneg m c)
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      calc (1 : ℝ) = if L < (c j).valMinAbs.natAbs then (1 : ℝ) else 0 := by simp [hj]
        _ ≤ _ := single_le_sum (f := fun j => if L < (c j).valMinAbs.natAbs then (1 : ℝ) else 0)
            (fun _ _ => by positivity) (mem_univ j)
    · exact sum_nonneg fun _ _ => by positivity
  refine (sum_le_sum fun c _ => h1 c).trans ?_
  rw [sum_comm]
  calc ∑ j : I, ∑ c : I → ZMod N, (∏ i, fejer m (c i)) * (if L < (c j).valMinAbs.natAbs then (1 : ℝ) else 0)
      ≤ ∑ _j : I, (N / (2 * m * L) : ℝ) := sum_le_sum fun j _ => sum_prod_fejer_coord hm hmN hL j
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ]

end Product

end CutQuery
