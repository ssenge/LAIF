import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exponent arithmetic of Theorem 1

`a_d = 1 / (2 d + 2)`. The nested recursion, with the rounding of `k` and of the block sizes:

`T_0(r, c) ≤ √(r c)`,
`T_{d+1}(r, c) ≤ √(k (c + k)) + C √(Σ_i T_d(r_i, c_i)²)`,

where `r^{1/(d+2)} ≤ k ≤ 2 r^{1/(d+2)}`, there are at most `k + 1` blocks, `r_i ≤ 2 r / k`, and
`Σ c_i ≤ c + k`. `nested_bound` solves it for every depth:

`T_d(r, c) ≤ A^d √(c + r) r^{a_d}`, with `A = 2 + 4 C`.

The recursion itself is a hypothesis on `T`. Nothing here models variable-time search, which is the
source of `C` in the notes.
-/

namespace Monge

/-- `a_d = 1 / (2 d + 2)`. -/
noncomputable def expo (d : ℕ) : ℝ := 1 / (2 * (d : ℝ) + 2)

theorem expo_zero : expo 0 = 1 / 2 := by norm_num [expo]

theorem expo_pos (d : ℕ) : 0 < expo d := by
  unfold expo
  positivity

theorem expo_le_half (d : ℕ) : expo d ≤ 1 / 2 := by
  unfold expo
  apply one_div_le_one_div_of_le (by norm_num)
  have : (0 : ℝ) ≤ d := by positivity
  linarith

/-- The exponent identity of the proof: `(1 - 1 / (d + 1)) · 1 / (2 d) = 1 / (2 d + 2)` for `d ≥ 1`,
written here with `d + 1` in place of `d`. -/
theorem expo_step (d : ℕ) : (1 - 1 / ((d : ℝ) + 2)) * expo d = expo (d + 1) := by
  unfold expo
  push_cast
  have h1 : (d : ℝ) + 2 ≠ 0 := by positivity
  have h2 : 2 * (d : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 2 * ((d : ℝ) + 1) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- With `k = r^{1/(d+1)}`, the bisection term has exponent `1 / (2 d + 2)`. -/
theorem expo_first (d : ℕ) : (1 / 2) * (1 / ((d : ℝ) + 1)) = expo d := by
  unfold expo
  have h1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (d : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- The exponents at depths `1` and `2`: `n^{1/4}` and `n^{1/6}` on top of `√n`. So depth `1` gives
`n^{3/4}`. -/
theorem expo_one : expo 1 = 1 / 4 := by norm_num [expo]

theorem expo_two : expo 2 = 1 / 6 := by norm_num [expo]

/-- The bound of Theorem 1, with explicit base `A`. -/
noncomputable def nestedBound (A : ℝ) (d : ℕ) (r c : ℝ) : ℝ :=
  A ^ d * √(c + r) * r ^ expo d

/-- The recursion at one depth: a block family with the rounding allowed above. -/
def NestedStep (C : ℝ) (T : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (d : ℕ) (r c : ℝ), 1 ≤ r → 0 ≤ c → ∃ (k : ℝ) (m : ℕ) (rb cb : Fin m → ℝ),
    r ^ (1 / ((d : ℝ) + 2)) ≤ k ∧ k ≤ 2 * r ^ (1 / ((d : ℝ) + 2)) ∧ (m : ℝ) ≤ k + 1 ∧
    (∀ i, 1 ≤ rb i ∧ rb i ≤ 2 * r / k ∧ 0 ≤ cb i) ∧ ∑ i, cb i ≤ c + k ∧
    T (d + 1) r c ≤ √(k * (c + k)) + C * √(∑ i, T d (rb i) (cb i) ^ 2)

/-- One step of the induction. -/
theorem nested_step {C A : ℝ} {T : ℕ → ℝ → ℝ → ℝ} (hC : 0 ≤ C) (hA : A = 2 + 4 * C)
    (hT0 : ∀ d r c, 0 ≤ T d r c) (hstep : NestedStep C T) (d : ℕ)
    (ih : ∀ r c, 1 ≤ r → 0 ≤ c → T d r c ≤ nestedBound A d r c) (r c : ℝ) (hr : 1 ≤ r)
    (hc : 0 ≤ c) : T (d + 1) r c ≤ nestedBound A (d + 1) r c := by
  obtain ⟨k, m, rb, cb, hk1, hk2, hm, hb, hsum, hT⟩ := hstep d r c hr hc
  have hr0 : 0 < r := by linarith
  have hA2 : 2 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  set e : ℝ := 1 / ((d : ℝ) + 2) with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one hd]
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  set ρ := r ^ e with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hr he0
  have hρr : ρ ≤ r := by
    have := Real.rpow_le_rpow_of_exponent_le hr he1
    rwa [Real.rpow_one] at this
  have hk0 : 0 < k := by linarith
  have hk1' : 1 ≤ k := by linarith
  have hk2r : k ≤ 2 * r := by linarith
  -- the exponent of the bisection term
  set a' := expo (d + 1) with ha'
  have hsqrtρ : √ρ = r ^ a' := by
    rw [Real.sqrt_eq_rpow, hρ, ← Real.rpow_mul hr0.le]
    congr 1
    have h := expo_first (d + 1)
    push_cast at h
    rw [he, ha', ← h]
    ring_nf
  have hra' : 0 < r ^ a' := Real.rpow_pos_of_pos hr0 _
  set W := √(c + r) with hW
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hW2 : W ^ 2 = c + r := Real.sq_sqrt (by linarith)
  -- the bisection term
  have hfirst : √(k * (c + k)) ≤ 2 * r ^ a' * W := by
    have h1 : k * (c + k) ≤ (2 * ρ) * (2 * (c + r)) := by
      apply mul_le_mul hk2 _ (by linarith) (by linarith)
      linarith
    have h2 : (2 * ρ) * (2 * (c + r)) = (2 * r ^ a' * W) ^ 2 := by
      rw [mul_pow, mul_pow, hW2, ← hsqrtρ, Real.sq_sqrt (by linarith)]
      ring
    rw [h2] at h1
    exact Real.sqrt_le_iff.mpr ⟨by positivity, h1⟩
  -- the recursive term: the exponent on each block
  set a := expo d with ha
  have ha0 : 0 < a := expo_pos d
  have hbase : 2 * r / k ≤ 2 * r ^ (1 - e) := by
    have h1 : r ^ (1 - e) * ρ = r := by
      rw [hρ, ← Real.rpow_add hr0]
      simp
    rw [div_le_iff₀ hk0]
    calc 2 * r = 2 * (r ^ (1 - e) * ρ) := by rw [h1]
      _ ≤ 2 * r ^ (1 - e) * k := by nlinarith [Real.rpow_pos_of_pos hr0 (1 - e)]
  have hpower : (2 * r ^ (1 - e)) ^ a ≤ √2 * r ^ a' := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hr0.le _), ← Real.rpow_mul hr0.le]
    have h1 : (1 - e) * a = a' := by
      rw [he, ha, ha']
      exact expo_step d
    rw [h1]
    apply mul_le_mul_of_nonneg_right _ hra'.le
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (expo_le_half d)
  have hblock : ∀ i, T d (rb i) (cb i) ^ 2 ≤
      (A ^ d * (√2 * r ^ a')) ^ 2 * (cb i + 2 * r / k) := by
    intro i
    obtain ⟨hb1, hb2, hb3⟩ := hb i
    have hb0 : 0 ≤ rb i := by linarith
    have h1 : T d (rb i) (cb i) ≤ nestedBound A d (rb i) (cb i) := ih _ _ hb1 hb3
    have h2 : (rb i) ^ a ≤ √2 * r ^ a' :=
      (Real.rpow_le_rpow hb0 (hb2.trans hbase) ha0.le).trans hpower
    have h3 : nestedBound A d (rb i) (cb i) ≤
        A ^ d * √(cb i + rb i) * (√2 * r ^ a') := by
      unfold nestedBound
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 := pow_le_pow_left₀ (hT0 _ _ _) (h1.trans h3) 2
    refine h4.trans ?_
    have h5 : (A ^ d * √(cb i + rb i) * (√2 * r ^ a')) ^ 2 =
        (A ^ d * (√2 * r ^ a')) ^ 2 * (cb i + rb i) := by
      rw [show A ^ d * √(cb i + rb i) * (√2 * r ^ a') =
        A ^ d * (√2 * r ^ a') * √(cb i + rb i) by ring, mul_pow _ (√(cb i + rb i)),
        Real.sq_sqrt (by linarith)]
    rw [h5]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith
  -- the sum over blocks: `c + k + (k + 1) (2 r / k) ≤ 6 (c + r)`
  have hsumblocks : ∑ i, T d (rb i) (cb i) ^ 2 ≤ (A ^ d * (√2 * r ^ a')) ^ 2 * (6 * (c + r)) := by
    calc ∑ i, T d (rb i) (cb i) ^ 2
        ≤ ∑ i, (A ^ d * (√2 * r ^ a')) ^ 2 * (cb i + 2 * r / k) :=
          Finset.sum_le_sum fun i _ => hblock i
      _ = (A ^ d * (√2 * r ^ a')) ^ 2 * (∑ i, cb i + m * (2 * r / k)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp
      _ ≤ (A ^ d * (√2 * r ^ a')) ^ 2 * (6 * (c + r)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have hq : 0 ≤ 2 * r / k := by positivity
          have h1 : (m : ℝ) * (2 * r / k) ≤ (k + 1) * (2 * r / k) :=
            mul_le_mul_of_nonneg_right hm hq
          have h2 : (k + 1) * (2 * r / k) = 2 * r + 2 * r / k := by
            field_simp
          have h3 : 2 * r / k ≤ 2 * r := by
            rw [div_le_iff₀ hk0]
            nlinarith
          linarith
  have hsecond : √(∑ i, T d (rb i) (cb i) ^ 2) ≤ A ^ d * (√2 * r ^ a') * (√6 * W) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    calc ∑ i, T d (rb i) (cb i) ^ 2 ≤ (A ^ d * (√2 * r ^ a')) ^ 2 * (6 * (c + r)) := hsumblocks
      _ = (A ^ d * (√2 * r ^ a') * (√6 * W)) ^ 2 := by
          rw [mul_pow _ (√6 * W), mul_pow √6 W, h6, hW2]
  -- combine: `2 + C √12 A^d ≤ A^(d+1)`
  have h12 : √2 * √6 ≤ 4 := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hAd : 1 ≤ A ^ d := one_le_pow₀ (by linarith)
  have hconst : 2 + C * (A ^ d * (√2 * √6)) ≤ A ^ (d + 1) := by
    have h1 : C * (A ^ d * (√2 * √6)) ≤ C * (A ^ d * 4) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h12 (by positivity)) hC
    rw [pow_succ, hA] at *
    nlinarith
  unfold nestedBound
  have hfinal : √(k * (c + k)) + C * √(∑ i, T d (rb i) (cb i) ^ 2) ≤
      (2 + C * (A ^ d * (√2 * √6))) * (W * r ^ a') := by
    have h1 := mul_le_mul_of_nonneg_left hsecond hC
    have : (2 + C * (A ^ d * (√2 * √6))) * (W * r ^ a') =
        2 * r ^ a' * W + C * (A ^ d * (√2 * r ^ a') * (√6 * W)) := by ring
    rw [this]
    linarith
  calc T (d + 1) r c ≤ _ := hT
    _ ≤ _ := hfinal
    _ ≤ A ^ (d + 1) * (W * r ^ a') :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = A ^ (d + 1) * W * r ^ a' := by ring

/-- **Theorem 1's arithmetic, all depths.** If `T_0(r, c) ≤ √(r c)` and `T` obeys the nested recursion
with overhead `C`, then `T_d(r, c) ≤ (2 + 4 C)^d √(c + r) r^{1/(2 d + 2)}` for all `d`, `r ≥ 1`, and
`c ≥ 0`. -/
theorem nested_bound {C : ℝ} {T : ℕ → ℝ → ℝ → ℝ} (hC : 0 ≤ C) (hT0 : ∀ d r c, 0 ≤ T d r c)
    (hbase : ∀ r c, 1 ≤ r → 0 ≤ c → T 0 r c ≤ √(r * c)) (hstep : NestedStep C T) (d : ℕ)
    (r c : ℝ) (hr : 1 ≤ r) (hc : 0 ≤ c) :
    T d r c ≤ (2 + 4 * C) ^ d * √(c + r) * r ^ (1 / (2 * (d : ℝ) + 2)) := by
  have key : ∀ d r c, 1 ≤ r → 0 ≤ c → T d r c ≤ nestedBound (2 + 4 * C) d r c := by
    intro d
    induction d with
    | zero =>
      intro r c hr hc
      refine (hbase r c hr hc).trans ?_
      have hr0 : 0 < r := by linarith
      unfold nestedBound
      rw [expo_zero, pow_zero, one_mul, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by linarith)]
      apply Real.sqrt_le_sqrt
      nlinarith
    | succ d ih =>
      exact nested_step hC rfl hT0 hstep d ih
  exact key d r c hr hc

/-- Depth one, square input: `n^{3/4}` up to the constant. -/
theorem nested_bound_depth_one {C : ℝ} {T : ℕ → ℝ → ℝ → ℝ} (hC : 0 ≤ C) (hT0 : ∀ d r c, 0 ≤ T d r c)
    (hbase : ∀ r c, 1 ≤ r → 0 ≤ c → T 0 r c ≤ √(r * c)) (hstep : NestedStep C T) (n : ℝ)
    (hn : 1 ≤ n) : T 1 n n ≤ (2 + 4 * C) * √2 * n ^ (3 / 4 : ℝ) := by
  have h := nested_bound hC hT0 hbase hstep 1 n n hn (by linarith)
  have hn0 : 0 < n := by linarith
  have h1 : √(n + n) = √2 * n ^ (1 / 2 : ℝ) := by
    rw [← two_mul, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow n]
  have h2 : n ^ (1 / 2 : ℝ) * n ^ (1 / 4 : ℝ) = n ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hn0]
    norm_num
  refine h.trans (le_of_eq ?_)
  rw [h1, pow_one]
  norm_num
  rw [show (2 + 4 * C) * (√2 * n ^ (1 / 2 : ℝ)) * n ^ (1 / 4 : ℝ) =
    (2 + 4 * C) * √2 * (n ^ (1 / 2 : ℝ) * n ^ (1 / 4 : ℝ)) by ring, h2]

end Monge
