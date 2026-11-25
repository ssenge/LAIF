import Mathlib

/-!
# Second moment of unbiased linear estimators

A randomized design picks the index `r` with probability `p r` and then sums `w r t · m t` over the tuples `t ∈ A r`,
where the `m t` are orthonormal monomials (products of one queried sign per function). Unbiasedness for every input
fixes the averaged coefficients: `∑ r, p r · [t ∈ A r] · w r t = c t`. Its average second moment is then at least
`(∑ t, |c t|)² / E |A r|`.

* `second_moment_ge`: `(∑ t, |c t|)² ≤ (∑ r, p r · |A r|) · ∑ r, p r · ∑_{t ∈ A r} (w r t)²`.
* `second_moment_ge_of_card_le`: with `|A r| ≤ M` for every `r` and `∑ r, p r = 1`, the second moment is at least
  `(∑ t, |c t|)² / M`.
* `sum_abs_sq_of_const`: if `(c t)² = γ ≥ 0` for all `t` in a type with `m` elements, then `(∑ t, |c t|)² = m² γ`.
* `cyclic_constant`: for `m = N^k` and `γ = 1 / N^(k+2)`, `m² γ = N^(k-2)` when `k ≥ 2` and `N > 0`.
* `second_moment_ge_tight`, `cyclic_constant_two_three`: instances that satisfy every hypothesis, with the bound
  attained.
-/

open Finset

namespace LinearEstimators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

theorem second_moment_ge (p : ι → ℝ) (hp : ∀ r, 0 ≤ p r) (A : ι → Finset α) (w : ι → α → ℝ)
    (c : α → ℝ) (hc : ∀ t, ∑ r, p r * (if t ∈ A r then w r t else 0) = c t) :
    (∑ t, |c t|) ^ 2 ≤ (∑ r, p r * ((A r).card : ℝ)) * ∑ r, p r * ∑ t ∈ A r, w r t ^ 2 := by
  have habs : ∀ r t, |p r * (if t ∈ A r then w r t else 0)| =
      if t ∈ A r then p r * |w r t| else 0 := by
    intro r t
    split_ifs <;> simp [abs_mul, abs_of_nonneg (hp r)]
  have h1 : ∑ t, |c t| ≤ ∑ x ∈ (univ : Finset ι).sigma A, p x.1 * |w x.1 x.2| := by
    rw [Finset.sum_sigma]
    calc ∑ t, |c t| = ∑ t, |∑ r, p r * (if t ∈ A r then w r t else 0)| := by simp only [hc]
      _ ≤ ∑ t, ∑ r, |p r * (if t ∈ A r then w r t else 0)| :=
          sum_le_sum fun t _ => abs_sum_le_sum_abs _ _
      _ = ∑ r, ∑ t, |p r * (if t ∈ A r then w r t else 0)| := sum_comm
      _ = ∑ r, ∑ t ∈ A r, p r * |w r t| := by
          simp_rw [habs, Finset.sum_ite_mem, univ_inter]
  have h2 : (∑ x ∈ (univ : Finset ι).sigma A, p x.1 * |w x.1 x.2|) ^ 2 ≤
      (∑ x ∈ (univ : Finset ι).sigma A, p x.1) *
        ∑ x ∈ (univ : Finset ι).sigma A, p x.1 * w x.1 x.2 ^ 2 := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun x _ => hp x.1)
      (fun x _ => mul_nonneg (hp x.1) (sq_nonneg _)) (fun x _ => ?_)
    rw [mul_pow, sq_abs]; nlinarith [hp x.1, sq_nonneg (w x.1 x.2)]
  have h3 : ∑ x ∈ (univ : Finset ι).sigma A, p x.1 = ∑ r, p r * ((A r).card : ℝ) := by
    rw [Finset.sum_sigma]; simp [sum_const, nsmul_eq_mul, mul_comm]
  have h4 : ∑ x ∈ (univ : Finset ι).sigma A, p x.1 * w x.1 x.2 ^ 2 =
      ∑ r, p r * ∑ t ∈ A r, w r t ^ 2 := by
    rw [Finset.sum_sigma]; simp [mul_sum]
  have h0 : 0 ≤ ∑ t, |c t| := sum_nonneg fun t _ => abs_nonneg _
  calc (∑ t, |c t|) ^ 2 ≤ (∑ x ∈ (univ : Finset ι).sigma A, p x.1 * |w x.1 x.2|) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2
    _ = _ := by rw [h3, h4]

theorem second_moment_ge_of_card_le (p : ι → ℝ) (hp : ∀ r, 0 ≤ p r) (hp1 : ∑ r, p r = 1)
    (A : ι → Finset α) (w : ι → α → ℝ) (c : α → ℝ)
    (hc : ∀ t, ∑ r, p r * (if t ∈ A r then w r t else 0) = c t) (M : ℝ) (hM : 0 < M)
    (hA : ∀ r, ((A r).card : ℝ) ≤ M) :
    (∑ t, |c t|) ^ 2 / M ≤ ∑ r, p r * ∑ t ∈ A r, w r t ^ 2 := by
  have h := second_moment_ge p hp A w c hc
  have hE : ∑ r, p r * ((A r).card : ℝ) ≤ M := by
    calc ∑ r, p r * ((A r).card : ℝ) ≤ ∑ r, p r * M :=
          sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hA r) (hp r)
      _ = M := by rw [← sum_mul, hp1, one_mul]
  have hS : 0 ≤ ∑ r, p r * ∑ t ∈ A r, w r t ^ 2 :=
    sum_nonneg fun r _ => mul_nonneg (hp r) (sum_nonneg fun t _ => sq_nonneg _)
  rw [div_le_iff₀ hM]
  nlinarith [mul_le_mul_of_nonneg_right hE hS]

omit [DecidableEq α] in
theorem sum_abs_sq_of_const (c : α → ℝ) (γ : ℝ) (hγ : 0 ≤ γ) (hc : ∀ t, c t ^ 2 = γ) :
    (∑ t, |c t|) ^ 2 = (Fintype.card α : ℝ) ^ 2 * γ := by
  have h : ∀ t, |c t| = Real.sqrt γ := fun t => by rw [← hc t, Real.sqrt_sq_eq_abs]
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  rw [mul_pow, Real.sq_sqrt hγ]

theorem cyclic_constant (N : ℝ) (hN : 0 < N) (k : ℕ) (hk : 2 ≤ k) :
    (N ^ k) ^ 2 * (1 / N ^ (k + 2)) = N ^ (k - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hNk : N ^ (j + 2 + 2) ≠ 0 := pow_ne_zero _ hN.ne'
  field_simp
  simp only [Nat.add_sub_cancel]
  ring

/-- Non-vacuity of `second_moment_ge` and `second_moment_ge_of_card_le`: one design that queries both tuples of
`Fin 2` with weights `c = 1` satisfies every hypothesis, and both sides of the bound equal `4 > 0`, so the
hypotheses are satisfiable and the bound is attained. -/
theorem second_moment_ge_tight :
    (∀ t : Fin 2, ∑ _r : Unit, (1 : ℝ) * (if t ∈ (univ : Finset (Fin 2)) then (1 : ℝ) else 0) = 1) ∧
    (∑ _t : Fin 2, |(1 : ℝ)|) ^ 2 =
      (∑ _r : Unit, (1 : ℝ) * ((univ : Finset (Fin 2)).card : ℝ)) *
        ∑ _r : Unit, (1 : ℝ) * ∑ _t ∈ (univ : Finset (Fin 2)), (1 : ℝ) ^ 2 ∧
    (∑ _t : Fin 2, |(1 : ℝ)|) ^ 2 / 2 = ∑ _r : Unit, (1 : ℝ) * ∑ _t ∈ (univ : Finset (Fin 2)), (1 : ℝ) ^ 2 ∧
    (0 : ℝ) < (∑ _t : Fin 2, |(1 : ℝ)|) ^ 2 := by
  refine ⟨fun t => by simp, ?_, ?_, ?_⟩ <;> norm_num

/-- Non-vacuity of `cyclic_constant`: for `N = 2` and `k = 3`, `(2^3)² / 2^5 = 2 = 2^1`. -/
theorem cyclic_constant_two_three : ((2 : ℝ) ^ 3) ^ 2 * (1 / 2 ^ (3 + 2)) = 2 ^ (3 - 2) := by norm_num

end LinearEstimators
