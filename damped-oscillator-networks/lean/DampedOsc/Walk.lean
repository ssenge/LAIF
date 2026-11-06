import DampedOsc.Mode

/-!
# The random-walk form of strongly damped dynamics

For a mode with `ℓ = λ/γ²`, the position response `F = Gd + 2G` to a unit initial displacement is a power
series in `β = 1 - ℓ` with the nonnegative weights `w_k(τ) = e^{-τ} (τ^{2k}/(2k)! + τ^{2k+1}/(2k+1)!)`, which
are the probabilities that a Poisson variable of mean `τ` has `⌊N/2⌋ = k`. The same holds for
`G = Σ_k e^{-τ} τ^{2k+1}/(2k+1)! β^k`. Applied to the matrix `P = I - M^{-1}K/γ²`, whose eigenvalues are the
`β`, this gives `x(t) = E[P^{⌊N/2⌋} x₀ + 1{N odd} P^{(N-1)/2} ẋ₀/γ]`.

This file proves the scalar series in the overdamped (`β = ρ² > 0`) and underdamped (`β = -ω² < 0`) cases,
that the weights are nonnegative and sum to one, and that `P` is entrywise nonnegative with row sums at most
one when every diagonal stiffness satisfies `K_jj ≤ m_j γ²`.
-/

open Real Nat

namespace DampedOsc

/-- Weight of `β^k` in the position response to an initial displacement. -/
noncomputable def wx (τ : ℝ) (k : ℕ) : ℝ :=
  exp (-τ) * (τ ^ (2 * k) / (2 * k)! + τ ^ (2 * k + 1) / (2 * k + 1)!)

/-- Weight of `β^k` in the position response to an initial velocity (times `γ`). -/
noncomputable def wv (τ : ℝ) (k : ℕ) : ℝ := exp (-τ) * (τ ^ (2 * k + 1) / (2 * k + 1)!)

lemma wx_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) : 0 ≤ wx τ k := by unfold wx; positivity

lemma wv_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) : 0 ≤ wv τ k := by unfold wv; positivity

lemma exp_one_sub (τ ρ : ℝ) : exp (-(τ * (1 - ρ))) = exp (-τ) * exp (τ * ρ) := by
  rw [← exp_add]; ring_nf

lemma exp_one_add (τ ρ : ℝ) : exp (-(τ * (1 + ρ))) = exp (-τ) * exp (-(τ * ρ)) := by
  rw [← exp_add]; ring_nf

/-- Overdamped: `Gd + 2G = Σ_k w_k(τ) (ρ²)^k`. -/
theorem hasSum_wx_over (τ ρ : ℝ) (hρ : ρ ≠ 0) :
    HasSum (fun k => wx τ k * (ρ ^ 2) ^ k) (Gdover ρ τ + 2 * Gover ρ τ) := by
  have h := ((hasSum_cosh (τ * ρ)).add ((hasSum_sinh (τ * ρ)).div_const ρ)).mul_left (exp (-τ))
  convert h using 1
  · funext k
    unfold wx
    rw [mul_pow, mul_pow, ← pow_mul, pow_succ (ρ) (2 * k)]
    field_simp
  · unfold Gdover Gover
    rw [exp_one_sub, exp_one_add, cosh_eq, sinh_eq]
    field_simp
    ring

/-- Overdamped: `G = Σ_k e^{-τ} τ^{2k+1}/(2k+1)! (ρ²)^k`. -/
theorem hasSum_wv_over (τ ρ : ℝ) (hρ : ρ ≠ 0) :
    HasSum (fun k => wv τ k * (ρ ^ 2) ^ k) (Gover ρ τ) := by
  have h := ((hasSum_sinh (τ * ρ)).div_const ρ).mul_left (exp (-τ))
  convert h using 1
  · funext k
    unfold wv
    rw [mul_pow, ← pow_mul, pow_succ (ρ) (2 * k)]
    field_simp
  · unfold Gover
    rw [exp_one_sub, exp_one_add, sinh_eq]
    field_simp

/-- Underdamped: `Gd + 2G = Σ_k w_k(τ) (-ω²)^k`. -/
theorem hasSum_wx_under (τ ω : ℝ) (hω : ω ≠ 0) :
    HasSum (fun k => wx τ k * (-ω ^ 2) ^ k) (Gdunder ω τ + 2 * Gunder ω τ) := by
  have h := ((Real.hasSum_cos (τ * ω)).add ((Real.hasSum_sin (τ * ω)).div_const ω)).mul_left (exp (-τ))
  convert h using 1
  · funext k
    unfold wx
    rw [neg_pow, mul_pow, mul_pow, ← pow_mul, pow_succ (ω) (2 * k)]
    field_simp
  · unfold Gdunder Gunder
    ring

/-- Underdamped: `G = Σ_k e^{-τ} τ^{2k+1}/(2k+1)! (-ω²)^k`. -/
theorem hasSum_wv_under (τ ω : ℝ) (hω : ω ≠ 0) :
    HasSum (fun k => wv τ k * (-ω ^ 2) ^ k) (Gunder ω τ) := by
  have h := ((Real.hasSum_sin (τ * ω)).div_const ω).mul_left (exp (-τ))
  convert h using 1
  · funext k
    unfold wv
    rw [neg_pow, mul_pow, ← pow_mul, pow_succ (ω) (2 * k)]
    field_simp
  · unfold Gunder
    ring

/-- The displacement weights are a probability distribution: `Σ_k w_k(τ) = 1`. -/
theorem hasSum_wx_one (τ : ℝ) : HasSum (fun k => wx τ k) 1 := by
  have h := hasSum_wx_over τ 1 one_ne_zero
  have e : Gdover 1 τ + 2 * Gover 1 τ = 1 := by
    unfold Gdover Gover; simp; ring
  rw [e] at h
  simpa using h

/-! ### The walk matrix -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P = I - M^{-1} K / γ²` for masses `m` and stiffness matrix `K`. -/
noncomputable def walkMatrix (K : Matrix ι ι ℝ) (m : ι → ℝ) (γ : ℝ) : Matrix ι ι ℝ :=
  fun j k => (if j = k then 1 else 0) - K j k / (m j * γ ^ 2)

omit [Fintype ι] in
/-- If springs have nonpositive off-diagonal entries and the damping exceeds every clamped-node frequency,
`K_jj ≤ m_j γ²`, then `P` is entrywise nonnegative. -/
theorem walkMatrix_nonneg (K : Matrix ι ι ℝ) (m : ι → ℝ) (γ : ℝ) (hm : ∀ j, 0 < m j) (hγ : γ ≠ 0)
    (hoff : ∀ j k, j ≠ k → K j k ≤ 0) (hdiag : ∀ j, K j j ≤ m j * γ ^ 2) (j k : ι) :
    0 ≤ walkMatrix K m γ j k := by
  have hd : 0 < m j * γ ^ 2 := mul_pos (hm j) (by positivity)
  unfold walkMatrix
  by_cases h : j = k
  · subst h; simp only [ite_true]
    rw [sub_nonneg, div_le_one hd]; exact hdiag j
  · simp only [h, ite_false, zero_sub, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (hoff j k h) hd.le

/-- If every row of `K` has a nonnegative sum (walls have nonnegative stiffness), the rows of `P` sum to at
most one, so `P` is substochastic. -/
theorem walkMatrix_row_le (K : Matrix ι ι ℝ) (m : ι → ℝ) (γ : ℝ) (hm : ∀ j, 0 < m j) (hγ : γ ≠ 0)
    (hrow : ∀ j, 0 ≤ ∑ k, K j k) (j : ι) : ∑ k, walkMatrix K m γ j k ≤ 1 := by
  have hd : 0 < m j * γ ^ 2 := mul_pos (hm j) (by positivity)
  unfold walkMatrix
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have : 0 ≤ (∑ k, K j k) / (m j * γ ^ 2) := div_nonneg (hrow j) hd.le
  linarith

end DampedOsc
