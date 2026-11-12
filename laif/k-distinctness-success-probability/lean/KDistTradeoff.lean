import Mathlib

/-!
Exponents for queries versus success probability in k-distinctness. All quantities are exponents
of `n`: a query budget `T = n ^ τ`, list sizes `r_l = n ^ (rho l τ)`, success `n ^ (...)`.

Belovs's bound: success `≤ O(1/n + T ^ e / n ^ (e - 1))` with `e = 4 - 2 ^ (2 - k)`.
-/

namespace KDistTradeoff

/-- Exponent of the list size after stage `l + 1`: `r_1 = T`, `r_{l+1} = T √(r_l / n)`. -/
def rho : ℕ → ℚ → ℚ
  | 0, τ => τ
  | l + 1, τ => τ + (rho l τ - 1) / 2

theorem rho_closed (l : ℕ) (τ : ℚ) :
    rho l τ = (2 - (1 / 2) ^ l) * τ - (1 - (1 / 2) ^ l) := by
  induction l with
  | zero => simp [rho]; ring
  | succ l ih => rw [rho, ih, pow_succ]; ring

/-- Success exponent of the nested Grover algorithm, `k = l + 2`: `(r_{k-1}/n) (T^2/n)`. -/
def nestedExp (l : ℕ) (τ : ℚ) : ℚ := rho l τ + 2 * τ - 2

/-- Belovs's T-term, `e τ - (e - 1)` with `e = 4 - (1/2)^(k-2)`. -/
def belovsExp (l : ℕ) (τ : ℚ) : ℚ := (4 - (1 / 2) ^ l) * τ - (3 - (1 / 2) ^ l)

theorem nested_eq_belovs (l : ℕ) (τ : ℚ) : nestedExp l τ = belovsExp l τ := by
  rw [nestedExp, belovsExp, rho_closed]; ring

/-- Lower end of the window: the T-term of Belovs's bound is at least `1/n`. -/
def lower (l : ℕ) : ℚ := (2 - (1 / 2) ^ l) / (4 - (1 / 2) ^ l)

theorem belovs_ge_inv_n (l : ℕ) (τ : ℚ) (h : lower l ≤ τ) : -1 ≤ belovsExp l τ := by
  have hp : (0 : ℚ) < (1 / 2) ^ l := by positivity
  have hq : (1 / 2 : ℚ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h4 : (0 : ℚ) < 4 - (1 / 2) ^ l := by linarith
  rw [lower, div_le_iff₀ h4] at h
  rw [belovsExp]; nlinarith

/-- In the window `[lower l, 1/2]` all constraints of the nested algorithm hold:
the last list is nonempty, lists shrink, and each search has `T^2 M ≥ n`. -/
theorem window_valid (l : ℕ) (τ : ℚ) (h1 : lower l ≤ τ) (h2 : τ ≤ 1 / 2) :
    0 ≤ rho l τ ∧ (∀ j, j < l → rho (j + 1) τ ≤ rho j τ ∧ 1 ≤ 2 * τ + rho j τ) := by
  have hH : (0 : ℚ) < (1 / 2) ^ l := by positivity
  have hH1 : (1 / 2 : ℚ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h4 : (0 : ℚ) < 4 - (1 / 2) ^ l := by linarith
  have hlow : (2 - (1 / 2) ^ l) ≤ τ * (4 - (1 / 2) ^ l) := by
    rw [lower, div_le_iff₀ h4] at h1; linarith
  -- rho is nonnegative for every index up to l, since (1/2)^j ≥ (1/2)^l
  have pos : ∀ j, j ≤ l → 0 ≤ rho j τ := by
    intro j hj
    have hj' : (1 / 2 : ℚ) ^ l ≤ (1 / 2) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have hj1 : (1 / 2 : ℚ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [rho_closed]; nlinarith
  refine ⟨pos l le_rfl, fun j hj => ⟨?_, ?_⟩⟩
  · have := pos j hj.le
    rw [rho]; linarith
  · -- (1/2)^j ≥ 2 (1/2)^l, and τ ≥ (2 - h)/(4 - h) is decreasing in h
    have hj' : 2 * (1 / 2 : ℚ) ^ l ≤ (1 / 2) ^ j := by
      have : (1 / 2 : ℚ) ^ l = (1 / 2) ^ (l - (j + 1)) * (1 / 2) ^ (j + 1) := by
        rw [← pow_add]; congr 1; omega
      have hle : (1 / 2 : ℚ) ^ (l - (j + 1)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hb : (0 : ℚ) ≤ (1 / 2) ^ j := by positivity
      have hm := mul_le_mul_of_nonneg_right hle hb
      rw [this, pow_succ]; nlinarith
    have hj1 : (1 / 2 : ℚ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [rho_closed]; nlinarith

/-- k = 3 above `√n`: the partial walk with `s1 = T`, `s2 = T^(3/2) / √n` and `T / √n`
iterations of cost `√n` has amplitude `(T/√n) √(s2/n)`. Its square is Belovs's T-term, and
the constraints hold on `[1/2, 5/7]`. -/
theorem walk_k3 (τ : ℚ) (h1 : 1 / 2 ≤ τ) (h2 : τ ≤ 5 / 7) :
    let s1 := τ
    let s2 := 3 / 2 * τ - 1 / 2
    let amp := (τ - 1 / 2) + (s2 - 1) / 2
    2 * amp = belovsExp 1 τ ∧ amp ≤ 0 ∧ 0 ≤ s2 ∧ s2 ≤ s1 ∧ 1 / 2 ≤ s1 ∧
      -- m = s1^2 / n pairs replaced per step, at most s2 (spectral gap m / s2)
      2 * s1 - 1 ≤ s2 ∧
      -- per-iteration update cost √(n s2 / s1) is at most the checking cost √n
      (1 + s2 - s1) / 2 ≤ 1 / 2 ∧
      -- setup s1 + s2 √(n/s1) is within the budget
      s2 + (1 - s1) / 2 ≤ τ := by
  simp only [belovsExp]; norm_num
  refine ⟨by ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- At the end of the window the walk has constant success (`n ^ (5/7)` queries). -/
theorem walk_k3_end : belovsExp 1 (5 / 7) = 0 := by norm_num [belovsExp]

/-- The window for k = 3 starts at `3/7`, for k = 4 at `7/15`. -/
theorem lower_values : lower 1 = 3 / 7 ∧ lower 2 = 7 / 15 := by norm_num [lower]

end KDistTradeoff
