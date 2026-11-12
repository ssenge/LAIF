import Mathlib

/-!
Exponents of amplitude amplification over the random partitions of the algebraic sieves for
Hamiltonicity and k-path. A run costs `2 ^ L`, succeeds with probability `P`, and amplification costs
`2 ^ L / √P`. All statements are about the squares `4 ^ L / P`.
-/

open Nat

namespace QuantumSieve

/-- One step of `C(3t, t)`. -/
theorem choose_step (t : ℕ) :
    (3 * (t + 1)).choose (t + 1) * ((t + 1) * ((2 * t + 2) * (2 * t + 1)))
      = (3 * t).choose t * ((3 * t + 3) * ((3 * t + 2) * (3 * t + 1))) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show t + 1 ≤ 3 * (t + 1) by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show t ≤ 3 * t by omega)
  have e1 : 3 * (t + 1) - (t + 1) = 2 * t + 2 := by omega
  have e2 : 3 * t - t = 2 * t := by omega
  rw [e1] at h1
  rw [e2] at h2
  have f1 : (3 * (t + 1))! = (3 * t + 3) * ((3 * t + 2) * ((3 * t + 1) * (3 * t)!)) := by
    rw [show 3 * (t + 1) = 3 * t + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
  have f2 : (2 * t + 2)! = (2 * t + 2) * ((2 * t + 1) * (2 * t)!) := by
    rw [show 2 * t + 2 = 2 * t + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  have f3 : (t + 1)! = (t + 1) * t ! := Nat.factorial_succ t
  have hpos : 0 < t ! * (2 * t)! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [f1, f2, f3] at h1
  rw [← h2] at h1
  nlinarith [h1]

/-- `(27 / 4) ^ t ≤ (3 t + 1) C(3t, t)`. -/
theorem choose_lower (t : ℕ) :
    ((27 : ℝ) / 4) ^ t ≤ (3 * (t : ℝ) + 1) * ((3 * t).choose t : ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : (((3 * (t + 1)).choose (t + 1) : ℕ) : ℝ) * ((t + 1) * ((2 * t + 2) * (2 * t + 1)))
        = ((3 * t).choose t : ℝ) * ((3 * t + 3) * ((3 * t + 2) * (3 * t + 1))) := by
      exact_mod_cast choose_step t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    set c : ℝ := ((3 * t).choose t : ℝ) with hc
    set d : ℝ := ((3 * (t + 1)).choose (t + 1) : ℝ) with hd
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    have hden : (0 : ℝ) < (t + 1) * ((2 * t + 2) * (2 * t + 1)) := by positivity
    have hd' : d = c * ((3 * t + 3) * ((3 * t + 2) * (3 * t + 1)))
        / ((t + 1) * ((2 * t + 2) * (2 * t + 1))) := by
      rw [eq_div_iff hden.ne']; exact hstep
    rw [pow_succ]
    have hgoal : (3 * ((t + 1 : ℕ) : ℝ) + 1) * d
        = c * ((3 * t + 4) * ((3 * t + 3) * ((3 * t + 2) * (3 * t + 1))))
          / ((t + 1) * ((2 * t + 2) * (2 * t + 1))) := by
      rw [hd']; push_cast; ring
    rw [hgoal, le_div_iff₀ hden]
    have hkey : (3 * (t : ℝ) + 1) * (27 / 4) * ((t + 1) * ((2 * t + 2) * (2 * t + 1)))
        ≤ (3 * t + 4) * ((3 * t + 3) * ((3 * t + 2) * (3 * t + 1))) := by
      have : 0 ≤ (3 * (t : ℝ) + 1) * (t + 1) * (2 * t + 2) := by positivity
      nlinarith [mul_nonneg this ht, mul_nonneg ht ht]
    calc ((27 : ℝ) / 4) ^ t * (27 / 4) * ((t + 1) * ((2 * t + 2) * (2 * t + 1)))
        ≤ ((3 * (t : ℝ) + 1) * c) * (27 / 4) * ((t + 1) * ((2 * t + 2) * (2 * t + 1))) := by
          have : 0 ≤ (27 / 4 : ℝ) * ((t + 1) * ((2 * t + 2) * (2 * t + 1))) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right ih this]
      _ = c * ((3 * (t : ℝ) + 1) * (27 / 4) * ((t + 1) * ((2 * t + 2) * (2 * t + 1)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkey hc0

/-- `3 t C(3t - 1, 2t - 1) = 2 t C(3t, t)`, for `t ≥ 1`. -/
theorem choose_prev_a (t : ℕ) (ht : 1 ≤ t) :
    3 * ((3 * t - 1).choose (2 * t - 1)) = 2 * (3 * t).choose t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have h := Nat.add_one_mul_choose_eq (3 * (u + 1) - 1) (2 * (u + 1) - 1)
  have e1 : 3 * (u + 1) - 1 + 1 = 3 * (u + 1) := by omega
  have e2 : 2 * (u + 1) - 1 + 1 = 2 * (u + 1) := by omega
  rw [e1, e2] at h
  have hsymm : (3 * (u + 1)).choose (2 * (u + 1)) = (3 * (u + 1)).choose (u + 1) := by
    rw [← Nat.choose_symm (show u + 1 ≤ 3 * (u + 1) by omega)]
    congr 1
    omega
  rw [hsymm] at h
  have hpos : 0 < u + 1 := by omega
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  nlinarith [h]

/-- `3 C(3t - 1, t) = 2 C(3t, t)`, for `t ≥ 1`. -/
theorem choose_prev_b (t : ℕ) (ht : 1 ≤ t) :
    3 * ((3 * t - 1).choose t) = 2 * (3 * t).choose t := by
  have h := choose_prev_a t ht
  have hs : (3 * t - 1).choose (2 * t - 1) = (3 * t - 1).choose t := by
    rw [← Nat.choose_symm (show t ≤ 3 * t - 1 by omega)]
    congr 1
    omega
  rwa [hs] at h

/-- `(27 / 4) ^ t ≤ (3 / 2) (3 t + 1) C(3t - 1, 2t - 1)`. -/
theorem prev_lower (t : ℕ) (ht : 1 ≤ t) :
    ((27 : ℝ) / 4) ^ t ≤ 3 / 2 * (3 * (t : ℝ) + 1) * ((3 * t - 1).choose (2 * t - 1) : ℝ) := by
  have h : (3 : ℝ) * ((3 * t - 1).choose (2 * t - 1) : ℝ) = 2 * ((3 * t).choose t : ℝ) := by
    exact_mod_cast choose_prev_a t ht
  have h0 := choose_lower t
  have : 3 / 2 * (3 * (t : ℝ) + 1) * ((3 * t - 1).choose (2 * t - 1) : ℝ)
      = (3 * (t : ℝ) + 1) * ((3 * t).choose t : ℝ) := by
    calc _ = (3 * (t : ℝ) + 1) / 2 * (3 * ((3 * t - 1).choose (2 * t - 1) : ℝ)) := by ring
      _ = _ := by rw [h]; ring
  rw [this]
  exact h0

/-- The arithmetic of the exponent: `4 ^ (4 t) 2 ^ (6 t) / (27 / 4) ^ (2 t) = (8 / 3) ^ (6 t)`. -/
theorem exponent_identity (t : ℕ) :
    (4 : ℝ) ^ (4 * t) * 2 ^ (6 * t) = ((8 : ℝ) / 3) ^ (6 * t) * (((27 : ℝ) / 4) ^ t) ^ 2 := by
  rw [← pow_mul]
  have e1 : (4 : ℝ) ^ (4 * t) * 2 ^ (6 * t) = (4 ^ 4 * 2 ^ 6) ^ t := by
    rw [pow_mul, pow_mul, mul_pow]
  have e2 : ((8 : ℝ) / 3) ^ (6 * t) * ((27 : ℝ) / 4) ^ (t * 2)
      = (((8 : ℝ) / 3) ^ 6 * ((27 : ℝ) / 4) ^ 2) ^ t := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 6 t, mul_comm 2 t]
  rw [e1, e2]
  norm_num

/-- Hamiltonicity. With `n = 6 t`, `m = t` extra labels, `L = 4 t`, and success probability
`C(3t - 1, 2t - 1) ^ 2 / C(6t, 3t)`, the square of the cost is at most a polynomial times
`(8 / 3) ^ n`. -/
theorem hamiltonicity_cost (t : ℕ) (ht : 1 ≤ t) :
    (4 : ℝ) ^ (4 * t) * ((6 * t).choose (3 * t) : ℝ)
      ≤ (3 / 2 * (3 * (t : ℝ) + 1)) ^ 2 * ((8 : ℝ) / 3) ^ (6 * t)
        * ((3 * t - 1).choose (2 * t - 1) : ℝ) ^ 2 := by
  have h1 : ((6 * t).choose (3 * t) : ℝ) ≤ 2 ^ (6 * t) := by
    exact_mod_cast Nat.choose_le_two_pow _ _
  have h2 := prev_lower t ht
  have h3 : (((27 : ℝ) / 4) ^ t) ^ 2
      ≤ (3 / 2 * (3 * (t : ℝ) + 1) * ((3 * t - 1).choose (2 * t - 1) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc (4 : ℝ) ^ (4 * t) * ((6 * t).choose (3 * t) : ℝ)
      ≤ (4 : ℝ) ^ (4 * t) * 2 ^ (6 * t) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((8 : ℝ) / 3) ^ (6 * t) * (((27 : ℝ) / 4) ^ t) ^ 2 := exponent_identity t
    _ ≤ ((8 : ℝ) / 3) ^ (6 * t)
        * (3 / 2 * (3 * (t : ℝ) + 1) * ((3 * t - 1).choose (2 * t - 1) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- k-path. With `k = 6 t`, `k₁ = 3 t`, `ℓ₂ = t`, `L = 4 t`, and success probability
`2 ^ (-k) C(k₁ + 1, k - k₁ - ℓ₂) C(k - k₁ - 1, ℓ₂)`, the square of the cost is at most a polynomial
times `(8 / 3) ^ k`. -/
theorem kpath_cost (t : ℕ) (ht : 1 ≤ t) :
    (4 : ℝ) ^ (4 * t) * 2 ^ (6 * t)
      ≤ (3 / 2 * (3 * (t : ℝ) + 1) ^ 2) * ((8 : ℝ) / 3) ^ (6 * t)
        * (((3 * t + 1).choose (2 * t) : ℝ) * ((3 * t - 1).choose t : ℝ)) := by
  have h0 := choose_lower t
  have hb : (3 : ℝ) * ((3 * t - 1).choose t : ℝ) = 2 * ((3 * t).choose t : ℝ) := by
    exact_mod_cast choose_prev_b t ht
  have ha : ((3 * t).choose t : ℝ) ≤ ((3 * t + 1).choose (2 * t) : ℝ) := by
    have e : (3 * t).choose t = (3 * t).choose (2 * t) := by
      rw [← Nat.choose_symm (show t ≤ 3 * t by omega)]
      congr 1
      omega
    rw [e]
    exact_mod_cast Nat.choose_le_succ _ _
  set c : ℝ := ((3 * t).choose t : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hprod : (((27 : ℝ) / 4) ^ t) ^ 2
      ≤ (3 / 2 * (3 * (t : ℝ) + 1) ^ 2)
        * (((3 * t + 1).choose (2 * t) : ℝ) * ((3 * t - 1).choose t : ℝ)) := by
    have h3 : (((27 : ℝ) / 4) ^ t) ^ 2 ≤ ((3 * (t : ℝ) + 1) * c) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h0 2
    have hb' : ((3 * t - 1).choose t : ℝ) = 2 / 3 * c := by linarith
    have h4 : c * ((3 * t - 1).choose t : ℝ)
        ≤ ((3 * t + 1).choose (2 * t) : ℝ) * ((3 * t - 1).choose t : ℝ) :=
      mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
    have h5 : (3 / 2 * (3 * (t : ℝ) + 1) ^ 2) * (c * ((3 * t - 1).choose t : ℝ))
        = ((3 * (t : ℝ) + 1) * c) ^ 2 := by rw [hb']; ring
    calc (((27 : ℝ) / 4) ^ t) ^ 2 ≤ ((3 * (t : ℝ) + 1) * c) ^ 2 := h3
      _ = (3 / 2 * (3 * (t : ℝ) + 1) ^ 2) * (c * ((3 * t - 1).choose t : ℝ)) := h5.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  calc (4 : ℝ) ^ (4 * t) * 2 ^ (6 * t)
      = ((8 : ℝ) / 3) ^ (6 * t) * (((27 : ℝ) / 4) ^ t) ^ 2 := exponent_identity t
    _ ≤ ((8 : ℝ) / 3) ^ (6 * t) * ((3 / 2 * (3 * (t : ℝ) + 1) ^ 2)
        * (((3 * t + 1).choose (2 * t) : ℝ) * ((3 * t - 1).choose t : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

/-- `(8 / 3) ^ (1 / 2) < 1.633` in squares, and `1.633` is below `1.656` and `1.727`. -/
theorem base_values : ((8 : ℝ) / 3) < 1.633 ^ 2 ∧ (1.633 : ℝ) < 1.656 ∧ (1.633 : ℝ) < 1.727 := by
  norm_num

end QuantumSieve
