import Mathlib

/-!
# Multipliers of the fixed-observable construction on a circle

On the curve `z = ε (cos θ, sin θ, 0, …, 0)` the polynomial
`G = z₁² + z₂² + Σ_{j≥3} z_j T_{j−1}(z₁/ε)` is constant, and its partial derivatives in the
directions `j ≥ 3` are `T_{j−1}(cos θ) = cos((j − 1)θ)`. The products of `cos(kθ)` with
`cos(ωx)` and `sin(ωx)` have a top frequency `kθ + ωx` and a lower one `kθ − ωx`.
-/

namespace PhotonThreshold

open Real Polynomial

/-- The quadratic part is constant on the circle. -/
theorem quad_on_circle (ε t : ℝ) : (ε * cos t) ^ 2 + (ε * sin t) ^ 2 = ε ^ 2 := by
  have := sin_sq_add_cos_sq t
  nlinarith [this]

/-- The multiplier in direction `j ≥ 3`: `T_k(cos θ) = cos(kθ)`. -/
theorem multiplier_cos (k : ℕ) (θ : ℝ) : (Chebyshev.T ℝ k).eval (cos θ) = cos (k * θ) := by
  simp [Chebyshev.T_real_cos]

/-- Product with a cosine: top frequency plus a lower frequency. -/
theorem cos_mul_cos (a b : ℝ) : cos a * cos b = (cos (a + b) + cos (a - b)) / 2 := by
  rw [cos_add, cos_sub]; ring

/-- Product with a sine: top frequency minus a lower frequency. -/
theorem cos_mul_sin (a b : ℝ) : cos a * sin b = (sin (a + b) - sin (a - b)) / 2 := by
  rw [sin_add, sin_sub]; ring

/-- Every frequency `f` with `2L < f ≤ (m − 1)L` is `kL + ω` with `2 ≤ k ≤ m − 2` and
`1 ≤ ω ≤ L`, and its partner `kL − ω` is smaller. -/
theorem freq_decomp (L m f : ℕ) (hL : 1 ≤ L) (h1 : 2 * L < f) (h2 : f ≤ (m - 1) * L) :
    ∃ k ω, 2 ≤ k ∧ k ≤ m - 2 ∧ 1 ≤ ω ∧ ω ≤ L ∧ f = k * L + ω ∧ k * L - ω < f := by
  refine ⟨(f - 1) / L, (f - 1) % L + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (by omega)]; omega
  · have : (f - 1) / L < m - 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : (m - 1) * L = (m - 1) * L := rfl
      omega
    omega
  · omega
  · have := Nat.mod_lt (f - 1) (show 0 < L by omega); omega
  · have := Nat.div_add_mod (f - 1) L
    have : L * ((f - 1) / L) = (f - 1) / L * L := Nat.mul_comm _ _
    omega
  · have := Nat.div_add_mod (f - 1) L
    have : L * ((f - 1) / L) = (f - 1) / L * L := Nat.mul_comm _ _
    omega

end PhotonThreshold
