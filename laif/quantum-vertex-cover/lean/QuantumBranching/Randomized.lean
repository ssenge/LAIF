import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Randomized paths and the pairing formula

`AmplitudeAmplification` is a named hypothesis on two functions: the number of iterations, as a
function of a lower bound `q` on the success probability, and the probability of success with that
number of iterations, for true success probability `p`. It is not proved here.

`iterations_le` is the cost arithmetic of Theorem 3: a success probability at least `1 / B` gives at
most `c * √B` iterations, success at least `2/3` on a yes instance, and no error on a no instance.
`iterations_le_of_rounded` allows a constant factor lost to the precision of the probabilities.

`pairing` is `d = 2 c (a + b) / (a + 2 c)`, and `pairing_half` is its homogeneity.
-/

namespace QuantumBranching

/-- **Amplitude amplification.** For a lower bound `q` on the success probability, `iter q` iterations
suffice, at most `c / √q`, and they succeed with probability at least `2/3` for every true success
probability `p ≥ q`. With success probability zero they never succeed. -/
structure AmplitudeAmplification (iter : ℝ → ℝ) (succ : ℝ → ℝ → ℝ) (c : ℝ) : Prop where
  iter_le : ∀ q, 0 < q → q ≤ 1 → iter q ≤ c / √q
  succ_ge : ∀ q p, 0 < q → q ≤ p → p ≤ 1 → (2 : ℝ) / 3 ≤ succ q p
  succ_zero : ∀ q, 0 < q → q ≤ 1 → succ q 0 = 0

/-- **Theorem 3, cost arithmetic.** -/
theorem iterations_le {iter : ℝ → ℝ} {succ : ℝ → ℝ → ℝ} {c : ℝ}
    (h : AmplitudeAmplification iter succ c) {B p : ℝ} (hB : 1 ≤ B) (hp : 1 / B ≤ p) (hp1 : p ≤ 1) :
    iter (1 / B) ≤ c * √B ∧ (2 : ℝ) / 3 ≤ succ (1 / B) p ∧ succ (1 / B) 0 = 0 := by
  have hB0 : 0 < B := by linarith
  have hq : 0 < 1 / B := by positivity
  have hq1 : 1 / B ≤ 1 := by rw [div_le_one hB0]; exact hB
  refine ⟨?_, h.succ_ge _ _ hq hp hp1, h.succ_zero _ hq hq1⟩
  have h1 := h.iter_le _ hq hq1
  have h2 : c / √(1 / B) = c * √B := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    field_simp
  rwa [h2] at h1

/-- The same when the success probability is only known up to a constant factor `κ`. -/
theorem iterations_le_of_rounded {iter : ℝ → ℝ} {succ : ℝ → ℝ → ℝ} {c : ℝ}
    (h : AmplitudeAmplification iter succ c) {B p κ : ℝ} (hB : 1 ≤ B) (hκ : 1 ≤ κ)
    (hp : 1 / (κ * B) ≤ p) (hp1 : p ≤ 1) :
    iter (1 / (κ * B)) ≤ c * √κ * √B := by
  have hκB : 1 ≤ κ * B := by nlinarith
  have := (iterations_le h hκB hp hp1).1
  rwa [Real.sqrt_mul (by linarith), ← mul_assoc] at this

/-- The pairing of the two bounds. -/
noncomputable def pairing (a b c : ℝ) : ℝ := 2 * c * (a + b) / (a + 2 * c)

/-- The pairing is homogeneous of degree one. -/
theorem pairing_smul (t a b c : ℝ) : pairing (t * a) (t * b) (t * c) = t * pairing a b c := by
  unfold pairing
  have h1 : t * a + 2 * (t * c) = t * (a + 2 * c) := by ring
  have h2 : 2 * (t * c) * (t * a + t * b) = t * t * (2 * c * (a + b)) := by ring
  rw [h1, h2]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hd : a + 2 * c = 0
  · simp [hd]
  · field_simp

/-- Halving `a`, `b`, `c` halves `d`. -/
theorem pairing_half (a b c : ℝ) : pairing (a / 2) (b / 2) (c / 2) = pairing a b c / 2 := by
  have := pairing_smul (1 / 2) a b c
  convert this using 2 <;> ring

end QuantumBranching
