import Mathlib

/-!
# Cost of the quantum AE-MonoEq triangle algorithm

With thresholds `n^f`, the Boolean products for one colour with `m` edges have shapes whose sides `x, z ≤ n` and
`y ≤ m / n^f`, and by square blocks cost at most `x · y · z^(ω - 2)`. The searches cost `n^(2 + f/2)`.

* `colour_cost_le`: `x · y · z^(ω-2) ≤ n^(1-f) · m · n^(ω-2)` for `0 ≤ x, z ≤ n`, `0 ≤ y ≤ m / n^f`, `ω ≥ 2`.
* `total_cost_le`: summed over colours with `∑ m_c ≤ 4 n²`, the products cost at most `4 · n^(ω + 1 - f)`.
* `balance`: with `f = 2(ω - 1)/3`, both `2 + f/2` and `ω + 1 - f` equal `(5 + ω)/3`.
* `exponent_published`: `(5 + 2.371177)/3 ≤ 2.45706`; `exponent_nine_fourths`: `(5 + 9/4)/3 = 29/12`.
* `colour_cost_tight`, `balance_example`: the bound of `colour_cost_le` is attained at `x = z = n`, `y = m / n^f`, and
  at `ω = 2.371177` the threshold `f` lies in `(0, 1)`.
-/

namespace MaxMinExponent

theorem colour_cost_le {n m f ω x y z : ℝ} (hn : 1 ≤ n) (hω : 2 ≤ ω)
    (hx0 : 0 ≤ x) (hx : x ≤ n) (hy0 : 0 ≤ y) (hy : y ≤ m / n ^ f) (hz0 : 0 ≤ z) (hz : z ≤ n) :
    x * y * z ^ (ω - 2) ≤ n ^ (1 - f) * m * n ^ (ω - 2) := by
  have hn0 : 0 < n := by linarith
  have hzr : z ^ (ω - 2) ≤ n ^ (ω - 2) := Real.rpow_le_rpow hz0 hz (by linarith)
  have hzr0 : 0 ≤ z ^ (ω - 2) := Real.rpow_nonneg hz0 _
  have hxy : x * y ≤ n * (m / n ^ f) := mul_le_mul hx hy hy0 hn0.le
  have hnm : n * (m / n ^ f) = n ^ (1 - f) * m := by
    rw [Real.rpow_sub hn0 1 f, Real.rpow_one]; ring
  calc x * y * z ^ (ω - 2) ≤ n * (m / n ^ f) * n ^ (ω - 2) :=
        mul_le_mul hxy hzr hzr0 (mul_nonneg hn0.le (le_trans hy0 hy))
    _ = n ^ (1 - f) * m * n ^ (ω - 2) := by rw [hnm]

theorem total_cost_le {ι : Type*} (s : Finset ι) {n f ω : ℝ} (m x y z : ι → ℝ) (hn : 1 ≤ n) (hω : 2 ≤ ω)
    (hx0 : ∀ c, 0 ≤ x c) (hx : ∀ c, x c ≤ n) (hy0 : ∀ c, 0 ≤ y c) (hy : ∀ c, y c ≤ m c / n ^ f)
    (hz0 : ∀ c, 0 ≤ z c) (hz : ∀ c, z c ≤ n) (hm : ∑ c ∈ s, m c ≤ 4 * n ^ 2) :
    ∑ c ∈ s, x c * y c * z c ^ (ω - 2) ≤ 4 * n ^ (ω + 1 - f) := by
  have hn0 : 0 < n := by linarith
  have hk : 0 ≤ n ^ (1 - f) * n ^ (ω - 2) := mul_nonneg (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hn0.le _)
  calc ∑ c ∈ s, x c * y c * z c ^ (ω - 2) ≤ ∑ c ∈ s, n ^ (1 - f) * m c * n ^ (ω - 2) :=
        Finset.sum_le_sum fun c _ => colour_cost_le hn hω (hx0 c) (hx c) (hy0 c) (hy c) (hz0 c) (hz c)
    _ = (n ^ (1 - f) * n ^ (ω - 2)) * ∑ c ∈ s, m c := by rw [Finset.mul_sum]; congr 1; ext c; ring
    _ ≤ (n ^ (1 - f) * n ^ (ω - 2)) * (4 * n ^ 2) := mul_le_mul_of_nonneg_left hm hk
    _ = 4 * n ^ (ω + 1 - f) := by
        have h2 : n ^ (2 : ℕ) = n ^ (2 : ℝ) := by norm_cast
        rw [h2, show n ^ (1 - f) * n ^ (ω - 2) * (4 * n ^ (2 : ℝ)) =
            4 * (n ^ (1 - f) * n ^ (ω - 2) * n ^ (2 : ℝ)) by ring, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
        congr 2; ring

theorem balance (ω : ℝ) :
    2 + (2 * (ω - 1) / 3) / 2 = (5 + ω) / 3 ∧ ω + 1 - 2 * (ω - 1) / 3 = (5 + ω) / 3 := by
  constructor <;> ring

theorem exponent_published : (5 + 2.371177 : ℝ) / 3 ≤ 2.45706 := by norm_num

theorem exponent_nine_fourths : (5 + 9 / 4 : ℝ) / 3 = 29 / 12 := by norm_num

theorem colour_cost_tight {n m f ω : ℝ} (hn : 1 ≤ n) :
    n * (m / n ^ f) * n ^ (ω - 2) = n ^ (1 - f) * m * n ^ (ω - 2) := by
  have hn0 : 0 < n := by linarith
  rw [Real.rpow_sub hn0 1 f, Real.rpow_one]; ring

theorem balance_example : 0 < 2 * ((2.371177 : ℝ) - 1) / 3 ∧ 2 * ((2.371177 : ℝ) - 1) / 3 < 1 := by
  constructor <;> norm_num

end MaxMinExponent
