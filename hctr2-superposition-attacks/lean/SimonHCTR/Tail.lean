import Mathlib.Data.Nat.Factorial.Basic

/-!
# Numeric tail bounds for Lemma 6 (`n = 128`)

With `n = 128`: `2^{2n} / n! < 2^{-460}`, `2^{3n} / n! < 2^{-330}` and
`2^{6n} / (2n)! < 2^{-900}`, stated as inequalities between natural numbers.
-/

namespace SimonHCTR.Tail

/-- `2^{2n} · 2^{460} < n!` for `n = 128`. -/
theorem tail_delta : 2 ^ (2 * 128) * 2 ^ 460 < Nat.factorial 128 := by decide +kernel

/-- `2^{3n} · 2^{330} < n!` for `n = 128`. -/
theorem tail_cross : 2 ^ (3 * 128) * 2 ^ 330 < Nat.factorial 128 := by decide +kernel

/-- `2^{6n} · 2^{900} < (2n)!` for `n = 128`. -/
theorem tail_hctrpp : 2 ^ (6 * 128) * 2 ^ 900 < Nat.factorial 256 := by decide +kernel

end SimonHCTR.Tail
