import Mathlib

/-!
# Counting steps of the single-copy Clifford testing lower bound

* `inter_card_le`: two distinct subspaces of the same finite dimension `t` over `ZMod 2` meet in at
  most `2 ^ (t - 1)` vectors.
* `inv_entry_bound`: if `(1 + E) * W = 1` for an `N × N` real matrix `E` whose entries are at most
  `ε` in absolute value, with `N ε < 1`, then every entry of `W - 1` is at most `ε / (1 - N ε)`.
  Applied to the Gram matrix `2 ^ (n t) (1 + E)` of the commutant generators, this bounds the entries
  of the inverse Gram matrix.
* `three_sums_le`: the arithmetic that turns these entry bounds into the total variation bound
  `2 ^ (-n) + 2 w` with `w = N 2 ^ (-n) ≤ 1/2`.
-/

namespace CliffordCount

open Matrix

/-- Distinct subspaces of the same finite dimension `t` over `ZMod 2` meet in at most
`2 ^ (t - 1)` vectors. -/
theorem inter_card_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (U U' : Submodule (ZMod 2) V) (t : ℕ) (hU : Module.finrank (ZMod 2) U = t)
    (hU' : Module.finrank (ZMod 2) U' = t) (hne : U ≠ U') :
    Nat.card (U ⊓ U' : Submodule (ZMod 2) V) ≤ 2 ^ (t - 1) := by
  have hlt : U ⊓ U' < U := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    have hle : U ≤ U' := by rw [← h]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hU, hU']))
  have hr : Module.finrank (ZMod 2) (U ⊓ U' : Submodule (ZMod 2) V) < t := by
    rw [← hU]; exact Submodule.finrank_lt_finrank_of_lt hlt
  have : Module.Finite (ZMod 2) (U ⊓ U' : Submodule (ZMod 2) V) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Entry bound for the inverse of `1 + E`, by a fixed-point argument. -/
theorem inv_entry_bound {N : ℕ} (E W : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ)
    (hE : ∀ i j, |E i j| ≤ ε) (hNε : (N : ℝ) * ε < 1) (hW : (1 + E) * W = 1) :
    ∀ i j, |W i j - (1 : Matrix (Fin N) (Fin N) ℝ) i j| ≤ ε / (1 - N * ε) := by
  intro i j
  have hpos : 0 < 1 - (N : ℝ) * ε := by linarith
  have : Nonempty (Fin N × Fin N) := ⟨(i, j)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max
    (fun q : Fin N × Fin N => |W q.1 q.2 - (1 : Matrix (Fin N) (Fin N) ℝ) q.1 q.2|)
  set m := |W p.1 p.2 - (1 : Matrix (Fin N) (Fin N) ℝ) p.1 p.2| with hm
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hE i j)
  -- `W - 1 = - E W`, entrywise
  have hrel : ∀ a b, W a b - (1 : Matrix (Fin N) (Fin N) ℝ) a b = -∑ k, E a k * W k b := by
    intro a b
    have h := congrFun (congrFun hW a) b
    rw [add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply] at h
    linarith
  have hone : ∀ b, ∑ k : Fin N, |(1 : Matrix (Fin N) (Fin N) ℝ) k b| = 1 := by
    intro b
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [Matrix.one_apply, hk])
      (fun h => absurd (Finset.mem_univ b) h)]
    simp
  have hentry : ∀ a b, |W a b - (1 : Matrix (Fin N) (Fin N) ℝ) a b| ≤ ε + N * ε * m := by
    intro a b
    rw [hrel a b, abs_neg]
    calc |∑ k, E a k * W k b| ≤ ∑ k, |E a k * W k b| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |E a k| * |W k b| := by simp [abs_mul]
      _ ≤ ∑ k, ε * (|(1 : Matrix (Fin N) (Fin N) ℝ) k b| + m) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul (hE a k) _ (abs_nonneg _) hε
          have h1 := hp (k, b)
          have h2 : |W k b| ≤ |(1 : Matrix (Fin N) (Fin N) ℝ) k b|
              + |W k b - (1 : Matrix (Fin N) (Fin N) ℝ) k b| := by
            have := abs_add_le ((1 : Matrix (Fin N) (Fin N) ℝ) k b)
              (W k b - (1 : Matrix (Fin N) (Fin N) ℝ) k b)
            simpa using this
          simp only at h1
          linarith
      _ = ε * ∑ k : Fin N, |(1 : Matrix (Fin N) (Fin N) ℝ) k b| + N * ε * m := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp
          ring
      _ = ε + N * ε * m := by rw [hone b, mul_one]
  have hm_le : m ≤ ε / (1 - N * ε) := by
    rw [le_div_iff₀ hpos]
    have := hentry p.1 p.2
    nlinarith
  exact le_trans (hp (i, j)) hm_le

/-- The three sums of the total variation bound. Here `q = 2 ^ (-n)`, `w = N q ≤ 1/2`, and
`a = q / (1 - w)` bounds the off-diagonal and diagonal deviations of the normalized inverse Gram
matrix. -/
theorem three_sums_le (N q : ℝ) (hN : 1 ≤ N) (hq : 0 ≤ q) (hw : N * q ≤ 1 / 2) :
    (q / (1 - N * q)) / 2 + (N - 1) * (q / (1 - N * q)) / 2
      + q * (N - 1) * (1 + q / (1 - N * q) + (N - 1) * (q / (1 - N * q))) / 2
      ≤ q + 2 * (N * q) := by
  set w := N * q with hwdef
  have h1w : 0 < 1 - w := by linarith
  set a := q / (1 - w) with ha
  have ha0 : 0 ≤ a := div_nonneg hq h1w.le
  have haw : a * (1 - w) = q := by rw [ha]; field_simp
  -- a ≤ 2 q and N a ≤ 2 w
  have ha2 : a ≤ 2 * q := by nlinarith
  have hNa : N * a * (1 - w) = w := by rw [hwdef]; nlinarith [haw]
  have hNa2 : N * a ≤ 2 * w := by nlinarith
  have hNa1 : N * a ≤ 1 := by nlinarith
  have hq1 : q ≤ w := by nlinarith
  -- first two terms: a / 2 + (N - 1) a / 2 = N a / 2 ≤ w
  -- third term: q (N - 1)(1 + N a) / 2 ≤ w (1 + N a) / 2 ≤ w
  have h3 : q * (N - 1) * (1 + a + (N - 1) * a) ≤ w * (1 + N * a) := by
    have : q * (N - 1) ≤ w := by nlinarith
    have hpos : 0 ≤ 1 + N * a := by nlinarith
    calc q * (N - 1) * (1 + a + (N - 1) * a) = q * (N - 1) * (1 + N * a) := by ring
      _ ≤ w * (1 + N * a) := mul_le_mul_of_nonneg_right this hpos
  have h4 : w * (1 + N * a) ≤ 2 * w := by nlinarith
  have h5 : a / 2 + (N - 1) * a / 2 = N * a / 2 := by ring
  nlinarith

end CliffordCount
