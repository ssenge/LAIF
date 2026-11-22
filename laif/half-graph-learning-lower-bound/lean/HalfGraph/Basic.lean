import Mathlib

/-!
# Learning column-permuted half graphs: the combinatorial steps of the lower bound

The adversary matrix relates π to π ∘ (j j′) with weight 1/|π(j) − π(j′)|.

* `rowSum`: every row sums to Σ_{d=1}^{n−1} (n − d)/d (values 0, …, n − 1).
* `swap_apply_col`, `swap_swap_back`: for a fixed column j, exchanging j with the column of value b
  maps the permutations with π(j) = a bijectively to those with π(j) = b.
* `block_norm_le`: the triangle step ‖Σ_b B_b x_b‖ ≤ Σ_b m_b ‖x_b‖ for blocks of norm at most m_b.
-/

namespace HalfGraph

open Finset

/-- The weight of a row: Σ over value pairs a < b of 1/(b − a). -/
noncomputable def pairSum (n : ℕ) : ℝ :=
  ∑ b ∈ range n, ∑ a ∈ range b, (1 : ℝ) / ((b : ℝ) - a)

theorem inner_sum (b : ℕ) :
    ∑ a ∈ range b, (1 : ℝ) / ((b : ℝ) - a) = ∑ d ∈ Ico 1 (b + 1), (1 : ℝ) / d := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr (by simp)
  intro a ha
  rw [Finset.mem_range] at ha
  have : ((b - 1 - a : ℕ) : ℝ) = (b : ℝ) - 1 - a := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  congr 1
  push_cast [this]
  ring

theorem rowSum (n : ℕ) :
    pairSum n = ∑ d ∈ Ico 1 n, ((n : ℝ) - d) / d := by
  induction n with
  | zero => simp [pairSum]
  | succ k ih =>
    rw [pairSum, Finset.sum_range_succ, ← pairSum, ih, inner_sum]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k), Finset.sum_Ico_succ_top (by omega : 1 ≤ k)]
    have hs : ∑ d ∈ Ico 1 k, (((k + 1 : ℕ) : ℝ) - d) / d =
        ∑ d ∈ Ico 1 k, ((k : ℝ) - d) / d + ∑ d ∈ Ico 1 k, (1 : ℝ) / d := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun d _ => by push_cast; ring)
    rw [hs]
    push_cast
    ring

variable {n : ℕ}

/-- Exchanging column j with the column of value b puts the value b into column j. -/
theorem swap_apply_col (π : Equiv.Perm (Fin n)) (j b : Fin n) :
    (π * Equiv.swap j (π.symm b)) j = b := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- Exchanging back with the column that now holds the old value π(j) returns π. -/
theorem swap_swap_back (π : Equiv.Perm (Fin n)) (j b : Fin n) :
    (π * Equiv.swap j (π.symm b)) * Equiv.swap j ((π * Equiv.swap j (π.symm b)).symm (π j)) = π := by
  have h : (π * Equiv.swap j (π.symm b)).symm (π j) = π.symm b := by
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
    simp [Equiv.swap_apply_left, Equiv.symm_swap]
  rw [h, mul_assoc, Equiv.swap_mul_self, mul_one]

/-- The triangle step of the block bound. -/
theorem block_norm_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ι)
    (B : ι → E →L[ℝ] E) (m : ι → ℝ) (x : ι → E) (hB : ∀ b ∈ s, ‖B b‖ ≤ m b) :
    ‖∑ b ∈ s, B b (x b)‖ ≤ ∑ b ∈ s, m b * ‖x b‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  exact ((B b).le_opNorm (x b)).trans (mul_le_mul_of_nonneg_right (hB b hb) (norm_nonneg _))

end HalfGraph
