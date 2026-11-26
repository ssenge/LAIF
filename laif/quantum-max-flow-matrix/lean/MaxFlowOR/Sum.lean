import Mathlib

/-!
# The sum of flow times path length over the phases

Phase `j` adds flow `F j` along paths of length `D j`. Writing `R d` for the flow pushed in phases
with `D j > d`, the total `∑ F j · D j` equals `∑_d R d`. If `R d ≤ f` and `R d ≤ 8 n² / (d+1)²`,
the sum over any range is at most `K f + 8 n² / K` for every `K ≥ 1`.
-/

namespace MaxFlowOR

/-- Exchange of summation: `∑_j F j · D j = ∑_{d < N} ∑_{j, d < D j} F j` when all `D j ≤ N`. -/
theorem charging {ι : Type*} (J : Finset ι) (F D : ι → ℕ) (N : ℕ) (hD : ∀ j ∈ J, D j ≤ N) :
    ∑ j ∈ J, F j * D j = ∑ d ∈ Finset.range N, ∑ j ∈ J.filter (fun j => d < D j), F j := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  have : (Finset.range N).filter (fun d => d < D j) = Finset.range (D j) := by
    ext d; simp; have := hD j hj; omega
  rw [this, Finset.card_range]

/-- Telescoping tail: `∑_{k < m} 1/(K+k+1)² ≤ 1/K`. -/
theorem tail_le (K : ℝ) (hK : 0 < K) (m : ℕ) :
    ∑ k ∈ Finset.range m, 1 / (K + k + 1) ^ 2 ≤ 1 / K - 1 / (K + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : 1 / (K + m + 1) ^ 2 ≤ 1 / (K + m) - 1 / (K + m + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    rw [show K + ((m : ℝ) + 1) = K + m + 1 by ring]
    linarith

/-- The sum `∑_{d < K + m} R d` with `R d ≤ f` and `R d ≤ 8 n² / (d+1)²` is at most
`K f + 8 n² / K`. -/
theorem sum_R_le (R : ℕ → ℝ) (f n : ℝ) (K m : ℕ) (hK : 1 ≤ K)
    (hf : ∀ d, R d ≤ f) (hn : ∀ d, R d ≤ 8 * n ^ 2 / ((d : ℝ) + 1) ^ 2) :
    ∑ d ∈ Finset.range (K + m), R d ≤ K * f + 8 * n ^ 2 / K := by
  rw [Finset.sum_range_add]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : ∑ d ∈ Finset.range K, R d ≤ K * f := by
    calc ∑ d ∈ Finset.range K, R d ≤ ∑ _d ∈ Finset.range K, f := Finset.sum_le_sum (fun d _ => hf d)
      _ = K * f := by simp
  have h2 : ∑ k ∈ Finset.range m, R (K + k) ≤ 8 * n ^ 2 * (1 / K - 1 / (K + m)) := by
    calc ∑ k ∈ Finset.range m, R (K + k)
        ≤ ∑ k ∈ Finset.range m, 8 * n ^ 2 * (1 / ((K : ℝ) + k + 1) ^ 2) :=
          Finset.sum_le_sum (fun k _ => by
            have := hn (K + k); push_cast at this; rw [mul_one_div]; exact this)
      _ = 8 * n ^ 2 * ∑ k ∈ Finset.range m, 1 / ((K : ℝ) + k + 1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 8 * n ^ 2 * (1 / K - 1 / (K + m)) :=
          mul_le_mul_of_nonneg_left (tail_le K hK' m) (by positivity)
  have h3 : 8 * n ^ 2 * (1 / (K : ℝ) - 1 / (K + m)) ≤ 8 * n ^ 2 / K := by
    have : (0 : ℝ) ≤ 1 / (K + m) := by positivity
    have h8 : (0 : ℝ) ≤ 8 * n ^ 2 := by positivity
    rw [mul_sub, mul_one_div]; nlinarith
  linarith

/-- Lemma 4 in the form used for the query count: if the flow pushed after distance `d` is at most
`f` and at most `8 n² / (d+1)²`, then `∑_j F j · D j ≤ K f + 8 n² / K` for every `K ≥ 1`. -/
theorem sum_FD_le {ι : Type*} (J : Finset ι) (F D : ι → ℕ) (f n : ℝ) (K m : ℕ) (hK : 1 ≤ K)
    (hD : ∀ j ∈ J, D j ≤ K + m)
    (hf : ∀ d : ℕ, ((∑ j ∈ J.filter (fun j => d < D j), F j : ℕ) : ℝ) ≤ f)
    (hn : ∀ d : ℕ, ((∑ j ∈ J.filter (fun j => d < D j), F j : ℕ) : ℝ) ≤
      8 * n ^ 2 / ((d : ℝ) + 1) ^ 2) :
    ((∑ j ∈ J, F j * D j : ℕ) : ℝ) ≤ K * f + 8 * n ^ 2 / K := by
  rw [charging J F D (K + m) hD]
  push_cast
  have := sum_R_le (fun d => ((∑ j ∈ J.filter (fun j => d < D j), F j : ℕ) : ℝ)) f n K m hK hf hn
  push_cast at this
  exact this

end MaxFlowOR
