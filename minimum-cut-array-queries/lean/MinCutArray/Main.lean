import MinCutArray.Family

/-!
# The lower bound for minimum cut in the adjacency array model

The only hypothesis is the classical polynomial degree bound for exact counting, `CountDegree`.
-/

open Finset

namespace MinCutArray

/-- A real multilinear polynomial of degree at most `D` on `N` bits that is bounded on the cube and separates
Hamming weight `k + 1` from Hamming weight `k - 1` has degree `Ω(√(N k))`. -/
def CountDegreeWith (c : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (k D : ℕ) (R : (ι → Bool) → ℝ),
    1 ≤ k → 2 * k + 1 ≤ Fintype.card ι → IsJuntaSum D R →
    (∀ x, 0 ≤ R x ∧ R x ≤ 1) →
    (∀ x : ι → Bool, (∑ e, ind (x e)) = k + 1 → 2 / 3 ≤ R x) →
    (∀ x : ι → Bool, (∑ e, ind (x e)) + 1 = k → R x ≤ 1 / 3) →
    c * Real.sqrt ((Fintype.card ι : ℝ) * k) ≤ D

/-- The degree bound for exact counting, for some constant. -/
def CountDegree : Prop := ∃ c : ℝ, 0 < c ∧ CountDegreeWith c

variable {T : ℕ} {S : Type} [Fintype S] [DecidableEq S]

/-- An algorithm for minimum cut on `t` vertices per class gives a degree `2T` polynomial that separates the two
Hamming weights. -/
theorem degree_from_algorithm {c : ℝ} (hc0 : 0 < c) (hdeg : CountDegreeWith c) (t τ : ℕ) [NeZero t]
    (q : QAlg (Vx t) T S) (ht : 9 ≤ t) (hτ : 1 ≤ τ) (hτt : τ ≤ t) (hq : q.Computes τ) :
    c / 4 * ((t : ℝ) * Real.sqrt t * Real.sqrt τ) ≤ T := by
  set m := τ * (t - 1) with hm
  set k := m / 2 - 1 with hk
  have hm8 : 8 ≤ m := by
    have : 8 ≤ t - 1 := by omega
    calc 8 ≤ 1 * (t - 1) := by omega
      _ ≤ τ * (t - 1) := Nat.mul_le_mul_right _ hτ
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 * (k + 1) ≤ m := by omega
  have hmt : m + 1 ≤ t * t := by
    have h1 : τ * (t - 1) ≤ t * (t - 1) := Nat.mul_le_mul_right _ hτt
    have h2 : t * (t - 1) + 1 ≤ t * t := by
      obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    omega
  have hcard : Fintype.card (Cell t) = t * t := by simp [ZMod.card]
  have hmc : ∀ x : Cell t → Bool, wtX x ≤ k + 1 → (graph τ x).IsMinCut (2 * wtX x) := by
    intro x hx
    exact isMinCut τ x (by omega) (by omega)
  let P : ℕ → Prop := fun n => 2 * k ≤ n
  have hbound := hdeg (Cell t) k (2 * T) (fun x => q.prob (arr τ x) P) hk1 (by rw [hcard]; omega)
    (q.isJuntaSum_prob (fun x => arr τ x) loc (fun p x y h => loc_spec τ p x y h) P)
    (fun x => ⟨q.prob_nonneg _ _, q.prob_le_one _ _⟩)
    (by
      intro x hx
      have hx' : wtX x = k + 1 := hx
      have h1 := hq (graph τ x) (arr τ x) (2 * wtX x) (graph_ratio τ hτ x) (arr_represents τ hτ x)
        (hmc x (by omega))
      refine h1.trans (q.prob_mono _ _ _ ?_)
      intro n hn
      show 2 * k ≤ n
      omega)
    (by
      intro x hx
      have hx' : wtX x + 1 = k := hx
      have h1 := hq (graph τ x) (arr τ x) (2 * wtX x) (graph_ratio τ hτ x) (arr_represents τ hτ x)
        (hmc x (by omega))
      have h2 := q.prob_add_le (arr τ x) P (· = 2 * wtX x) (by
        intro n hn hn'
        have : 2 * k ≤ n := hn
        omega)
      linarith)
  rw [hcard] at hbound
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hkτ : (τ : ℝ) * t ≤ 4 * k := by
    have hnat : τ * t ≤ 4 * k := by
      have h1 : 2 * k + 3 ≥ m := by omega
      obtain ⟨r, hr⟩ : ∃ r, t = r + 9 := ⟨t - 9, by omega⟩
      have hm' : m = τ * (r + 8) := by
        rw [hm, hr]
        congr 1
      rw [hr]
      subst hr
      nlinarith
    exact_mod_cast hnat
  have hsq : (t : ℝ) * Real.sqrt t * Real.sqrt τ / 2 ≤ Real.sqrt (((t * t : ℕ) : ℝ) * k) := by
    apply Real.le_sqrt_of_sq_le
    have hs1 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hs2 : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have : ((t : ℝ) * Real.sqrt t * Real.sqrt τ / 2) ^ 2
        = (t : ℝ) * t * ((Real.sqrt t * Real.sqrt t) * (Real.sqrt τ * Real.sqrt τ)) / 4 := by ring
    rw [this, hs1, hs2]
    push_cast
    have ht2 : (0 : ℝ) ≤ (t : ℝ) * t := by positivity
    nlinarith
  have hfinal : c * ((t : ℝ) * Real.sqrt t * Real.sqrt τ / 2) ≤ ((2 * T : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hsq hc0.le).trans hbound
  push_cast at hfinal
  nlinarith

/-- **Lower bound.** Assuming the degree bound for exact counting, any quantum algorithm that computes the weight of
a minimum cut in the adjacency array model on `n = 4t` vertices, for all graphs with weights between `1` and `τ`,
`1 ≤ τ ≤ n/4`, makes `Ω(n^{3/2} √τ)` queries. For `τ = 1` the graphs are simple, and this is edge connectivity. -/
theorem minCut_bound (hc : CountDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ (t τ : ℕ) [NeZero t] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (q : QAlg (Vx t) T S), 1 ≤ τ → τ ≤ t → q.Computes τ →
      c * (((4 * t : ℕ) : ℝ) * Real.sqrt (4 * t : ℕ) * Real.sqrt τ) ≤ T + 1 := by
  obtain ⟨c, hc0, hc1⟩ := hc
  refine ⟨min (c / 128) (1 / 648), by positivity, ?_⟩
  intro t τ _ T S _ _ q hτ hτt hq
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hX : (0 : ℝ) ≤ ((4 * t : ℕ) : ℝ) * Real.sqrt (4 * t : ℕ) * Real.sqrt τ := by positivity
  by_cases ht : 9 ≤ t
  · have hbound := degree_from_algorithm hc0 hc1 t τ q ht hτ hτt hq
    have hs4 : Real.sqrt (4 * t : ℕ) = 2 * Real.sqrt t := by
      push_cast
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have hY : (0 : ℝ) ≤ (t : ℝ) * Real.sqrt t * Real.sqrt τ := by positivity
    have hX8 : ((4 * t : ℕ) : ℝ) * Real.sqrt (4 * t : ℕ) * Real.sqrt τ
        = 8 * ((t : ℝ) * Real.sqrt t * Real.sqrt τ) := by
      rw [hs4]
      push_cast
      ring
    calc _ ≤ c / 128 * (((4 * t : ℕ) : ℝ) * Real.sqrt (4 * t : ℕ) * Real.sqrt τ) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hX
      _ = c / 16 * ((t : ℝ) * Real.sqrt t * Real.sqrt τ) := by rw [hX8]; ring
      _ ≤ c / 4 * ((t : ℝ) * Real.sqrt t * Real.sqrt τ) :=
          mul_le_mul_of_nonneg_right (by linarith) hY
      _ ≤ T := hbound
      _ ≤ T + 1 := by linarith
  · have ht8 : t ≤ 8 := by omega
    have hτ8 : τ ≤ 8 := by omega
    have hs1 : Real.sqrt (4 * t : ℕ) ≤ 6 := by
      rw [show (6 : ℝ) = Real.sqrt 36 by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num]
        exact (Real.sqrt_sq (by norm_num)).symm]
      apply Real.sqrt_le_sqrt
      have : 4 * t ≤ 36 := by omega
      exact_mod_cast this
    have hs2 : Real.sqrt τ ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        exact (Real.sqrt_sq (by norm_num)).symm]
      apply Real.sqrt_le_sqrt
      have : τ ≤ 9 := by omega
      exact_mod_cast this
    have hn : ((4 * t : ℕ) : ℝ) ≤ 36 := by
      have : 4 * t ≤ 36 := by omega
      exact_mod_cast this
    have hprod : ((4 * t : ℕ) : ℝ) * Real.sqrt (4 * t : ℕ) * Real.sqrt τ ≤ 648 := by
      calc _ ≤ (36 : ℝ) * 6 * 3 := by
            apply mul_le_mul (mul_le_mul hn hs1 (Real.sqrt_nonneg _) (by norm_num)) hs2 (Real.sqrt_nonneg _)
            norm_num
        _ = 648 := by norm_num
    calc _ ≤ (1 / 648 : ℝ) * (((4 * t : ℕ) : ℝ) * Real.sqrt (4 * t : ℕ) * Real.sqrt τ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hX
      _ ≤ (1 / 648 : ℝ) * 648 := by gcongr
      _ = 1 := by norm_num
      _ ≤ T + 1 := by linarith

end MinCutArray
