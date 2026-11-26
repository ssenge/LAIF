import Mathlib

/-!
# A conjugation bound for sample-based Lindbladian simulation: the scalar steps

For d ≥ 3, the dual certificate behind the lower bound n ε ≥ (d−2)(cγ − ε/s)₊² splits into 2 × 2 blocks,
one for each excitation number k. This file proves the parts of that argument that are statements about real
numbers:

* `D_succ`, `inv_D_sub`: the dimensions D_k = dim Sym^k(C^{d−1}) = C(k+d−2, k) satisfy
  D_{k+1}(k+1) = D_k(k+d−1) and 1/D_k − 1/D_{k+1} = (d−2)/(D_k (k+d−1)).
* `binom_mean`: Σ_k k C(n,k) p^k (1−p)^{n−k} = n p.
* `block_posSemidef`: the 2 × 2 block [[x, g], [g, y + μ]] is positive semidefinite when x μ = g², y ≥ 0, μ > 0.
* `trace_certificate`: the trace of the certificate, Σ_{k<n} D_{k+1} x_{k+1} = n p/(λ(d−2)), with
  x_{k+1} = g_{k+1}²/(λ h_k), g_{k+1} = √(b_{k+1} b_k)/D_{k+1}, h_k = b_k (d−2)/(D_k (k+d−1)).
* `step5`: from X ≥ 2csγ − 2ε, Y ≤ ε and X − λY ≤ n s²/(λ(d−2)) for all λ > 0 follows
  (d−2)(cγ − ε/s)₊² ≤ n ε.
* `one_sub_exp_neg_ge`, `corollary_pi4`, `corollary_small_t`: the constants of the corollary at θ = π/4.
-/

namespace ConjugationBound

open Finset Real

/-- Dimension of the symmetric power Sym^k(C^{d−1}). -/
def D (d k : ℕ) : ℕ := (k + d - 2).choose k

theorem D_pos (d k : ℕ) (hd : 2 ≤ d) : 0 < D d k :=
  Nat.choose_pos (by omega)

theorem D_succ_nat (d k : ℕ) (hd : 2 ≤ d) : D d (k + 1) * (k + 1) = D d k * (k + d - 1) := by
  unfold D
  have h1 : k + 1 + d - 2 = (k + d - 2) + 1 := by omega
  have h2 : k + d - 1 = (k + d - 2) + 1 := by omega
  rw [h1, h2, ← Nat.add_one_mul_choose_eq]
  ring

theorem D_succ (d k : ℕ) (hd : 2 ≤ d) :
    (D d (k + 1) : ℝ) * (k + 1) = D d k * ((k : ℝ) + d - 1) := by
  have h := D_succ_nat d k hd
  have e : ((k + d - 1 : ℕ) : ℝ) = (k : ℝ) + d - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [← e]; exact_mod_cast h

theorem inv_D_sub (d k : ℕ) (hd : 2 ≤ d) :
    1 / (D d k : ℝ) - 1 / (D d (k + 1) : ℝ) = ((d : ℝ) - 2) / ((D d k : ℝ) * ((k : ℝ) + d - 1)) := by
  have h0 : (0 : ℝ) < D d k := by exact_mod_cast D_pos d k hd
  have h1 : (0 : ℝ) < D d (k + 1) := by exact_mod_cast D_pos d (k + 1) hd
  have hk : (0 : ℝ) < (k : ℝ) + d - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hs := D_succ d k hd
  field_simp
  nlinarith [hs]

/-- Mean of the binomial distribution. -/
theorem binom_mean (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) * (n.choose k) * p ^ k * (1 - p) ^ (n - k) = n * p := by
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ']
    have key : ∀ k ∈ range (m + 1),
        ((k + 1 : ℕ) : ℝ) * ((m + 1).choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (m + 1 - (k + 1))
          = ((m : ℝ) + 1) * p * (p ^ k * (1 - p) ^ (m - k) * (m.choose k : ℝ)) := by
      intro k _
      have h : ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) = ((m + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq m k
      have e : m + 1 - (k + 1) = m - k := by omega
      rw [e, pow_succ]
      push_cast at h ⊢
      linear_combination (-(p ^ k * p * (1 - p) ^ (m - k))) * h
    rw [sum_congr rfl key, ← mul_sum, ← add_pow]
    simp

/-- A 2 × 2 block [[x, g], [g, y + μ]] with x μ = g², y ≥ 0 and μ > 0 is positive semidefinite. -/
theorem block_posSemidef (x g y μ : ℝ) (hy : 0 ≤ y) (hμ : 0 < μ) (h : x * μ = g ^ 2) :
    Matrix.PosSemidef !![x, g; g, y + μ] := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro v
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    -- x a² + 2 g a b + (y + μ) b² ≥ 0, since μ (x a² + 2 g a b + μ b²) = (μ b + g a)² + 0
    have : 0 ≤ μ * (x * v 0 ^ 2 + 2 * g * v 0 * v 1 + μ * v 1 ^ 2) := by
      nlinarith [sq_nonneg (μ * v 1 + g * v 0)]
    have h2 : 0 ≤ x * v 0 ^ 2 + 2 * g * v 0 * v 1 + μ * v 1 ^ 2 := by
      by_contra hc; have hc' := not_le.mp hc; nlinarith [mul_neg_of_pos_of_neg hμ hc']
    nlinarith [mul_nonneg hy (sq_nonneg (v 1))]

/-- Binomial weights b_k = C(n,k) p^k (1−p)^{n−k}. -/
noncomputable def b (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := (n.choose k) * p ^ k * (1 - p) ^ (n - k)

/-- Weight of the cross term between excitation numbers k + 1 and k. -/
noncomputable def g (d n : ℕ) (p : ℝ) (k : ℕ) : ℝ := Real.sqrt (b n p (k + 1) * b n p k) / D d (k + 1)

/-- Diagonal weight of the term λ Π_v on the symmetric part, excitation number k. -/
noncomputable def h (d n : ℕ) (p : ℝ) (k : ℕ) : ℝ := b n p k * ((d : ℝ) - 2) / ((D d k : ℝ) * ((k : ℝ) + d - 1))

/-- Coefficient of the certificate on the excitation-(k+1) sector. -/
noncomputable def x (d n : ℕ) (p lam : ℝ) (k : ℕ) : ℝ := g d n p k ^ 2 / (lam * h d n p k)

theorem b_pos (n : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : k ≤ n) : 0 < b n p k := by
  unfold b
  have : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have : (0 : ℝ) < 1 - p := by linarith
  positivity

theorem b_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ b n p k := by
  unfold b
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

/-- The blocks satisfy x_{k+1} · λ h_k = g_{k+1}². -/
theorem x_mul (d n : ℕ) (p lam : ℝ) (k : ℕ) (hd : 3 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) (hk : k < n)
    (hlam : 0 < lam) : x d n p lam k * (lam * h d n p k) = g d n p k ^ 2 := by
  have hb : 0 < b n p k := b_pos n p hp0 hp1 k hk.le
  have h0 : (0 : ℝ) < D d k := by exact_mod_cast D_pos d k (by omega)
  have hd' : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk' : (0 : ℝ) < (k : ℝ) + d - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hh : 0 < lam * h d n p k := mul_pos hlam (div_pos (mul_pos hb hd') (mul_pos h0 hk'))
  unfold x; rw [div_mul_cancel₀ _ hh.ne']

/-- One summand of the trace: D_{k+1} x_{k+1} = (k+1) b_{k+1}/(λ(d−2)). -/
theorem D_mul_x (d n : ℕ) (p lam : ℝ) (k : ℕ) (hd : 3 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) (hk : k < n)
    (hlam : 0 < lam) :
    (D d (k + 1) : ℝ) * x d n p lam k = ((k : ℝ) + 1) * b n p (k + 1) / (lam * ((d : ℝ) - 2)) := by
  have hb : 0 < b n p k := b_pos n p hp0 hp1 k hk.le
  have hb1 : 0 ≤ b n p (k + 1) := b_nonneg n p hp0.le hp1.le (k + 1)
  have h0 : (0 : ℝ) < D d k := by exact_mod_cast D_pos d k (by omega)
  have h1 : (0 : ℝ) < D d (k + 1) := by exact_mod_cast D_pos d (k + 1) (by omega)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd' : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hk' : (0 : ℝ) < (k : ℝ) + d - 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hs := D_succ d k (by omega)
  unfold x g h
  rw [div_pow, Real.sq_sqrt (mul_nonneg hb1 hb.le)]
  field_simp
  linear_combination (-(b n p (k + 1))) * hs

/-- The trace of the certificate: Σ_{k<n} D_{k+1} x_{k+1} = n p/(λ(d−2)). -/
theorem trace_certificate (d n : ℕ) (p lam : ℝ) (hd : 3 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) (hlam : 0 < lam) :
    ∑ k ∈ range n, (D d (k + 1) : ℝ) * x d n p lam k = n * p / (lam * ((d : ℝ) - 2)) := by
  rw [sum_congr rfl (fun k hk => D_mul_x d n p lam k hd hp0 hp1 (mem_range.1 hk) hlam), ← sum_div]
  congr 1
  have hm := binom_mean n p
  rw [sum_range_succ'] at hm
  simp only [CharP.cast_eq_zero, zero_mul, add_zero] at hm
  rw [← hm]
  refine sum_congr rfl (fun k _ => ?_)
  unfold b; push_cast; ring

/-- The last step: the two tests and the certificate bound give (d−2)(cγ − ε/s)₊² ≤ n ε. -/
theorem step5 {n d s c γ ε X Y : ℝ} (hn : 0 < n) (hd : 3 ≤ d) (hs : 0 < s)
    (hX : 2 * c * s * γ - 2 * ε ≤ X) (hY : Y ≤ ε) (hε : 0 ≤ ε)
    (hcert : ∀ lam : ℝ, 0 < lam → X - lam * Y ≤ n * s ^ 2 / (lam * (d - 2))) :
    (d - 2) * (max (c * γ - ε / s) 0) ^ 2 ≤ n * ε := by
  have hd2 : 0 < d - 2 := by linarith
  rcases le_or_gt (c * γ - ε / s) 0 with hm | hm
  · rw [max_eq_right hm]; simp; positivity
  · rw [max_eq_left hm.le]
    set m := c * γ - ε / s with hmdef
    have hXm : 2 * s * m ≤ X := by
      have : 2 * s * m = 2 * c * s * γ - 2 * ε := by
        rw [hmdef]; field_simp
      linarith
    have hXpos : 0 < X := by nlinarith
    -- λ = 2 n s²/(X (d−2)) gives X/2 ≤ λ Y, i.e. X² (d−2) ≤ 4 n s² Y
    have hlam : 0 < 2 * n * s ^ 2 / (X * (d - 2)) := by positivity
    have h1 := hcert _ hlam
    have e : n * s ^ 2 / (2 * n * s ^ 2 / (X * (d - 2)) * (d - 2)) = X / 2 := by
      field_simp
    rw [e] at h1
    have h2 : X ^ 2 * (d - 2) ≤ 4 * n * s ^ 2 * Y := by
      have h3 : X / 2 ≤ 2 * n * s ^ 2 / (X * (d - 2)) * Y := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h3
      nlinarith [h3]
    have h4 : (2 * s * m) ^ 2 ≤ X ^ 2 := by
      have : 0 ≤ 2 * s * m := by positivity
      nlinarith
    have h5 : 4 * s ^ 2 * ((d - 2) * m ^ 2) ≤ 4 * s ^ 2 * (n * ε) := by
      nlinarith [mul_le_mul_of_nonneg_right h4 hd2.le, mul_le_mul_of_nonneg_left hY (by positivity : (0:ℝ) ≤ 4 * n * s ^ 2)]
    have hs4 : 0 < 4 * s ^ 2 := by positivity
    exact le_of_mul_le_mul_left h5 hs4

/-- At θ = π/4 (c = s, s² = 1/2): ε ≤ γ/4 gives (d−2) γ²/8 ≤ n ε. -/
theorem corollary_pi4 {n d s γ ε : ℝ} (hd : 3 ≤ d) (hs : 0 < s) (hs2 : s ^ 2 = 1 / 2) (hγ : 0 ≤ γ)
    (hε : ε ≤ γ / 4) (hmain : (d - 2) * (max (s * γ - ε / s) 0) ^ 2 ≤ n * ε) :
    (d - 2) * γ ^ 2 / 8 ≤ n * ε := by
  have hd2 : 0 ≤ d - 2 := by linarith
  have e : s * γ - ε / s = (γ / 2 - ε) / s := by field_simp; rw [hs2]; ring
  have hpos : 0 ≤ (γ / 2 - ε) / s := by apply div_nonneg <;> linarith
  rw [e, max_eq_left hpos, div_pow, hs2] at hmain
  have : γ ^ 2 / 8 ≤ (γ / 2 - ε) ^ 2 / (1 / 2) := by
    have h1 : γ / 4 ≤ γ / 2 - ε := by linarith
    have h2 : 0 ≤ γ / 4 := by linarith
    have : (γ / 4) ^ 2 ≤ (γ / 2 - ε) ^ 2 := pow_le_pow_left₀ h2 h1 2
    rw [div_div_eq_mul_div]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hd2]

/-- 1 − e^{−t} ≥ 0.632 t for 0 ≤ t ≤ 1, by convexity of exp. -/
theorem one_sub_exp_neg_ge (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0.632 * t ≤ 1 - exp (-t) := by
  have hc := convexOn_exp.2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ (0 : ℝ)) h0 (by linarith : 0 ≤ 1 - t)
    (by ring : t + (1 - t) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hc
  have he := Real.exp_neg_one_lt_d9
  have : t * (-1) = -t := by ring
  rw [this] at hc
  nlinarith

/-- With γ = (1 − e^{−t})/2 (the value at θ = π/4), t ≤ 1 and ε ≤ 0.079 t, the bound (d−2)γ²/8 ≤ n ε gives
0.0124 (d−2) t² ≤ n ε. -/
theorem corollary_small_t {n d t ε : ℝ} (hd : 3 ≤ d) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hb : (d - 2) * ((1 - exp (-t)) / 2) ^ 2 / 8 ≤ n * ε) : 0.0124 * (d - 2) * t ^ 2 ≤ n * ε := by
  have hg := one_sub_exp_neg_ge t ht0.le ht1
  have hd2 : 0 ≤ d - 2 := by linarith
  have h1 : (0.316 * t) ^ 2 ≤ ((1 - exp (-t)) / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  nlinarith [mul_le_mul_of_nonneg_left h1 hd2]

/-- The accuracy condition of the corollary: ε ≤ 0.079 t implies ε ≤ γ/4 for γ = (1 − e^{−t})/2, t ≤ 1. -/
theorem small_t_accuracy {t ε : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε : ε ≤ 0.079 * t) :
    ε ≤ (1 - exp (-t)) / 2 / 4 := by
  have := one_sub_exp_neg_ge t ht0 ht1; linarith

/-! ### Content of the statements -/

/-- The hypotheses of `step5` can hold with a positive right-hand side. -/
theorem step5_satisfiable :
    ∃ n d s c γ ε X Y : ℝ, 0 < n ∧ 3 ≤ d ∧ 0 < s ∧ 2 * c * s * γ - 2 * ε ≤ X ∧ Y ≤ ε ∧ 0 ≤ ε ∧
      (∀ lam : ℝ, 0 < lam → X - lam * Y ≤ n * s ^ 2 / (lam * (d - 2))) ∧
      0 < (d - 2) * (max (c * γ - ε / s) 0) ^ 2 := by
  refine ⟨1, 3, 1, 1, 1, 2 / 5, 6 / 5, 2 / 5, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl,
    by norm_num, ?_, ?_⟩
  · intro lam hlam
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith [sq_nonneg (lam - 3 / 2)]
  · norm_num

/-- The conclusion of `step5` is not automatic: it fails for small ε when nothing else is assumed. -/
theorem step5_conclusion_can_fail :
    ¬ ((3 : ℝ) - 2) * (max (1 * 1 - (1 / 10) / 1) 0) ^ 2 ≤ 1 * (1 / 10) := by norm_num

/-- The dimension identity is not vacuous: at d = 3 the gap 1/D_k − 1/D_{k+1} is positive. -/
example : 1 / (D 3 0 : ℝ) - 1 / (D 3 1 : ℝ) = 1 / 2 := by
  rw [inv_D_sub 3 0 (by norm_num)]; norm_num [D]

end ConjugationBound
