import SigregDim.Atomic

/-!
# Exponential kernel profiles: blindness and separation

Two profiles in the normalized inner product `ρ` matter here.

* The SIGReg profile on the sphere of radius `√K`: `ρ ↦ ∫ exp (-K (1 - ρ) u) dν(u)`, where `ν` is the law of
  `a₁²` for a uniformly random direction `a`. The statements hold for every probability law `ν` on `[0, 1]`.
* The squared-exponential-kernel uniformity profile at inverse temperature `t`: `ρ ↦ exp (-2t (1 - ρ))`.

Both are power series in `ρ` with nonnegative coefficients, which gives cubic remainders on `[-1, 1]` and
hence, through `energy_near`, energies of isotropic finite laws that agree up to `O(1/K)`. The uniformity
profile equals `1` at `ρ = 1`, which gives the lower bound `1/m` for laws with `m` atoms.
-/

open Finset MeasureTheory Set Real

namespace SigregDim

variable {K m : ℕ}

/-- Cubic remainder of the exponential series on `[-1, 1]`. -/
lemma exp_remainder {y : ℝ} (hy : 0 ≤ y) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    |exp (y * ρ) - (1 + y * ρ + y ^ 2 / 2 * ρ ^ 2)| ≤ (exp y - 1 - y - y ^ 2 / 2) * |ρ| ^ 3 := by
  have hs : ∀ z : ℝ, HasSum (fun n => z ^ n / (n.factorial : ℝ)) (exp z) := fun z => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp z
  set β : ℕ → ℝ := fun n => y ^ n / (n.factorial : ℝ)
  have hβ : ∀ n, 0 ≤ β n := fun n => by positivity
  have hser : ∀ r, |r| ≤ 1 → HasSum (fun n => β n * r ^ n) (exp (y * r)) := fun r _ => by
    convert hs (y * r) using 1
    ext n; simp only [β]; rw [mul_pow]; ring
  have key := remainder_le_of_series hβ (hs y).summable hser ρ hρ
  have htail : ∑' n, β (n + 3) = exp y - 1 - y - y ^ 2 / 2 := by
    have := ((hasSum_nat_add_iff' 3).2 (hs y)).tsum_eq
    simp only [β] at this ⊢
    rw [this]
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have b0 : β 0 = 1 := by simp [β]
  have b1 : β 1 = y := by simp [β]
  have b2 : β 2 = y ^ 2 / 2 := by simp [β, Nat.factorial]
  rw [htail, b0, b1, b2] at key
  exact key

lemma exp_tail_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ exp y - 1 - y - y ^ 2 / 2 := by
  have := Real.quadratic_le_exp_of_nonneg hy
  linarith

/-- **Blindness of the uniformity loss.** For every isotropic finite law on the sphere, the squared-exponential-kernel
energy at inverse temperature `t` lies within `e^{-2t} (e^{2t} - 1 - 2t - 2t²) / K` of
`e^{-2t} (1 + 2t²/K)`. -/
theorem unif_energy_near (hK : 0 < K) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ} (h : IsoAtoms K m x p)
    {t : ℝ} (ht : 0 ≤ t) :
    |energy K x p (fun ρ => exp (-(2 * t) * (1 - ρ))) -
        (exp (-(2 * t)) + 2 * t ^ 2 * exp (-(2 * t)) / K)| ≤
      exp (-(2 * t)) * (exp (2 * t) - 1 - 2 * t - (2 * t) ^ 2 / 2) / K := by
  have hy : 0 ≤ 2 * t := by linarith
  have hE := exp_pos (-(2 * t))
  refine energy_near hK h (H₀ := exp (-(2 * t))) (H₁ := 2 * t * exp (-(2 * t)))
    (mul_nonneg hE.le (exp_tail_nonneg hy)) ?_
  intro ρ hρ
  have e : exp (-(2 * t) * (1 - ρ)) = exp (-(2 * t)) * exp (2 * t * ρ) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have := exp_remainder hy hρ
  calc |exp (-(2 * t)) * exp (2 * t * ρ) -
        (exp (-(2 * t)) + 2 * t * exp (-(2 * t)) * ρ + 2 * t ^ 2 * exp (-(2 * t)) * ρ ^ 2)|
      = exp (-(2 * t)) * |exp (2 * t * ρ) - (1 + 2 * t * ρ + (2 * t) ^ 2 / 2 * ρ ^ 2)| := by
        rw [← abs_of_pos hE, ← abs_mul, abs_of_pos hE]; congr 1; ring
    _ ≤ exp (-(2 * t)) * ((exp (2 * t) - 1 - 2 * t - (2 * t) ^ 2 / 2) * |ρ| ^ 3) :=
        mul_le_mul_of_nonneg_left this hE.le
    _ = _ := by ring

/-- **Separation by the uniformity loss.** A finite law on the sphere with `m` atoms has squared-exponential-kernel
energy at least `1/m`, at every inverse temperature. -/
theorem unif_energy_ge (hK : 0 < K) (hm : 0 < m) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ}
    (hp : ∀ j, 0 ≤ p j) (h1 : ∑ j, p j = 1) (hx : ∀ j, ∑ i, x j i ^ 2 = K) (t : ℝ) :
    1 / (m : ℝ) ≤ energy K x p (fun ρ => exp (-(2 * t) * (1 - ρ))) :=
  energy_ge_inv_card hK hm hp h1 hx (fun ρ _ => (exp_pos _).le) (by simp)

/-- The SIGReg profile on the sphere of radius `√K`, for a law `ν` of `a₁²`. -/
noncomputable def sigKernel (ν : Measure ℝ) (K : ℕ) (ρ : ℝ) : ℝ := ∫ u, exp (-(K * (1 - ρ) * u)) ∂ν

/-- Its power-series coefficients `βₙ = ∫ e^{-Ku} (Ku)ⁿ / n! dν`. -/
noncomputable def sigCoef (ν : Measure ℝ) (K n : ℕ) : ℝ :=
  ∫ u, exp (-(K * u)) * ((K * u) ^ n / (n.factorial : ℝ)) ∂ν

lemma integrable_of_cont {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable f ν := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc (0 : ℝ) 1))
  exact Integrable.of_bound hf.aestronglyMeasurable C (hν.mono fun u hu => hC u hu)

/-- Cubic remainder of the SIGReg profile, with constant `1`. -/
theorem sigKernel_remainder {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) 1) (K : ℕ) (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    |sigKernel ν K ρ - (sigCoef ν K 0 + sigCoef ν K 1 * ρ + sigCoef ν K 2 * ρ ^ 2)| ≤ 1 * |ρ| ^ 3 := by
  have I : ∀ f : ℝ → ℝ, Continuous f → Integrable f ν := fun f hf => integrable_of_cont hν hf
  set g : ℝ → ℝ := fun u => exp (-(K * (1 - ρ) * u)) -
    (exp (-(K * u)) * ((K * u) ^ 0 / (Nat.factorial 0 : ℝ)) +
      exp (-(K * u)) * ((K * u) ^ 1 / (Nat.factorial 1 : ℝ)) * ρ +
      exp (-(K * u)) * ((K * u) ^ 2 / (Nat.factorial 2 : ℝ)) * ρ ^ 2)
  have hg : sigKernel ν K ρ - (sigCoef ν K 0 + sigCoef ν K 1 * ρ + sigCoef ν K 2 * ρ ^ 2) = ∫ u, g u ∂ν := by
    unfold sigKernel sigCoef
    simp only [g]
    rw [integral_sub (I _ (by fun_prop)) (I _ (by fun_prop)),
      integral_add (I _ (by fun_prop)) (I _ (by fun_prop)),
      integral_add (I _ (by fun_prop)) (I _ (by fun_prop)), integral_mul_const, integral_mul_const]
  rw [hg, one_mul]
  have hb : ∀ᵐ u ∂ν, ‖g u‖ ≤ |ρ| ^ 3 := by
    filter_upwards [hν] with u hu
    have hy : 0 ≤ (K : ℝ) * u := mul_nonneg (Nat.cast_nonneg K) hu.1
    have hE := exp_pos (-(K * u))
    have e : exp (-(K * (1 - ρ) * u)) = exp (-(K * u)) * exp (K * u * ρ) := by
      rw [← Real.exp_add]; ring_nf
    have hgu : g u = exp (-(K * u)) * (exp (K * u * ρ) - (1 + K * u * ρ + (K * u) ^ 2 / 2 * ρ ^ 2)) := by
      simp only [g, e, Nat.factorial, Nat.cast_one, pow_zero, pow_one, div_one]
      norm_num; ring
    rw [Real.norm_eq_abs, hgu, abs_mul, abs_of_pos hE]
    have hr := exp_remainder hy hρ
    have hc : exp (-(K * u)) * (exp (K * u) - 1 - K * u - (K * u) ^ 2 / 2) ≤ 1 := by
      have h1 : exp (-(K * u)) * exp (K * u) = 1 := by rw [← Real.exp_add]; simp
      have h2 : 0 ≤ exp (-(K * u)) * (1 + K * u + (K * u) ^ 2 / 2) := by positivity
      nlinarith
    calc exp (-(K * u)) * |exp (K * u * ρ) - (1 + K * u * ρ + (K * u) ^ 2 / 2 * ρ ^ 2)|
        ≤ exp (-(K * u)) * ((exp (K * u) - 1 - K * u - (K * u) ^ 2 / 2) * |ρ| ^ 3) :=
          mul_le_mul_of_nonneg_left hr hE.le
      _ = (exp (-(K * u)) * (exp (K * u) - 1 - K * u - (K * u) ^ 2 / 2)) * |ρ| ^ 3 := by ring
      _ ≤ 1 * |ρ| ^ 3 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = |ρ| ^ 3 := one_mul _
  calc |∫ u, g u ∂ν| = ‖∫ u, g u ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ _, |ρ| ^ 3 ∂ν := norm_integral_le_of_norm_le (integrable_const _) hb
    _ = |ρ| ^ 3 := by simp

/-- **Cluster blindness of SIGReg.** For every isotropic finite law on the sphere of radius `√K`, the SIGReg
energy lies within `1/K` of `β₀ + β₂/K`; the number and position of the atoms do not enter. -/
theorem sigreg_energy_near (hK : 0 < K) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ} (h : IsoAtoms K m x p)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) 1) :
    |energy K x p (sigKernel ν K) - (sigCoef ν K 0 + sigCoef ν K 2 / K)| ≤ 1 / K :=
  energy_near hK h zero_le_one (sigKernel_remainder hν K)

/-- Two isotropic finite laws on the sphere have SIGReg energies within `2/K` of each other. -/
theorem sigreg_energy_diff (hK : 0 < K) {m' : ℕ} {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ}
    {y : Fin m' → Fin K → ℝ} {q : Fin m' → ℝ} (hx : IsoAtoms K m x p) (hy : IsoAtoms K m' y q)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) 1) :
    |energy K x p (sigKernel ν K) - energy K y q (sigKernel ν K)| ≤ 2 * 1 / K :=
  energy_diff hK hx hy zero_le_one (sigKernel_remainder hν K)

/-- Sharper cubic remainder of the SIGReg profile: the constant is the tail `1 - β₀ - β₁ - β₂`. -/
theorem sigKernel_remainder_tail {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) 1) (K : ℕ) (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    |sigKernel ν K ρ - (sigCoef ν K 0 + sigCoef ν K 1 * ρ + sigCoef ν K 2 * ρ ^ 2)| ≤
      (1 - sigCoef ν K 0 - sigCoef ν K 1 - sigCoef ν K 2) * |ρ| ^ 3 := by
  have I : ∀ f : ℝ → ℝ, Continuous f → Integrable f ν := fun f hf => integrable_of_cont hν hf
  set c : ℕ → ℝ → ℝ := fun n u => exp (-(K * u)) * ((K * u) ^ n / (n.factorial : ℝ))
  set g : ℝ → ℝ := fun u => exp (-(K * (1 - ρ) * u)) - (c 0 u + c 1 u * ρ + c 2 u * ρ ^ 2)
  set T : ℝ → ℝ := fun u => (1 - c 0 u - c 1 u - c 2 u) * |ρ| ^ 3
  have hc : ∀ n, Continuous (c n) := fun n => by simp only [c]; fun_prop
  have hg : sigKernel ν K ρ - (sigCoef ν K 0 + sigCoef ν K 1 * ρ + sigCoef ν K 2 * ρ ^ 2) =
      ∫ u, g u ∂ν := by
    unfold sigKernel sigCoef
    simp only [g]
    rw [integral_sub (I _ (by fun_prop)) (I _ (by fun_prop)),
      integral_add (I _ (by fun_prop)) (I _ (by fun_prop)),
      integral_add (I _ (hc 0)) (I _ (by fun_prop)), integral_mul_const, integral_mul_const]
  have hT : ∫ u, T u ∂ν = (1 - sigCoef ν K 0 - sigCoef ν K 1 - sigCoef ν K 2) * |ρ| ^ 3 := by
    simp only [T]
    rw [integral_mul_const, integral_sub (I _ (by fun_prop)) (I _ (hc 2)),
      integral_sub (I _ (by fun_prop)) (I _ (hc 1)), integral_sub (I _ (by fun_prop)) (I _ (hc 0))]
    simp [sigCoef, c]
  rw [hg, ← hT]
  have hb : ∀ᵐ u ∂ν, ‖g u‖ ≤ T u := by
    filter_upwards [hν] with u hu
    have hy : 0 ≤ (K : ℝ) * u := mul_nonneg (Nat.cast_nonneg K) hu.1
    have hE := exp_pos (-(K * u))
    have e : exp (-(K * (1 - ρ) * u)) = exp (-(K * u)) * exp (K * u * ρ) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : exp (-(K * u)) * exp (K * u) = 1 := by rw [← Real.exp_add]; simp
    have hgu : g u = exp (-(K * u)) * (exp (K * u * ρ) - (1 + K * u * ρ + (K * u) ^ 2 / 2 * ρ ^ 2)) := by
      simp only [g, c, e, Nat.factorial, Nat.cast_one, pow_zero, pow_one, div_one]
      norm_num; ring
    have hTu : T u = exp (-(K * u)) * ((exp (K * u) - 1 - K * u - (K * u) ^ 2 / 2) * |ρ| ^ 3) := by
      simp only [T, c, Nat.factorial, Nat.cast_one, pow_zero, pow_one, div_one]
      norm_num
      linear_combination (-(|ρ| ^ 3)) * h1
    rw [Real.norm_eq_abs, hgu, abs_mul, abs_of_pos hE, hTu]
    exact mul_le_mul_of_nonneg_left (exp_remainder hy hρ) hE.le
  calc |∫ u, g u ∂ν| = ‖∫ u, g u ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u, T u ∂ν := norm_integral_le_of_norm_le (I _ (by simp only [T]; fun_prop)) hb

/-- `sigreg_energy_near` with the tail constant `1 - β₀ - β₁ - β₂` in place of `1`. -/
theorem sigreg_energy_near_tail (hK : 0 < K) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ}
    (h : IsoAtoms K m x p) {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) 1) :
    |energy K x p (sigKernel ν K) - (sigCoef ν K 0 + sigCoef ν K 2 / K)| ≤
      (1 - sigCoef ν K 0 - sigCoef ν K 1 - sigCoef ν K 2) / K := by
  have hC : 0 ≤ 1 - sigCoef ν K 0 - sigCoef ν K 1 - sigCoef ν K 2 := by
    have h := (abs_nonneg _).trans (sigKernel_remainder_tail hν K 1 (by simp))
    simpa using h
  exact energy_near hK h hC (sigKernel_remainder_tail hν K)

end SigregDim
