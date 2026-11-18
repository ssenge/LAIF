import LejepaDyn.Batch

/-!
# The expected minibatch statistic of SIGReg

For one slice, the statistic of a batch `X₁, …, X_N` at frequency `t` is `|φ_N(t) - φ₀(t)|²`, with the empirical
characteristic function `φ_N(t) = (1/N) Σⱼ e^{i t Xⱼ}` and the target `φ₀(t) = e^{-t²/2}`.

* `stat_pointwise`: for pairwise independent `Xⱼ` with common `E cos(t Xⱼ) = c` and `E sin(t Xⱼ) = s`,
  `N E|φ_N(t) - a|² = N ((c - a)² + s²) + 1 - c² - s²` for every real `a`.
* `stat_pointwise_gaussian`: for `Xⱼ ~ N(0, v)`, `N E|φ_N(t) - φ₀(t)|² = N (e^{-v t²/2} - e^{-t²/2})² + 1 - e^{-v t²}`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter

namespace LejepaDyn

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `E[((1/N) Σⱼ Yⱼ - a)²] = (m - a)² + (1/N²) Σⱼ Var Yⱼ` for pairwise independent `Yⱼ` with mean `m`. -/
lemma mean_sq_dev {N : ℕ} (hN : 0 < N) {Y : Fin N → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 P)
    (hind : Pairwise fun i j => IndepFun (Y i) (Y j) P) {m : ℝ} (hm : ∀ j, ∫ ω, Y j ω ∂P = m) (a : ℝ) :
    ∫ ω, ((1 / N : ℝ) * ∑ j, Y j ω - a) ^ 2 ∂P = (m - a) ^ 2 + 1 / (N : ℝ) ^ 2 * ∑ j, variance (Y j) P := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hS : MemLp (fun ω => ∑ j, Y j ω) 2 P := memLp_finsetSum _ fun j _ => hY j
  have hZ0 : MemLp (fun ω => (1 / N : ℝ) * ∑ j, Y j ω) 2 P := hS.const_mul _
  have hZ : MemLp (fun ω => (1 / N : ℝ) * ∑ j, Y j ω - a) 2 P := hZ0.sub (memLp_const a)
  have hEZ : ∫ ω, ((1 / N : ℝ) * ∑ j, Y j ω - a) ∂P = m - a := by
    rw [integral_sub (hZ0.integrable one_le_two) (integrable_const a), integral_const_mul,
      integral_finsetSum _ fun j _ => (hY j).integrable one_le_two]
    simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, integral_const,
      probReal_univ, smul_eq_mul, one_mul]
    field_simp
  have hVS : variance (fun ω => ∑ j, Y j ω) P = ∑ j, variance (Y j) P := by
    have := IndepFun.variance_sum (s := Finset.univ) (fun j _ => hY j) (fun i _ j _ hij => hind hij)
    convert this using 2; ext ω; simp
  have hV : variance (fun ω => (1 / N : ℝ) * ∑ j, Y j ω - a) P = 1 / (N : ℝ) ^ 2 * ∑ j, variance (Y j) P := by
    have := variance_add_const hZ0.aestronglyMeasurable (-a)
    simp only [← sub_eq_add_neg] at this
    rw [this, variance_const_mul, hVS]; ring
  have h := variance_eq_sub hZ
  rw [hV, hEZ] at h
  have e : P[(fun ω => (1 / N : ℝ) * ∑ j, Y j ω - a) ^ 2] = ∫ ω, ((1 / N : ℝ) * ∑ j, Y j ω - a) ^ 2 ∂P := rfl
  rw [e] at h
  linarith

lemma memLp_cos {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) : MemLp (fun ω => cos (t * X ω)) 2 P :=
  MemLp.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact abs_cos_le_one _)

lemma memLp_sin {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) : MemLp (fun ω => sin (t * X ω)) 2 P :=
  MemLp.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact abs_sin_le_one _)

/-- **Pointwise identity.** `N E[(C̄ - a)² + S̄²] = N ((c - a)² + s²) + 1 - c² - s²` with `C̄, S̄` the means of
`cos(t Xⱼ)` and `sin(t Xⱼ)`. -/
theorem stat_pointwise {N : ℕ} (hN : 0 < N) {X : Fin N → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) P) {t c s : ℝ}
    (hc : ∀ j, ∫ ω, cos (t * X j ω) ∂P = c) (hs : ∀ j, ∫ ω, sin (t * X j ω) ∂P = s) (a : ℝ) :
    N * ∫ ω, (((1 / N : ℝ) * ∑ j, cos (t * X j ω) - a) ^ 2 + ((1 / N : ℝ) * ∑ j, sin (t * X j ω)) ^ 2) ∂P =
      N * ((c - a) ^ 2 + s ^ 2) + (1 - c ^ 2 - s ^ 2) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have mC : ∀ j, MemLp (fun ω => cos (t * X j ω)) 2 P := fun j => memLp_cos (hX j) t
  have mS : ∀ j, MemLp (fun ω => sin (t * X j ω)) 2 P := fun j => memLp_sin (hX j) t
  have iC : Pairwise fun i j => IndepFun (fun ω => cos (t * X i ω)) (fun ω => cos (t * X j ω)) P :=
    fun i j hij => (hind hij).comp (φ := fun x => cos (t * x)) (ψ := fun x => cos (t * x)) (by fun_prop)
      (by fun_prop)
  have iS : Pairwise fun i j => IndepFun (fun ω => sin (t * X i ω)) (fun ω => sin (t * X j ω)) P :=
    fun i j hij => (hind hij).comp (φ := fun x => sin (t * x)) (ψ := fun x => sin (t * x)) (by fun_prop)
      (by fun_prop)
  have h1 := mean_sq_dev hN mC iC hc a
  have h2 := mean_sq_dev hN mS iS hs 0
  simp only [sub_zero] at h2
  have q1 : Integrable (fun ω => ((1 / N : ℝ) * ∑ j, cos (t * X j ω) - a) ^ 2) P :=
    (((memLp_finsetSum _ fun j _ => mC j).const_mul _).sub (memLp_const a)).integrable_sq
  have q2 : Integrable (fun ω => ((1 / N : ℝ) * ∑ j, sin (t * X j ω)) ^ 2) P :=
    ((memLp_finsetSum _ fun j _ => mS j).const_mul _).integrable_sq
  have hv : ∀ j, variance (fun ω => cos (t * X j ω)) P + variance (fun ω => sin (t * X j ω)) P =
      1 - c ^ 2 - s ^ 2 := by
    intro j
    rw [variance_eq_sub (mC j), variance_eq_sub (mS j)]
    have e1 : P[(fun ω => cos (t * X j ω)) ^ 2] + P[(fun ω => sin (t * X j ω)) ^ 2] = 1 := by
      simp only [Pi.pow_apply]
      rw [← integral_add (mC j).integrable_sq (mS j).integrable_sq]
      simp [Pi.pow_apply, cos_sq_add_sin_sq]
    have e2 : P[fun ω => cos (t * X j ω)] = c := hc j
    have e3 : P[fun ω => sin (t * X j ω)] = s := hs j
    rw [e2, e3]; linarith
  rw [integral_add q1 q2, h1, h2]
  have hsum : ∑ j, variance (fun ω => cos (t * X j ω)) P + ∑ j, variance (fun ω => sin (t * X j ω)) P =
      N * (1 - c ^ 2 - s ^ 2) := by
    rw [← Finset.sum_add_distrib]; simp [hv]; ring
  have key : 1 / (N : ℝ) ^ 2 * ∑ j, variance (fun ω => cos (t * X j ω)) P +
      1 / (N : ℝ) ^ 2 * ∑ j, variance (fun ω => sin (t * X j ω)) P = 1 / N * (1 - c ^ 2 - s ^ 2) := by
    rw [← mul_add, hsum]; field_simp
  calc (N : ℝ) * ((c - a) ^ 2 + 1 / (N : ℝ) ^ 2 * ∑ j, variance (fun ω => cos (t * X j ω)) P +
        (s ^ 2 + 1 / (N : ℝ) ^ 2 * ∑ j, variance (fun ω => sin (t * X j ω)) P))
      = N * ((c - a) ^ 2 + s ^ 2) + N * (1 / (N : ℝ) ^ 2 * ∑ j, variance (fun ω => cos (t * X j ω)) P +
        1 / (N : ℝ) ^ 2 * ∑ j, variance (fun ω => sin (t * X j ω)) P) := by ring
    _ = _ := by rw [key, ← mul_assoc, mul_one_div_cancel hNr, one_mul]

/-- `E cos(t X) = e^{-v t²/2}` and `E sin(t X) = 0` for `X ~ N(0, v)`. -/
lemma integral_cos_sin_gaussian (v : NNReal) (t : ℝ) :
    ∫ x, cos (t * x) ∂(gaussianReal 0 v) = exp (-(v * t ^ 2 / 2)) ∧
      ∫ x, sin (t * x) ∂(gaussianReal 0 v) = 0 := by
  have h := charFun_gaussianReal (μ := 0) (v := v) t
  rw [charFun_apply_real] at h
  have hi : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) (gaussianReal 0 v) := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => ?_)
    rw [show (t : ℂ) * x * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have k1 := integral_re hi
  have k2 := integral_im hi
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at k1 k2
  rw [← k1] at hre
  rw [← k2] at him
  have e : ∀ x : ℝ, (t : ℂ) * x * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I := fun x => by push_cast; ring
  simp only [e, RCLike.re_to_complex, RCLike.im_to_complex, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im] at hre him
  have e2 : ((t * 0 : ℝ) : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2 = ((-(v * t ^ 2 / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e2, Complex.exp_ofReal_re] at hre
  rw [e2, Complex.exp_ofReal_im] at him
  exact ⟨hre, him⟩

/-- **Gaussian batch.** For pairwise independent `Xⱼ ~ N(0, v)`,
`N E|φ_N(t) - e^{-t²/2}|² = N (e^{-v t²/2} - e^{-t²/2})² + 1 - e^{-v t²}`. -/
theorem stat_pointwise_gaussian {N : ℕ} (hN : 0 < N) {X : Fin N → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) P) {v : NNReal} (hlaw : ∀ j, P.map (X j) = gaussianReal 0 v)
    (t : ℝ) :
    N * ∫ ω, (((1 / N : ℝ) * ∑ j, cos (t * X j ω) - exp (-(t ^ 2 / 2))) ^ 2 +
        ((1 / N : ℝ) * ∑ j, sin (t * X j ω)) ^ 2) ∂P =
      N * (exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 + (1 - exp (-(v * t ^ 2))) := by
  obtain ⟨gc, gs⟩ := integral_cos_sin_gaussian v t
  have hc : ∀ j, ∫ ω, cos (t * X j ω) ∂P = exp (-(v * t ^ 2 / 2)) := fun j => by
    rw [← gc, ← hlaw j, integral_map (hX j).aemeasurable (by fun_prop)]
  have hs : ∀ j, ∫ ω, sin (t * X j ω) ∂P = 0 := fun j => by
    rw [← gs, ← hlaw j, integral_map (hX j).aemeasurable (by fun_prop)]
  rw [stat_pointwise hN hX hind hc hs]
  have : exp (-(v * t ^ 2 / 2)) ^ 2 = exp (-(v * t ^ 2)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]; ring

/-! ## The integrals over the frequency -/

open SigregDim in
/-- `∫ e^{-a t² / 2} dt = √(2π) a^{-1/2}` for `a > 0`. -/
lemma integral_exp_half {a : ℝ} (ha : 0 < a) : ∫ t : ℝ, exp (-(a / 2) * t ^ 2) = √(2 * π) * a ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussian, show π / (a / 2) = 2 * π / a by field_simp, Real.sqrt_div' _ ha.le,
    Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

lemma integrable_exp_half {a : ℝ} (ha : 0 < a) : Integrable fun t : ℝ => exp (-(a / 2) * t ^ 2) :=
  integrable_exp_neg_mul_sq (by positivity)

open SigregDim in
/-- `∫ e^{-t²/2} (e^{-v t²/2} - e^{-t²/2})² dt = D(v)`. -/
lemma integral_weight_D (v : ℝ) (hv : 0 ≤ v) :
    ∫ t : ℝ, exp (-(t ^ 2 / 2)) * (exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 = epD v := by
  have e : ∀ t : ℝ, exp (-(t ^ 2 / 2)) * (exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 =
      exp (-((2 * v + 1) / 2) * t ^ 2) - 2 * exp (-((v + 2) / 2) * t ^ 2) + exp (-(3 / 2) * t ^ 2) := by
    intro t
    have h1 : exp (-(t ^ 2 / 2)) * exp (-(v * t ^ 2 / 2)) ^ 2 = exp (-((2 * v + 1) / 2) * t ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    have h2 : exp (-(t ^ 2 / 2)) * (exp (-(v * t ^ 2 / 2)) * exp (-(t ^ 2 / 2))) =
        exp (-((v + 2) / 2) * t ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h3 : exp (-(t ^ 2 / 2)) * exp (-(t ^ 2 / 2)) ^ 2 = exp (-(3 / 2) * t ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [← h1, ← h2, ← h3]; ring
  simp_rw [e]
  have i1 := integrable_exp_half (a := 2 * v + 1) (by linarith)
  have i2 := (integrable_exp_half (a := v + 2) (by linarith)).const_mul 2
  have i3 := integrable_exp_half (a := 3) (by norm_num)
  have i12 : Integrable (fun t : ℝ => exp (-((2 * v + 1) / 2) * t ^ 2) - 2 * exp (-((v + 2) / 2) * t ^ 2)) :=
    i1.sub i2
  rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
    integral_exp_half (by linarith), integral_exp_half (by linarith),
    show (-(3 / 2 : ℝ)) = -((3 : ℝ) / 2) by norm_num, integral_exp_half (by norm_num)]
  unfold epD
  rw [show (v + 2) = 1 * v + 2 by ring]; simp only [one_mul]; ring

open SigregDim in
/-- `∫ e^{-t²/2} (1 - e^{-v t²}) dt = B(v)`. -/
lemma integral_weight_B (v : ℝ) (hv : 0 ≤ v) :
    ∫ t : ℝ, exp (-(t ^ 2 / 2)) * (1 - exp (-(v * t ^ 2))) = epB v := by
  have e : ∀ t : ℝ, exp (-(t ^ 2 / 2)) * (1 - exp (-(v * t ^ 2))) =
      exp (-((1 : ℝ) / 2) * t ^ 2) - exp (-((2 * v + 1) / 2) * t ^ 2) := by
    intro t
    rw [mul_sub, mul_one, ← Real.exp_add]; congr 2 <;> ring
  simp_rw [e]
  rw [integral_sub (integrable_exp_half one_pos) (integrable_exp_half (by linarith)),
    integral_exp_half one_pos, integral_exp_half (by linarith), Real.one_rpow]
  unfold epB; ring

/-! ## The expected statistic -/

open SigregDim in
/-- **Expected minibatch statistic.** For pairwise independent `Xⱼ ~ N(0, v)`, `j < N`, the expected value of `N`
times the statistic `∫ e^{-t²/2} |φ_N(t) - e^{-t²/2}|² dt` is `N D(v) + B(v)`. -/
theorem expected_stat_gaussian {N : ℕ} (hN : 0 < N) {X : Fin N → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) P) {v : NNReal}
    (hlaw : ∀ j, P.map (X j) = gaussianReal 0 v) :
    ∫ ω, (N : ℝ) * (∫ t : ℝ, exp (-(t ^ 2 / 2)) * (((1 / N : ℝ) * ∑ j, cos (t * X j ω) - exp (-(t ^ 2 / 2))) ^ 2 +
        ((1 / N : ℝ) * ∑ j, sin (t * X j ω)) ^ 2)) ∂P = N * epD v + epB v := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set g : Ω → ℝ → ℝ := fun ω t => ((1 / N : ℝ) * ∑ j, cos (t * X j ω) - exp (-(t ^ 2 / 2))) ^ 2 +
    ((1 / N : ℝ) * ∑ j, sin (t * X j ω)) ^ 2 with hg
  have gle : ∀ ω t, 0 ≤ g ω t ∧ g ω t ≤ 5 := by
    intro ω t
    have hc : |(1 / N : ℝ) * ∑ j, cos (t * X j ω)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
      calc 1 / (N : ℝ) * |∑ j, cos (t * X j ω)| ≤ 1 / N * ∑ j : Fin N, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => abs_cos_le_one _)) (by positivity)
        _ = 1 := by simp; field_simp
    have hs : |(1 / N : ℝ) * ∑ j, sin (t * X j ω)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
      calc 1 / (N : ℝ) * |∑ j, sin (t * X j ω)| ≤ 1 / N * ∑ j : Fin N, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => abs_sin_le_one _)) (by positivity)
        _ = 1 := by simp; field_simp
    have he0 : 0 < exp (-(t ^ 2 / 2)) := exp_pos _
    have he1 : exp (-(t ^ 2 / 2)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
    obtain ⟨c1, c2⟩ := abs_le.1 hc
    obtain ⟨s1, s2⟩ := abs_le.1 hs
    constructor
    · positivity
    · simp only [hg]; nlinarith
  have hmeas : Measurable (Function.uncurry fun ω t => exp (-(t ^ 2 / 2)) * g ω t) := by
    have hXj : ∀ j, Measurable fun p : Ω × ℝ => X j p.1 := fun j => (hX j).comp measurable_fst
    simp only [hg, Function.uncurry_def]
    fun_prop
  have hint : Integrable (Function.uncurry fun ω t => exp (-(t ^ 2 / 2)) * g ω t) (P.prod volume) := by
    refine Integrable.mono' (((integrable_exp_half one_pos).const_mul 5).comp_snd P) hmeas.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    obtain ⟨g0, g5⟩ := gle z.1 z.2
    simp only [Function.uncurry, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (exp_pos _).le g0)]
    have : exp (-(z.2 ^ 2 / 2)) = exp (-((1 : ℝ) / 2) * z.2 ^ 2) := by congr 1; ring
    rw [← this]; nlinarith [exp_pos (-(z.2 ^ 2 / 2))]
  rw [integral_const_mul, integral_integral_swap hint]
  have inner : ∀ t : ℝ, ∫ ω, exp (-(t ^ 2 / 2)) * g ω t ∂P =
      exp (-(t ^ 2 / 2)) * ((exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 + (1 - exp (-(v * t ^ 2))) / N) := by
    intro t
    rw [integral_const_mul]
    have := stat_pointwise_gaussian hN hX hind hlaw t
    congr 1
    field_simp
    linarith
  simp_rw [inner]
  have hw : ∀ t : ℝ, exp (-(t ^ 2 / 2)) = exp (-((1 : ℝ) / 2) * t ^ 2) := fun t => by congr 1; ring
  have hv0 : (0 : ℝ) ≤ v := NNReal.coe_nonneg v
  have e1 : ∀ t : ℝ, exp (-(v * t ^ 2 / 2)) ≤ 1 := fun t =>
    exp_le_one_iff.2 (by nlinarith [mul_nonneg hv0 (sq_nonneg t)])
  have e2 : ∀ t : ℝ, exp (-(t ^ 2 / 2)) ≤ 1 := fun t => exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  have e3 : ∀ t : ℝ, exp (-(v * t ^ 2)) ≤ 1 := fun t =>
    exp_le_one_iff.2 (by nlinarith [mul_nonneg hv0 (sq_nonneg t)])
  have i1 : Integrable fun t : ℝ => exp (-(t ^ 2 / 2)) * (exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 := by
    refine Integrable.mono' (integrable_exp_half one_pos) (by fun_prop) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hw]
    have a0 := exp_pos (-(v * t ^ 2 / 2)); have b0 := exp_pos (-(t ^ 2 / 2))
    have : (exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 ≤ 1 := by nlinarith [e1 t, e2 t]
    nlinarith
  have i2 : Integrable fun t : ℝ => exp (-(t ^ 2 / 2)) * (1 - exp (-(v * t ^ 2))) := by
    refine Integrable.mono' (integrable_exp_half one_pos) (by fun_prop) (Eventually.of_forall fun t => ?_)
    have c0 := exp_pos (-(v * t ^ 2)); have b0 := exp_pos (-(t ^ 2 / 2))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg b0.le (by linarith [e3 t])), ← hw]
    nlinarith
  have split : ∀ t : ℝ, exp (-(t ^ 2 / 2)) * ((exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 +
      (1 - exp (-(v * t ^ 2))) / N) = exp (-(t ^ 2 / 2)) * (exp (-(v * t ^ 2 / 2)) - exp (-(t ^ 2 / 2))) ^ 2 +
      1 / N * (exp (-(t ^ 2 / 2)) * (1 - exp (-(v * t ^ 2)))) := fun t => by ring
  simp_rw [split]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, integral_weight_D v hv0, integral_weight_B v hv0]
  field_simp

end LejepaDyn
