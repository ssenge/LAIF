import SelfPred.Algebra

/-!
# Linear self-predictive learning: invariant subspaces that are not local maxima

Let the columns of `Φ₀` be orthonormal, let column `i` be an eigenvector of `T` with eigenvalue `μ`, and let `v` be a
unit eigenvector of `T` with eigenvalue `λ` orthogonal to the span of `Φ₀`. Turning column `i` by the angle `s`
towards `v`, `Φ(s) = Φ₀ + (cos s - 1) Φ₀ J + sin s V` with `J` the projection on coordinate `i` and `V` the matrix
with `v` in column `i`, keeps the columns orthonormal (`turn_orth`) and changes the predictor only in entry `(i, i)`:
`Q(Φ(s)) = Q(Φ₀) + (λ - μ) sin² s J` (`turn_Q`). So `f = tr Q²` changes by `2 c μ + c²` with `c = (λ - μ) sin² s`
(`turn_f`), which is positive for small `s ≠ 0` when `μ (λ - μ) > 0`. Hence such a span is not a local maximum of
`f` among orthonormal frames (`not_local_max`, Theorem 3 (ii)).
-/

set_option linter.unusedSectionVars false

open Matrix Real Filter Topology

namespace SelfPred

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- The objective `f(Φ) = tr Q²` with `Q = Φᵀ T Φ`. -/
def fobj (T : Matrix n n ℝ) (Φ : Matrix n k ℝ) : ℝ := trace (Qm T Φ * Qm T Φ)

/-- Column `i` of `Φ₀` turned by the angle `s` towards the column `i` of `V`. -/
noncomputable def turn (Φ₀ V : Matrix n k ℝ) (J : Matrix k k ℝ) (s : ℝ) : Matrix n k ℝ :=
  Φ₀ + (cos s - 1) • (Φ₀ * J) + sin s • V

section Hyp

variable {T : Matrix n n ℝ} {Φ₀ V : Matrix n k ℝ} {J : Matrix k k ℝ} {μ l : ℝ}

/-- The products that the expansion of `Q(Φ(s))` needs. -/
private lemma prods (hT : Tᵀ = T) (h1 : Φ₀ᵀ * Φ₀ = 1) (hJt : Jᵀ = J) (hJJ : J * J = J)
    (hu : T * (Φ₀ * J) = μ • (Φ₀ * J)) (hv : T * V = l • V) (hΦV : Φ₀ᵀ * V = 0) (hVV : Vᵀ * V = J) :
    Φ₀ᵀ * T * (Φ₀ * J) = μ • J ∧ (Φ₀ * J)ᵀ * T * Φ₀ = μ • J ∧ (Φ₀ * J)ᵀ * T * (Φ₀ * J) = μ • J ∧
    Φ₀ᵀ * T * V = 0 ∧ Vᵀ * T * Φ₀ = 0 ∧ (Φ₀ * J)ᵀ * T * V = 0 ∧ Vᵀ * T * (Φ₀ * J) = 0 ∧
    Vᵀ * T * V = l • J := by
  have a1 : Φ₀ᵀ * T * (Φ₀ * J) = μ • J := by
    rw [Matrix.mul_assoc, hu, Matrix.mul_smul, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have a2 : (Φ₀ * J)ᵀ * T * Φ₀ = μ • J := by
    have := congrArg transpose a1
    simpa [transpose_mul, hT, hJt, Matrix.mul_assoc, transpose_smul] using this
  have a4 : Φ₀ᵀ * T * V = 0 := by rw [Matrix.mul_assoc, hv, Matrix.mul_smul, hΦV, smul_zero]
  have a5 : Vᵀ * T * Φ₀ = 0 := by
    have := congrArg transpose a4
    simpa [transpose_mul, hT, Matrix.mul_assoc] using this
  refine ⟨a1, a2, ?_, a4, a5, ?_, ?_, ?_⟩
  · rw [transpose_mul, hJt, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φ₀ᵀ, a1, Matrix.mul_smul, hJJ]
  · rw [transpose_mul, hJt, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φ₀ᵀ, a4, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, a5, Matrix.zero_mul]
  · rw [Matrix.mul_assoc, hv, Matrix.mul_smul, hVV]

/-- The turned frame stays orthonormal. -/
theorem turn_orth (h1 : Φ₀ᵀ * Φ₀ = 1) (hJt : Jᵀ = J) (hJJ : J * J = J) (hΦV : Φ₀ᵀ * V = 0) (hVV : Vᵀ * V = J)
    (s : ℝ) : (turn Φ₀ V J s)ᵀ * turn Φ₀ V J s = 1 := by
  have b1 : Φ₀ᵀ * (Φ₀ * J) = J := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b2 : (Φ₀ * J)ᵀ * Φ₀ = J := by rw [transpose_mul, hJt, Matrix.mul_assoc, h1, Matrix.mul_one]
  have b3 : (Φ₀ * J)ᵀ * (Φ₀ * J) = J := by rw [transpose_mul, hJt, Matrix.mul_assoc, b1, hJJ]
  have b4 : Vᵀ * Φ₀ = 0 := by
    have := congrArg transpose hΦV; simpa [transpose_mul] using this
  have b5 : (Φ₀ * J)ᵀ * V = 0 := by rw [transpose_mul, hJt, Matrix.mul_assoc, hΦV, Matrix.mul_zero]
  have b6 : Vᵀ * (Φ₀ * J) = 0 := by rw [← Matrix.mul_assoc, b4, Matrix.zero_mul]
  have hs : (cos s - 1) * (cos s - 1) + 2 * (cos s - 1) + sin s * sin s = 0 := by
    linear_combination sin_sq_add_cos_sq s
  simp only [turn, transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, h1, b1, b2, b3, b4, b5, b6, hVV, hΦV, smul_zero, add_zero, zero_add]
  calc _ = (1 : Matrix k k ℝ) + ((cos s - 1) * (cos s - 1) + 2 * (cos s - 1) + sin s * sin s) • J := by module
    _ = 1 := by rw [hs, zero_smul, add_zero]

/-- The predictor of the turned frame: `Q(Φ(s)) = Q(Φ₀) + (λ - μ) sin² s J`. -/
theorem turn_Q (hT : Tᵀ = T) (h1 : Φ₀ᵀ * Φ₀ = 1) (hJt : Jᵀ = J) (hJJ : J * J = J)
    (hu : T * (Φ₀ * J) = μ • (Φ₀ * J)) (hv : T * V = l • V) (hΦV : Φ₀ᵀ * V = 0) (hVV : Vᵀ * V = J) (s : ℝ) :
    Qm T (turn Φ₀ V J s) = Qm T Φ₀ + ((l - μ) * sin s ^ 2) • J := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := prods hT h1 hJt hJJ hu hv hΦV hVV
  have hs : μ * ((cos s - 1) * (cos s - 1) + 2 * (cos s - 1)) + l * (sin s * sin s) = (l - μ) * sin s ^ 2 := by
    linear_combination μ * sin_sq_add_cos_sq s
  simp only [Qm, turn, transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, ← Matrix.mul_assoc]
  simp only [Matrix.mul_assoc] at a1 a2 a3 a4 a5 a6 a7 a8 ⊢
  rw [a1, a2, a3, a4, a5, a6, a7, a8]
  simp only [smul_zero, add_zero, zero_add, smul_smul]
  rw [← hs]
  module

/-- The change of the objective: `f(Φ(s)) - f(Φ₀) = 2 c μ + c²` with `c = (λ - μ) sin² s`, where `J` is the
projection on coordinate `i` and `μ` the eigenvalue of column `i`. -/
theorem turn_f (hT : Tᵀ = T) (h1 : Φ₀ᵀ * Φ₀ = 1) (i : k) (hJ : J = Matrix.single i i 1)
    (hu : T * (Φ₀ * J) = μ • (Φ₀ * J)) (hv : T * V = l • V) (hΦV : Φ₀ᵀ * V = 0) (hVV : Vᵀ * V = J) (s : ℝ) :
    fobj T (turn Φ₀ V J s) - fobj T Φ₀ =
      2 * ((l - μ) * sin s ^ 2) * μ + ((l - μ) * sin s ^ 2) ^ 2 := by
  have hJt : Jᵀ = J := by rw [hJ, Matrix.transpose_single]
  have hJJ : J * J = J := by rw [hJ, Matrix.single_mul_single_same, mul_one]
  have hQJ : Qm T Φ₀ * J = μ • J := by
    rw [Qm, Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_smul, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have htrJ : trace J = 1 := by rw [hJ, Matrix.trace_single_eq_same]
  set c := (l - μ) * sin s ^ 2
  rw [fobj, fobj, turn_Q hT h1 hJt hJJ hu hv hΦV hVV s]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, trace_add, trace_smul, hJJ, hQJ]
  have hJQ : trace (J * Qm T Φ₀) = trace (Qm T Φ₀ * J) := Matrix.trace_mul_comm _ _
  rw [hJQ, hQJ, trace_smul, htrJ]
  simp only [smul_eq_mul]
  ring

end Hyp

/-- Sign of the change: if `μ (λ - μ) > 0`, `sin s ≠ 0` and `sin² s |λ - μ| < |μ|`, the objective increases. -/
lemma change_pos {μ l x : ℝ} (hml : 0 < μ * (l - μ)) (hx : 0 < x) (hsmall : x * |l - μ| < |μ|) :
    0 < 2 * ((l - μ) * x) * μ + ((l - μ) * x) ^ 2 := by
  rcases lt_or_gt_of_ne (show μ ≠ 0 by rintro rfl; simp at hml) with hμ | hμ
  · have hl : l - μ < 0 := by nlinarith
    rw [abs_of_neg hl, abs_of_neg hμ] at hsmall
    nlinarith
  · have hl : 0 < l - μ := by nlinarith
    rw [abs_of_pos hl, abs_of_pos hμ] at hsmall
    nlinarith

/-- **Theorem 3 (ii).** If column `i` of an orthonormal frame `Φ₀` is an eigenvector of `T` with eigenvalue `μ`
and some unit eigenvector `v` with eigenvalue `λ` orthogonal to the span has `μ (λ - μ) > 0`, then every
neighbourhood of `Φ₀` contains an orthonormal frame with a larger objective: `Φ₀` is not a local maximum of `f`. -/
theorem not_local_max {T : Matrix n n ℝ} (hT : Tᵀ = T) {Φ₀ V : Matrix n k ℝ} (h1 : Φ₀ᵀ * Φ₀ = 1) (i : k)
    {μ l : ℝ} (hu : T * (Φ₀ * Matrix.single i i (1 : ℝ)) = μ • (Φ₀ * Matrix.single i i (1 : ℝ)))
    (hv : T * V = l • V) (hΦV : Φ₀ᵀ * V = 0) (hVV : Vᵀ * V = Matrix.single i i (1 : ℝ)) (hml : 0 < μ * (l - μ)) :
    ∀ U ∈ 𝓝 Φ₀, ∃ Φ ∈ U, Φᵀ * Φ = 1 ∧ fobj T Φ₀ < fobj T Φ := by
  intro U hU
  set J : Matrix k k ℝ := Matrix.single i i (1 : ℝ) with hJ
  have hJt : Jᵀ = J := by rw [hJ, Matrix.transpose_single]
  have hJJ : J * J = J := by rw [hJ, Matrix.single_mul_single_same, mul_one]
  have hcont : Continuous (turn Φ₀ V J) := by unfold turn; fun_prop
  have h0 : turn Φ₀ V J 0 = Φ₀ := by simp [turn]
  have hpre : turn Φ₀ V J ⁻¹' U ∈ 𝓝 (0 : ℝ) := hcont.continuousAt.preimage_mem_nhds (by rwa [h0])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  have hμ0 : 0 < |μ| := abs_pos.2 (by rintro rfl; simp at hml)
  set δ := min (ε / 2) (min 1 (Real.sqrt (|μ| / (|l - μ| + 1)) / 2)) with hδ
  have hδpos : 0 < δ := by
    refine lt_min (by linarith) (lt_min one_pos (by positivity))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδpos (by linarith [pi_gt_three])
  have hsinle : sin δ ≤ δ := sin_le hδpos.le
  have hδsq : δ ^ 2 * (|l - μ| + 1) < |μ| := by
    have hr : δ ≤ Real.sqrt (|μ| / (|l - μ| + 1)) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hq : 0 < |l - μ| + 1 := by positivity
    have hsq : Real.sqrt (|μ| / (|l - μ| + 1)) ^ 2 = |μ| / (|l - μ| + 1) := Real.sq_sqrt (by positivity)
    have : δ ^ 2 ≤ |μ| / (|l - μ| + 1) / 4 := by nlinarith [Real.sqrt_nonneg (|μ| / (|l - μ| + 1))]
    calc δ ^ 2 * (|l - μ| + 1) ≤ |μ| / (|l - μ| + 1) / 4 * (|l - μ| + 1) := by gcongr
      _ = |μ| / 4 := by field_simp
      _ < |μ| := by linarith
  have hx : sin δ ^ 2 * |l - μ| < |μ| := by
    have : sin δ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hsin.le hsinle 2
    nlinarith [abs_nonneg (l - μ)]
  refine ⟨turn Φ₀ V J δ, hball ?_, turn_orth h1 hJt hJJ hΦV hVV δ, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
    exact (min_le_left _ _).trans_lt (by linarith)
  · have := turn_f hT h1 i hJ hu hv hΦV hVV δ
    have hp := change_pos hml (pow_pos hsin 2) hx
    linarith

end SelfPred
