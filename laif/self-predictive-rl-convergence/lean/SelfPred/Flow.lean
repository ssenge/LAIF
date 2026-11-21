import SelfPred.Algebra

/-!
# Linear self-predictive learning: the flow

Along a solution `Φ : ℝ → Matrix n k ℝ` of `Φ' = (1 - Φ Φᵀ) T Φ Q` with symmetric `T` and `Φ(s)ᵀ Φ(s) = 1`:
* `stiefel`: `Φ(t)ᵀ Φ(t) = 1` for all `t`;
* `pred_conj`: `Q(t) = W Q(s) Wᵀ` with `Wᵀ W - 1` positive semidefinite for `t ≥ s`;
* `eig_scale` (Theorem 1): the eigenvalues of `Q(t)` and `Q(s)`, in the same order, satisfy
  `λᵢ(Q(t)) = θᵢ λᵢ(Q(s))` with `θᵢ ≥ 1`, so their signs are kept and their absolute values do not decrease;
* `abs_det_mono`: `|det Q(t)| ≥ |det Q(s)|`;
* `limit_invariant` (Theorem 2): a limit that is a critical point, reached from a nonsingular `Q(s)`, has a
  nonsingular predictor and a `T`-invariant span.

Two classical theorems enter as hypotheses: global existence for linear matrix differential equations
(`LinearODEGlobal`) and Ostrowski's theorem on congruences (`OstrowskiCongruence`).
-/

set_option linter.unusedSectionVars false

open Matrix Filter Topology

namespace SelfPred

section Deriv

variable {m l p : Type*} [Fintype m] [Fintype l] [Fintype p]

/-- Entrywise derivative of a matrix-valued function of time. -/
def HasMatDeriv (X : ℝ → Matrix m l ℝ) (X' : Matrix m l ℝ) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => X s i j) (X' i j) t

lemma HasMatDeriv.congr_deriv {X : ℝ → Matrix m l ℝ} {A B : Matrix m l ℝ} {t : ℝ}
    (h : HasMatDeriv X A t) (e : A = B) : HasMatDeriv X B t := e ▸ h

lemma HasMatDeriv.mul {X : ℝ → Matrix m l ℝ} {Y : ℝ → Matrix l p ℝ} {X' : Matrix m l ℝ}
    {Y' : Matrix l p ℝ} {t : ℝ} (hX : HasMatDeriv X X' t) (hY : HasMatDeriv Y Y' t) :
    HasMatDeriv (fun s => X s * Y s) (X' * Y t + X t * Y') t := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun r _ => (hX i r).mul (hY r j)

lemma HasMatDeriv.transpose {X : ℝ → Matrix m l ℝ} {X' : Matrix m l ℝ} {t : ℝ}
    (h : HasMatDeriv X X' t) : HasMatDeriv (fun s => (X s)ᵀ) X'ᵀ t := fun i j => by
  simpa only [transpose_apply] using h j i

lemma hasMatDeriv_const (A : Matrix m l ℝ) (t : ℝ) : HasMatDeriv (fun _ => A) 0 t := fun i j => by
  simpa using hasDerivAt_const t (A i j)

lemma HasMatDeriv.sub_const {X : ℝ → Matrix m l ℝ} {X' : Matrix m l ℝ} {t : ℝ}
    (h : HasMatDeriv X X' t) (A : Matrix m l ℝ) : HasMatDeriv (fun s => X s - A) X' t := fun i j => by
  simpa using (h i j).sub_const (A i j)

lemma continuous_of_hasMatDeriv {X : ℝ → Matrix m l ℝ} {X' : ℝ → Matrix m l ℝ}
    (h : ∀ t, HasMatDeriv X (X' t) t) : Continuous X :=
  continuous_matrix fun i j => continuous_iff_continuousAt.2 fun t => (h t i j).continuousAt

lemma eq_of_hasMatDeriv_zero {X : ℝ → Matrix m l ℝ} (h : ∀ t, HasMatDeriv X 0 t) (s t : ℝ) :
    X s = X t := by
  ext i j
  have hd : ∀ u, HasDerivAt (fun r => X r i j) 0 u := fun u => by simpa using h u i j
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s t

lemma hasDerivAt_mulVec {W : ℝ → Matrix m l ℝ} {W' : Matrix m l ℝ} {t : ℝ} (h : HasMatDeriv W W' t)
    (x : l → ℝ) (i : m) : HasDerivAt (fun s => (W s *ᵥ x) i) ((W' *ᵥ x) i) t := by
  simp only [mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (h i j).mul_const (x j)

end Deriv

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- Global existence for linear matrix differential equations: for a continuous `A : ℝ → Matrix k k ℝ` and a
time `s` there is `X : ℝ → Matrix k k ℝ` with `X(s) = 1` and `X' = A X` on all of `ℝ`. Classical: linear
systems with continuous coefficients have solutions on the whole interval of continuity
(P. Hartman, Ordinary Differential Equations, Chapter IV, Theorem 1.1). -/
def LinearODEGlobal (k : Type*) [Fintype k] [DecidableEq k] : Prop :=
  ∀ A : ℝ → Matrix k k ℝ, Continuous A → ∀ s : ℝ,
    ∃ X : ℝ → Matrix k k ℝ, X s = 1 ∧ ∀ t, HasMatDeriv X (A t * X t) t

/-- Ostrowski's theorem on congruences (A. M. Ostrowski, Proc. Natl. Acad. Sci. USA 45, 1959; R. A. Horn and
C. R. Johnson, Matrix Analysis, 2nd ed., Theorem 4.5.9): if `B = W A Wᵀ` with symmetric `A` and all singular
values of `W` at least 1, then the eigenvalues in the same order satisfy `λᵢ(B) = θᵢ λᵢ(A)` with `θᵢ ≥ 1`. -/
def OstrowskiCongruence (k : Type*) [Fintype k] [DecidableEq k] : Prop :=
  ∀ (A B W : Matrix k k ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian), B = W * A * Wᵀ →
    (Wᵀ * W - 1).PosSemidef → ∀ i, ∃ θ : ℝ, 1 ≤ θ ∧ hB.eigenvalues i = θ * hA.eigenvalues i

/-- If `M' = A M + M Aᵀ` with continuous `A`, then `M(t) = W(t) M(s) W(t)ᵀ` with `W' = A W`, `W(s) = 1`. -/
theorem conj_repr (hlin : LinearODEGlobal k) {A M : ℝ → Matrix k k ℝ} (hA : Continuous A)
    (hM : ∀ t, HasMatDeriv M (A t * M t + M t * (A t)ᵀ) t) (s : ℝ) :
    ∃ W : ℝ → Matrix k k ℝ, W s = 1 ∧ (∀ t, HasMatDeriv W (A t * W t) t) ∧
      ∀ t, M t = W t * M s * (W t)ᵀ := by
  obtain ⟨W, hWs, hW⟩ := hlin A hA s
  obtain ⟨Z, hZs, hZ⟩ := hlin (fun t => -(A t)ᵀ) hA.matrix_transpose.neg s
  obtain ⟨V, hVs, hV⟩ : ∃ V : ℝ → Matrix k k ℝ, V s = 1 ∧ ∀ t, HasMatDeriv V (-(V t * A t)) t :=
    ⟨fun t => (Z t)ᵀ, by simp [hZs], fun t => (hZ t).transpose.congr_deriv (by
      simp [transpose_mul, transpose_neg])⟩
  have hVW : ∀ t, V t * W t = 1 := by
    intro t
    have hc := eq_of_hasMatDeriv_zero (X := fun t => V t * W t)
      (fun u => ((hV u).mul (hW u)).congr_deriv (by noncomm_ring)) t s
    simpa [hVs, hWs] using hc
  have hconst : ∀ t, V t * M t * (V t)ᵀ = M s := by
    intro t
    have hc := eq_of_hasMatDeriv_zero (X := fun t => V t * M t * (V t)ᵀ)
      (fun u => (((hV u).mul (hM u)).mul (hV u).transpose).congr_deriv (by
        rw [transpose_neg, transpose_mul]; noncomm_ring)) t s
    simpa [hVs] using hc
  refine ⟨W, hWs, hW, fun t => ?_⟩
  have hWV : W t * V t = 1 := mul_eq_one_comm.1 (hVW t)
  rw [← hconst t]
  calc M t = (W t * V t) * M t * (W t * V t)ᵀ := by rw [hWV]; simp
    _ = W t * (V t * M t * (V t)ᵀ) * (W t)ᵀ := by rw [transpose_mul]; noncomm_ring

/-- If `W' = A W` with positive semidefinite `A`, then `t ↦ |W(t) x|²` is monotone. -/
theorem norm_sq_mono {A W : ℝ → Matrix k k ℝ} (hW : ∀ t, HasMatDeriv W (A t * W t) t)
    (hA : ∀ t, (A t).PosSemidef) (x : k → ℝ) : Monotone fun t => (W t *ᵥ x) ⬝ᵥ (W t *ᵥ x) := by
  have hd : ∀ t, HasDerivAt (fun t => (W t *ᵥ x) ⬝ᵥ (W t *ᵥ x))
      (2 * ((W t *ᵥ x) ⬝ᵥ (A t *ᵥ (W t *ᵥ x)))) t := by
    intro t
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hasDerivAt_mulVec (hW t) x i).mul (hasDerivAt_mulVec (hW t) x i)
    convert h using 1
    · funext s; rfl
    · simp only [dotProduct, ← Matrix.mulVec_mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
  rw [(hd t).deriv]
  have := (posSemidef_iff_dotProduct_mulVec.1 (hA t)).2 (W t *ᵥ x)
  simp only [star_trivial] at this
  linarith

lemma Qm_isHermitian {T : Matrix n n ℝ} (hT : Tᵀ = T) (Φ : Matrix n k ℝ) : (Qm T Φ).IsHermitian := by
  show (Qm T Φ)ᴴ = Qm T Φ
  rw [conjTranspose_eq_transpose_of_trivial]; exact Qm_transpose hT Φ

/-- `Φ` solves the dynamics `Φ' = (1 - Φ Φᵀ) T Φ Q` on all of `ℝ`. -/
def IsFlow (T : Matrix n n ℝ) (Φ : ℝ → Matrix n k ℝ) : Prop := ∀ t, HasMatDeriv Φ (vf T (Φ t)) t

lemma continuous_Qm (T : Matrix n n ℝ) : Continuous fun Φ : Matrix n k ℝ => Qm T Φ :=
  (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

lemma continuous_Gm (T : Matrix n n ℝ) : Continuous fun Φ : Matrix n k ℝ => Gm T Φ := by
  unfold Gm Pm
  exact ((continuous_const.matrix_mul continuous_id).matrix_transpose.matrix_mul
    (continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_transpose))).matrix_mul
    (continuous_const.matrix_mul continuous_id)

lemma hasMatDeriv_Q {T : Matrix n n ℝ} (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ} (hΦ : IsFlow T Φ) (t : ℝ) :
    HasMatDeriv (fun s => Qm T (Φ s)) (Gm T (Φ t) * Qm T (Φ t) + Qm T (Φ t) * (Gm T (Φ t))ᵀ) t := by
  have h := ((hΦ t).transpose.mul (hasMatDeriv_const T t)).mul (hΦ t)
  refine h.congr_deriv ?_
  rw [Gm_transpose, Matrix.mul_zero, add_zero, qdot_eq hT, add_comm]

/-- The algebra of `(Φᵀ Φ)'`: `V(Φ)ᵀ Φ + Φᵀ V(Φ) = -(Q² E + E Q²)` with `E = Φᵀ Φ - 1`. -/
lemma stiefel_dot {T : Matrix n n ℝ} (hT : Tᵀ = T) (Φ : Matrix n k ℝ) :
    (vf T Φ)ᵀ * Φ + Φᵀ * vf T Φ =
      -(Qm T Φ * Qm T Φ) * (Φᵀ * Φ - 1) + (Φᵀ * Φ - 1) * (-(Qm T Φ * Qm T Φ))ᵀ := by
  have h1 : (vf T Φ)ᵀ = Qm T Φ * Φᵀ * T * Pm Φ := by
    simp only [vf, transpose_mul, Qm_transpose hT, Pm_transpose, hT, Matrix.mul_assoc]
  rw [h1, transpose_neg, transpose_mul, Qm_transpose hT]
  simp only [vf, Pm, Qm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  abel

/-- The constraint is kept: `Φ(t)ᵀ Φ(t) = 1` for all `t` if it holds at one time. -/
theorem stiefel (hlin : LinearODEGlobal k) {T : Matrix n n ℝ} (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ}
    (hΦ : IsFlow T Φ) {s : ℝ} (hs : (Φ s)ᵀ * Φ s = 1) (t : ℝ) : (Φ t)ᵀ * Φ t = 1 := by
  have hc : Continuous fun u => -(Qm T (Φ u) * Qm T (Φ u)) :=
    (((continuous_Qm T).comp (continuous_of_hasMatDeriv hΦ)).matrix_mul
      ((continuous_Qm T).comp (continuous_of_hasMatDeriv hΦ))).neg
  have hE : ∀ u, HasMatDeriv (fun r => (Φ r)ᵀ * Φ r - 1)
      (-(Qm T (Φ u) * Qm T (Φ u)) * ((Φ u)ᵀ * Φ u - 1) +
        ((Φ u)ᵀ * Φ u - 1) * (-(Qm T (Φ u) * Qm T (Φ u)))ᵀ) u := fun u =>
    (((hΦ u).transpose.mul (hΦ u)).sub_const 1).congr_deriv (stiefel_dot hT (Φ u))
  obtain ⟨W, -, -, hrep⟩ := conj_repr hlin hc hE s
  have := hrep t
  rw [hs, sub_self, Matrix.mul_zero, Matrix.zero_mul] at this
  exact sub_eq_zero.1 this

/-- The predictor moves by a congruence that does not shrink: `Q(t) = W Q(s) Wᵀ` with `Wᵀ W - 1` positive
semidefinite for `t ≥ s`. -/
theorem pred_conj (hlin : LinearODEGlobal k) {T : Matrix n n ℝ} (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ}
    (hΦ : IsFlow T Φ) {s : ℝ} (hs : (Φ s)ᵀ * Φ s = 1) {t : ℝ} (hst : s ≤ t) :
    ∃ W : Matrix k k ℝ, Qm T (Φ t) = W * Qm T (Φ s) * Wᵀ ∧ (Wᵀ * W - 1).PosSemidef := by
  have hc : Continuous fun u => Gm T (Φ u) := (continuous_Gm T).comp (continuous_of_hasMatDeriv hΦ)
  obtain ⟨W, hWs, hW, hrep⟩ := conj_repr hlin hc (hasMatDeriv_Q hT hΦ) s
  refine ⟨W t, hrep t, ?_⟩
  have hmono := norm_sq_mono hW (fun u => G_posSemidef T (stiefel hlin hT hΦ hs u))
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · show ((W t)ᵀ * W t - 1)ᴴ = (W t)ᵀ * W t - 1
    simp [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul]
  · have h := hmono x hst
    simp only [hWs, one_mulVec] at h
    simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec]
    rw [dotProduct_mulVec, vecMul_transpose]
    linarith

/-- **Theorem 1.** For `t ≥ s`, the ordered eigenvalues satisfy `λᵢ(Q(t)) = θᵢ λᵢ(Q(s))` with `θᵢ ≥ 1`. -/
theorem eig_scale (hlin : LinearODEGlobal k) (host : OstrowskiCongruence k) {T : Matrix n n ℝ}
    (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ} (hΦ : IsFlow T Φ) {s : ℝ} (hs : (Φ s)ᵀ * Φ s = 1) {t : ℝ}
    (hst : s ≤ t) (i : k) : ∃ θ : ℝ, 1 ≤ θ ∧
      (Qm_isHermitian hT (Φ t)).eigenvalues i = θ * (Qm_isHermitian hT (Φ s)).eigenvalues i := by
  obtain ⟨W, hrep, hW⟩ := pred_conj hlin hT hΦ hs hst
  exact host _ _ W _ _ hrep hW i

/-- The signs of the ordered eigenvalues are kept and their absolute values do not decrease. -/
theorem eig_abs_mono (hlin : LinearODEGlobal k) (host : OstrowskiCongruence k) {T : Matrix n n ℝ}
    (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ} (hΦ : IsFlow T Φ) {s : ℝ} (hs : (Φ s)ᵀ * Φ s = 1) {t : ℝ}
    (hst : s ≤ t) (i : k) :
    |(Qm_isHermitian hT (Φ s)).eigenvalues i| ≤ |(Qm_isHermitian hT (Φ t)).eigenvalues i| ∧
    (0 < (Qm_isHermitian hT (Φ s)).eigenvalues i ↔ 0 < (Qm_isHermitian hT (Φ t)).eigenvalues i) ∧
    ((Qm_isHermitian hT (Φ s)).eigenvalues i < 0 ↔ (Qm_isHermitian hT (Φ t)).eigenvalues i < 0) := by
  obtain ⟨θ, hθ, he⟩ := eig_scale hlin host hT hΦ hs hst i
  rw [he]
  have hθ0 : 0 < θ := by linarith
  refine ⟨?_, ⟨fun h => mul_pos hθ0 h, fun h => pos_of_mul_pos_right h hθ0.le⟩,
    ⟨fun h => mul_neg_of_pos_of_neg hθ0 h,
      fun h => lt_of_not_ge fun h' => absurd h (not_lt.2 (mul_nonneg hθ0.le h'))⟩⟩
  rw [abs_mul, abs_of_pos hθ0]
  exact le_mul_of_one_le_left (abs_nonneg _) hθ

/-- `|det Q(t)| ≥ |det Q(s)|` for `t ≥ s`. -/
theorem abs_det_mono (hlin : LinearODEGlobal k) (host : OstrowskiCongruence k) {T : Matrix n n ℝ}
    (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ} (hΦ : IsFlow T Φ) {s : ℝ} (hs : (Φ s)ᵀ * Φ s = 1) {t : ℝ}
    (hst : s ≤ t) : |(Qm T (Φ s)).det| ≤ |(Qm T (Φ t)).det| := by
  rw [(Qm_isHermitian hT (Φ s)).det_eq_prod_eigenvalues, (Qm_isHermitian hT (Φ t)).det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ =>
    (eig_abs_mono hlin host hT hΦ hs hst i).1

/-- **Theorem 2.** If the flow converges to a critical point `Φ∞` and `Q(s)` is nonsingular, then `Q∞` is
nonsingular and `T Φ∞ = Φ∞ Q∞`: the span of `Φ∞` is `T`-invariant. So no limit has a singular predictor or a
span that is not `T`-invariant. -/
theorem limit_invariant (hlin : LinearODEGlobal k) (host : OstrowskiCongruence k) {T : Matrix n n ℝ}
    (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ} (hΦ : IsFlow T Φ) {s : ℝ} (hs : (Φ s)ᵀ * Φ s = 1)
    (hdet : (Qm T (Φ s)).det ≠ 0) {Φinf : Matrix n k ℝ} (hlim : Tendsto Φ atTop (𝓝 Φinf))
    (hcrit : vf T Φinf = 0) : (Qm T Φinf).det ≠ 0 ∧ T * Φinf = Φinf * Qm T Φinf := by
  have hcont : Continuous fun Φ : Matrix n k ℝ => |(Qm T Φ).det| :=
    ((continuous_Qm T).matrix_det).abs
  have hge : |(Qm T (Φ s)).det| ≤ |(Qm T Φinf).det| :=
    ge_of_tendsto ((hcont.tendsto Φinf).comp hlim)
      (eventually_atTop.2 ⟨s, fun t ht => abs_det_mono hlin host hT hΦ hs ht⟩)
  have hne : (Qm T Φinf).det ≠ 0 := fun h => by
    rw [h, abs_zero] at hge; exact hdet (abs_nonpos_iff.1 hge)
  exact ⟨hne, crit_invariant ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)) hcrit⟩

end SelfPred
