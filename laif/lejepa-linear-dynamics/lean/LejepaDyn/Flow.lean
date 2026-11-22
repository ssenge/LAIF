import LejepaDyn.Features

/-!
# The gradient flow of linear LeJEPA and the feature equation

Linear encoder `W ∈ ℝ^{K×d}` (rows `k`), data covariance `Σ = Sᵀ S`, covariance `Δ` of the difference of two
views, direction law `ν` on the unit sphere of `ℝ^K`, slice function `h` with derivative `h'` on `[0, ∞)`:

  `L(W) = Σₖ Σₚ Σ_q W_{kp} Δ_{pq} W_{kq} + μ ∫ h(aᵀ W Σ Wᵀ a) dν(a)`.

* `hasDerivAt_loss`: for every direction `H`, `d/ds L(W + s H)` at `s = 0` equals `⟨∇L(W), H⟩` with
  `∇L(W) = 2 W Δ + 2 μ G W Σ`, `G = ∫ h'(aᵀ M a) a aᵀ dν` (written entrywise in `grad`).
* `feature_ode`: along a gradient flow, the learned variance `n = σ ‖W e‖²` of a common eigenvector `e`
  (`Σ e = σ e`, `Δ e = δ e`) satisfies `ṅ = -4 δ n - 4 μ σ² (W e)ᵀ G (W e)`.
* `never_learned_flow`, `early_phase_flow` and their versions for the SIGReg slice function `D`.
-/

open MeasureTheory Finset Set Real Filter Topology

namespace LejepaDyn

variable {K d : ℕ}

/-- `Wᵀ a`. -/
noncomputable def wa (W : Fin K → Fin d → ℝ) (a : Fin K → ℝ) : Fin d → ℝ := fun p => ∑ k, a k * W k p

/-- `(S Wᵀ a)ᵣ`. -/
noncomputable def sl (S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) (a : Fin K → ℝ) (r : Fin d) : ℝ :=
  ∑ p, S r p * wa W a p

/-- `W e`. -/
noncomputable def col (W : Fin K → Fin d → ℝ) (e : Fin d → ℝ) : Fin K → ℝ := fun k => ∑ p, W k p * e p

/-- The vectors `bᵣ = W sᵣ` for the rows `sᵣ` of `S`, so that `W Sᵀ S Wᵀ = Σᵣ bᵣ bᵣᵀ`. -/
noncomputable def bW (S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) : Fin d → Fin K → ℝ :=
  fun r => col W (S r)

/-- The invariance term `tr(W Δ Wᵀ)`. -/
noncomputable def invc (Δ : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) : ℝ :=
  ∑ k, ∑ p, ∑ q, W k p * Δ p q * W k q

/-- The loss of linear LeJEPA. -/
noncomputable def loss (ν : Measure (Fin K → ℝ)) (h : ℝ → ℝ) (μ : ℝ) (Δ S : Fin d → Fin d → ℝ)
    (W : Fin K → Fin d → ℝ) : ℝ :=
  invc Δ W + μ * ∫ a, h (qf (bW S W) a) ∂ν

/-- The gradient `2 W Δ + 2 μ G W Σ`, entrywise. -/
noncomputable def grad (ν : Measure (Fin K → ℝ)) (hp : ℝ → ℝ) (μ : ℝ) (Δ S : Fin d → Fin d → ℝ)
    (W : Fin K → Fin d → ℝ) : Fin K → Fin d → ℝ := fun k p =>
  2 * ∑ q, W k q * Δ q p + 2 * μ * ∫ a, hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p) ∂ν

/-- The trace inner product `⟨A, B⟩ = tr(Aᵀ B)`. -/
noncomputable def frob (X Y : Fin K → Fin d → ℝ) : ℝ := ∑ k, ∑ p, X k p * Y k p

/-! ## Algebra -/

lemma dot_bW (S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) (a : Fin K → ℝ) (r : Fin d) :
    dot (bW S W r) a = sl S W a r := by
  simp only [dot, bW, col, sl, wa, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

lemma qf_bW (S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) (a : Fin K → ℝ) :
    qf (bW S W) a = ∑ r, sl S W a r ^ 2 := by
  simp only [qf, dot_bW]

lemma sl_add_smul (S : Fin d → Fin d → ℝ) (W H : Fin K → Fin d → ℝ) (a : Fin K → ℝ) (r : Fin d) (s : ℝ) :
    sl S (W + s • H) a r = sl S W a r + s * sl S H a r := by
  simp only [sl, wa, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma sum_sl_mul (S : Fin d → Fin d → ℝ) (α : Fin d → ℝ) (H : Fin K → Fin d → ℝ) (a : Fin K → ℝ) :
    ∑ r, α r * sl S H a r = ∑ k, ∑ p, (a k * ∑ r, α r * S r p) * H k p := by
  simp only [sl, wa, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- With `y = S e` and `Sᵀ y = σ e`: `Σᵣ (S Wᵀ a)ᵣ yᵣ = σ (W e)ᵀ a`. -/
lemma sum_sl_eig (S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) (a : Fin K → ℝ) {e y : Fin d → ℝ}
    {σ : ℝ} (hy : ∀ q, ∑ r, S r q * y r = σ * e q) :
    ∑ r, sl S W a r * y r = σ * dot (col W e) a := by
  calc ∑ r, sl S W a r * y r = ∑ q, wa W a q * ∑ r, S r q * y r := by
        simp only [sl, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    _ = ∑ q, wa W a q * (σ * e q) := by simp only [hy]
    _ = σ * dot (col W e) a := by
        simp only [wa, dot, col, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-! ## Integrability on the sphere -/

lemma isCompact_unitSphere : IsCompact {a : Fin K → ℝ | nsq a = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by unfold nsq; fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin K → ℝ)) (r := 1)).subset fun a ha => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    have h1 : a j ^ 2 ≤ nsq a :=
      Finset.single_le_sum (f := fun j => a j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    simp only [Set.mem_ofPred_eq] at ha
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

lemma integrable_cont {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1)
    {g : (Fin K → ℝ) → ℝ} (hg : Continuous g) : Integrable g ν := by
  obtain ⟨C, hC⟩ := isCompact_unitSphere.exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C (hs.mono fun a ha => hC a ha)

lemma integrable_hp_mul {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1)
    {hp : ℝ → ℝ} (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (B : Fin d → Fin K → ℝ)
    {g : (Fin K → ℝ) → ℝ} (hg : Continuous g) : Integrable (fun a => hp (qf B a) * g a) ν :=
  (integrable_cont hs hg).bdd_mul (hm.comp_aemeasurable (continuous_qf B).aemeasurable).aestronglyMeasurable
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hC _ (qf_nonneg B a))

lemma continuous_sl (S : Fin d → Fin d → ℝ) (W : Fin K → Fin d → ℝ) (r : Fin d) :
    Continuous fun a => sl S W a r := by
  unfold sl wa; fun_prop

/-! ## The gradient -/

/-- Differentiation of the regularizer under the integral. -/
theorem hasDerivAt_reg {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1)
    {h hp : ℝ → ℝ} (hd : ∀ x, 0 ≤ x → HasDerivAt h (hp x) x) (hm : Measurable hp) {C C0 : ℝ}
    (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (hC0 : ∀ x, 0 ≤ x → |h x| ≤ C0) (S : Fin d → Fin d → ℝ)
    (W H : Fin K → Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => ∫ a, h (qf (bW S (W + s • H)) a) ∂ν)
      (∫ a, hp (qf (bW S W) a) * ∑ r, 2 * sl S W a r * sl S H a r ∂ν) 0 := by
  have key : ∀ s a, qf (bW S (W + s • H)) a = ∑ r, (sl S W a r + s * sl S H a r) ^ 2 := by
    intro s a; rw [qf_bW]; simp only [sl_add_smul]
  simp_rw [key]
  have hcont : ∀ s : ℝ, Continuous fun a => ∑ r, (sl S W a r + s * sl S H a r) ^ 2 := by
    intro s; unfold sl wa; fun_prop
  have hnn : ∀ (s : ℝ) a, 0 ≤ ∑ r, (sl S W a r + s * sl S H a r) ^ 2 :=
    fun s a => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hCnn : 0 ≤ C := (abs_nonneg _).trans (hC 0 le_rfl)
  have hFc : ∀ s : ℝ, Continuous fun a => h (∑ r, (sl S W a r + s * sl S H a r) ^ 2) := fun s =>
    continuous_iff_continuousAt.2 fun a => (hd _ (hnn s a)).continuousAt.comp
      (f := fun a => ∑ r, (sl S W a r + s * sl S H a r) ^ 2) (hcont s).continuousAt
  have hg : ∀ s : ℝ, Continuous fun a => ∑ r, 2 * (sl S W a r + s * sl S H a r) * sl S H a r := by
    intro s; unfold sl wa; fun_prop
  have hbd : ∀ a, ∀ s ∈ Icc (-1 : ℝ) 1,
      ‖hp (∑ r, (sl S W a r + s * sl S H a r) ^ 2) * ∑ r, 2 * (sl S W a r + s * sl S H a r) * sl S H a r‖ ≤
        C * ∑ r, (2 * sl S W a r ^ 2 + 3 * sl S H a r ^ 2) := by
    intro a s hs1
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul (hC _ (hnn s a)) ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun r _ => ?_)) (abs_nonneg _) hCnn
    obtain ⟨h1, h2⟩ := hs1
    set x := sl S W a r; set y := sl S H a r
    have hy2 := sq_nonneg y
    exact abs_le.2 ⟨by nlinarith [sq_nonneg (x + y), mul_nonneg (by linarith : (0:ℝ) ≤ 1 + s) hy2],
      by nlinarith [sq_nonneg (x - y), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) hy2]⟩
  have hbi : Integrable (fun a => C * ∑ r, (2 * sl S W a r ^ 2 + 3 * sl S H a r ^ 2)) ν :=
    integrable_cont hs (by unfold sl wa; fun_prop)
  have hdiff : ∀ a, ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun s => h (∑ r, (sl S W a r + s * sl S H a r) ^ 2))
      (hp (∑ r, (sl S W a r + s * sl S H a r) ^ 2) *
        ∑ r, 2 * (sl S W a r + s * sl S H a r) * sl S H a r) s := by
    intro a s _
    have hin : HasDerivAt (fun s => ∑ r, (sl S W a r + s * sl S H a r) ^ 2)
        (∑ r, 2 * (sl S W a r + s * sl S H a r) * sl S H a r) s := by
      refine HasDerivAt.fun_sum fun r _ => ?_
      have := (((hasDerivAt_id s).mul_const (sl S H a r)).const_add (sl S W a r)).pow 2
      convert this using 1
      · funext x; simp
      · simp
    exact (hd _ (hnn s a)).comp s hin
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ)) (s := Icc (-1) 1)
    (Icc_mem_nhds (by norm_num) (by norm_num)) (Eventually.of_forall fun s => (hFc s).aestronglyMeasurable)
    (Integrable.of_bound (hFc 0).aestronglyMeasurable C0
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hC0 _ (hnn 0 a)))
    ((hm.comp_aemeasurable (hcont 0).aemeasurable).aestronglyMeasurable.mul (hg 0).aestronglyMeasurable)
    (Eventually.of_forall hbd) hbi (Eventually.of_forall hdiff)
  refine this.2.congr_deriv ?_
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp [qf_bW]

theorem hasDerivAt_invc {Δ : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) (W H : Fin K → Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => invc Δ (W + s • H)) (∑ k, ∑ p, (2 * ∑ q, W k q * Δ q p) * H k p) 0 := by
  have h1 : ∀ k p, HasDerivAt (fun s : ℝ => (W + s • H) k p) (H k p) 0 := by
    intro k p
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (H k p)).const_add (W k p)
    convert this using 1
    · funext s; simp [mul_comm]
    · simp
  have h3 : HasDerivAt (fun s : ℝ => invc Δ (W + s • H))
      (∑ k, ∑ p, ∑ q, (H k p * Δ p q * (W + (0 : ℝ) • H) k q + (W + (0 : ℝ) • H) k p * Δ p q * H k q)) 0 := by
    unfold invc
    exact HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ =>
      ((h1 k p).mul_const (Δ p q)).mul (h1 k q)
  refine h3.congr_deriv ?_
  simp only [zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ p, ∑ q, (H k p * Δ p q * W k q + W k p * Δ p q * H k q)
      = ∑ p, ∑ q, H k p * Δ p q * W k q + ∑ p, ∑ q, W k p * Δ p q * H k q := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ p, ∑ q, H k p * Δ p q * W k q + ∑ q, ∑ p, W k p * Δ p q * H k q := by
        rw [Finset.sum_comm (f := fun p q => W k p * Δ p q * H k q)]
    _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hΔ p q]; ring

lemma mul_two_frob (c : ℝ) (g H : Fin K → Fin d → ℝ) :
    c * (2 * ∑ k, ∑ p, g k p * H k p) = ∑ k, ∑ p, 2 * (c * g k p) * H k p := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The gradient of the loss.** For every direction `H`, `d/ds L(W + s H) = ⟨grad W, H⟩` at `s = 0`. -/
theorem hasDerivAt_loss {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1)
    {h hp : ℝ → ℝ} (hd : ∀ x, 0 ≤ x → HasDerivAt h (hp x) x) (hm : Measurable hp) {C C0 : ℝ}
    (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (hC0 : ∀ x, 0 ≤ x → |h x| ≤ C0) {Δ S : Fin d → Fin d → ℝ}
    (hΔ : ∀ p q, Δ p q = Δ q p) (μ : ℝ) (W H : Fin K → Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => loss ν h μ Δ S (W + s • H)) (frob (grad ν hp μ Δ S W) H) 0 := by
  have := (hasDerivAt_invc hΔ W H).add ((hasDerivAt_reg hs hd hm hC hC0 S W H).const_mul μ)
  refine this.congr_deriv ?_
  have hint : ∀ k p, Integrable (fun a => hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p)) ν :=
    fun k p => integrable_hp_mul hs hm hC _ (by unfold sl wa; fun_prop)
  have pw : ∀ a, hp (qf (bW S W) a) * ∑ r, 2 * sl S W a r * sl S H a r =
      ∑ k, ∑ p, 2 * (hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p)) * H k p := by
    intro a
    rw [show ∑ r, 2 * sl S W a r * sl S H a r = 2 * ∑ r, sl S W a r * sl S H a r by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, sum_sl_mul]
    exact mul_two_frob _ (fun k p => a k * ∑ r, sl S W a r * S r p) H
  have e : ∫ a, hp (qf (bW S W) a) * ∑ r, 2 * sl S W a r * sl S H a r ∂ν =
      ∑ k, ∑ p, 2 * (∫ a, hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p) ∂ν) * H k p := by
    rw [integral_congr_ae (Eventually.of_forall pw), integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun p _ => ((hint k p).const_mul 2).mul_const (H k p)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun p _ => ((hint k p).const_mul 2).mul_const (H k p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_mul_const, integral_const_mul]
  rw [e]
  simp only [frob, grad, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma frob_single (X : Fin K → Fin d → ℝ) (k : Fin K) (p : Fin d) :
    frob X (fun k' p' => if k' = k ∧ p' = p then 1 else 0) = X k p := by
  simp [frob, ite_and]

/-! ## The feature equation -/

lemma sum_swap_aux (c : ℝ) (α : Fin d → ℝ) (S : Fin d → Fin d → ℝ) (e : Fin d → ℝ) :
    ∑ p, c * (∑ r, α r * S r p) * e p = c * ∑ r, α r * ∑ p, S r p * e p := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- `(grad W) e = 2 δ W e + 2 μ σ G W e` for a common eigenvector `e`. -/
lemma grad_col {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {μ σ δ : ℝ} {Δ S : Fin d → Fin d → ℝ}
    {e : Fin d → ℝ} (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q)
    (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q) (W : Fin K → Fin d → ℝ) (k : Fin K) :
    ∑ p, grad ν hp μ Δ S W k p * e p =
      2 * δ * col W e k + 2 * μ * σ * ∫ a, hp (qf (bW S W) a) * (a k * dot (col W e) a) ∂ν := by
  have hint : ∀ p, Integrable (fun a => hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p)) ν :=
    fun p => integrable_hp_mul hs hm hC _ (by unfold sl wa; fun_prop)
  have h1 : ∑ p, (∑ q, W k q * Δ q p) * e p = δ * col W e k := by
    calc ∑ p, (∑ q, W k q * Δ q p) * e p = ∑ q, W k q * ∑ p, Δ q p * e p := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      _ = δ * col W e k := by
          simp only [hΔe, col, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ p, (∫ a, hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p) ∂ν) * e p =
      σ * ∫ a, hp (qf (bW S W) a) * (a k * dot (col W e) a) ∂ν := by
    rw [← integral_const_mul]
    simp only [← integral_mul_const]
    rw [← integral_finsetSum _ fun p _ => (hint p).mul_const _]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    have := sum_swap_aux (hp (qf (bW S W) a) * a k) (sl S W a) S e
    rw [sum_sl_eig S W a hSe] at this
    calc _ = ∑ p, hp (qf (bW S W) a) * a k * (∑ r, sl S W a r * S r p) * e p :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [this]; ring
  have h0 : ∑ p, grad ν hp μ Δ S W k p * e p = 2 * ∑ p, (∑ q, W k q * Δ q p) * e p +
      2 * μ * ∑ p, (∫ a, hp (qf (bW S W) a) * (a k * ∑ r, sl S W a r * S r p) ∂ν) * e p := by
    simp only [grad]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h0, h1, h2]; ring

lemma sum_mul_gq {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (B : Fin d → Fin K → ℝ) (v : Fin K → ℝ) :
    ∑ k, v k * ∫ a, hp (qf B a) * (a k * dot v a) ∂ν = gq ν hp B v := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun k _ => (integrable_hp_mul hs hm hC B
    (by unfold dot; fun_prop : Continuous fun a : Fin K → ℝ => a k * dot v a)).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  have : ∑ k, v k * (hp (qf B a) * (a k * dot v a)) = hp (qf B a) * dot v a * ∑ k, v k * a k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  dsimp only
  rw [this, show ∑ k, v k * a k = dot v a from rfl]; ring

/-- **Feature equation.** Along `Ẇ = -grad W`, the learned variance `n = σ ‖W e‖²` of a common eigenvector `e`
satisfies `ṅ = -4 δ n - 4 μ σ² (W e)ᵀ G (W e)`. -/
theorem feature_ode {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {μ σ δ : ℝ} {Δ S : Fin d → Fin d → ℝ}
    {e : Fin d → ℝ} (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q)
    (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q) {W : ℝ → Fin K → Fin d → ℝ}
    (hW : ∀ t, HasDerivAt W (-grad ν hp μ Δ S (W t)) t) (t : ℝ) :
    HasDerivAt (fun t => σ * nsq (col (W t) e))
      (-4 * δ * (σ * nsq (col (W t) e)) - 4 * μ * σ ^ 2 * gq ν hp (bW S (W t)) (col (W t) e)) t := by
  have hv : ∀ k, HasDerivAt (fun t => col (W t) e k) (-(2 * δ * col (W t) e k + 2 * μ * σ *
      ∫ a, hp (qf (bW S (W t)) a) * (a k * dot (col (W t) e) a) ∂ν)) t := by
    intro k
    rw [← grad_col hs hm hC hΔe hSe (W t) k, ← Finset.sum_neg_distrib]
    unfold col
    refine HasDerivAt.fun_sum fun p _ => ?_
    have := (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hW t) k) p).mul_const (e p)
    convert this using 1; simp [neg_mul]
  have hn := (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hv k).fun_pow 2).const_mul σ
  refine hn.congr_deriv ?_
  rw [← sum_mul_gq hs hm hC (bW S (W t)) (col (W t) e)]
  unfold nsq
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by norm_num; ring

/-! ## Theorems 1 and 2 for the gradient flow of the loss -/

/-- A gradient flow of the loss (in the trace inner product) follows `Ẇ = -grad W`. -/
lemma flow_eq {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1)
    {h hp : ℝ → ℝ} (hd : ∀ x, 0 ≤ x → HasDerivAt h (hp x) x) (hm : Measurable hp) {C C0 : ℝ}
    (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (hC0 : ∀ x, 0 ≤ x → |h x| ≤ C0) {Δ S : Fin d → Fin d → ℝ}
    (hΔ : ∀ p q, Δ p q = Δ q p) {μ : ℝ} {W W' : ℝ → Fin K → Fin d → ℝ}
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν h μ Δ S (W t + s • H)) (-frob (W' t) H) 0) (t : ℝ) :
    W' t = -grad ν hp μ Δ S (W t) := by
  funext k p
  have h1 := (hflow t (fun k' p' => if k' = k ∧ p' = p then 1 else 0)).unique
    (hasDerivAt_loss hs hd hm hC hC0 hΔ μ (W t) _)
  rw [frob_single, frob_single] at h1
  simp only [Pi.neg_apply]; linarith

/-- **Theorem 1 for the gradient flow.** If `W` is a gradient flow of the loss, every common eigenvector `e`
of `Σ = Sᵀ S` and `Δ` satisfies `n(t) ≤ n(0) e^{4 (σ κ - δ) t}`, with `n = σ ‖W e‖²` and `κ = -μ h'(0) / K`. -/
theorem never_learned_flow {ν : Measure (Fin K → ℝ)} (hiso : Iso4 K ν) (hK : 0 < K) {h hp : ℝ → ℝ}
    (hd : ∀ x, 0 ≤ x → HasDerivAt h (hp x) x) (hm : Measurable hp) {C C0 : ℝ}
    (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (hC0 : ∀ x, 0 ≤ x → |h x| ≤ C0) (hlow : ∀ x, 0 ≤ x → hp 0 ≤ hp x)
    {μ σ δ T : ℝ} (hμ : 0 ≤ μ) {Δ S : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) {e : Fin d → ℝ}
    (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q) (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q)
    {W W' : ℝ → Fin K → Fin d → ℝ} (hW : ∀ t, HasDerivAt W (W' t) t)
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν h μ Δ S (W t + s • H)) (-frob (W' t) H) 0) :
    ∀ t ∈ Icc 0 T, σ * nsq (col (W t) e) ≤
      σ * nsq (col (W 0) e) * exp (4 * (σ * (-(μ * hp 0) / K) - δ) * t) := by
  have := hiso.prob
  have hW2 : ∀ t, HasDerivAt W (-grad ν hp μ Δ S (W t)) t := fun t => by
    rw [← flow_eq hiso.sphere hd hm hC hC0 hΔ hflow t]; exact hW t
  exact never_learned hiso hK hm hC hlow hμ (n := fun t => σ * nsq (col (W t) e)) (v := fun t => col (W t) e)
    (B := fun t => bW S (W t)) (fun t => rfl) (feature_ode hiso.sphere hm hC hΔe hSe hW2)

/-- **Theorem 2 for the gradient flow.** While `tr M ≤ ε`, `n(t) ≥ n(0) e^{4 (σ κ - δ - 3 μ σ L₂ ε / (K (K + 2))) t}`. -/
theorem early_phase_flow {ν : Measure (Fin K → ℝ)} (hiso : Iso4 K ν) (hK : 0 < K) {h hp : ℝ → ℝ}
    (hd : ∀ x, 0 ≤ x → HasDerivAt h (hp x) x) (hm : Measurable hp) {C C0 : ℝ}
    (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (hC0 : ∀ x, 0 ≤ x → |h x| ≤ C0) {L₂ : ℝ} (hL : 0 ≤ L₂)
    (hup : ∀ x, 0 ≤ x → hp x ≤ hp 0 + L₂ * x)
    {μ σ δ ε T : ℝ} (hμ : 0 ≤ μ) {Δ S : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) {e : Fin d → ℝ}
    (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q) (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q)
    {W W' : ℝ → Fin K → Fin d → ℝ} (hW : ∀ t, HasDerivAt W (W' t) t)
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν h μ Δ S (W t + s • H)) (-frob (W' t) H) 0)
    (hsmall : ∀ t ∈ Icc 0 T, trM (bW S (W t)) ≤ ε) :
    ∀ t ∈ Icc 0 T, σ * nsq (col (W 0) e) * exp (4 * (σ * (-(μ * hp 0) / K) - δ -
      3 * μ * σ * L₂ * ε / (K * (K + 2))) * t) ≤ σ * nsq (col (W t) e) := by
  have := hiso.prob
  have hW2 : ∀ t, HasDerivAt W (-grad ν hp μ Δ S (W t)) t := fun t => by
    rw [← flow_eq hiso.sphere hd hm hC hC0 hΔ hflow t]; exact hW t
  exact early_phase hiso hK hm hC hL hup hμ (n := fun t => σ * nsq (col (W t) e)) (v := fun t => col (W t) e)
    (B := fun t => bW S (W t)) (fun t => rfl) (feature_ode hiso.sphere hm hC hΔe hSe hW2) hsmall

open SigregDim in
/-- `never_learned_flow` for the SIGReg slice function `D`. -/
theorem never_learned_flow_D {ν : Measure (Fin K → ℝ)} (hiso : Iso4 K ν) (hK : 0 < K) {μ σ δ T : ℝ}
    (hμ : 0 ≤ μ) {Δ S : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) {e : Fin d → ℝ}
    (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q) (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q)
    {W W' : ℝ → Fin K → Fin d → ℝ} (hW : ∀ t, HasDerivAt W (W' t) t)
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν epD μ Δ S (W t + s • H)) (-frob (W' t) H) 0) :
    ∀ t ∈ Icc 0 T, σ * nsq (col (W t) e) ≤
      σ * nsq (col (W 0) e) * exp (4 * (σ * (-(μ * epD' 0) / K) - δ) * t) :=
  never_learned_flow hiso hK (fun _ hx => hasDerivAt_epD hx) measurable_epD' (fun _ hx => abs_epD'_le hx)
    (fun _ hx => abs_epD_le hx) (fun _ hx => epD'_ge hx) hμ hΔ hΔe hSe hW hflow

open SigregDim in
/-- `early_phase_flow` for the SIGReg slice function `D`, with `L₂ = 8`. -/
theorem early_phase_flow_D {ν : Measure (Fin K → ℝ)} (hiso : Iso4 K ν) (hK : 0 < K) {μ σ δ ε T : ℝ}
    (hμ : 0 ≤ μ) {Δ S : Fin d → Fin d → ℝ} (hΔ : ∀ p q, Δ p q = Δ q p) {e : Fin d → ℝ}
    (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q) (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q)
    {W W' : ℝ → Fin K → Fin d → ℝ} (hW : ∀ t, HasDerivAt W (W' t) t)
    (hflow : ∀ t H, HasDerivAt (fun s : ℝ => loss ν epD μ Δ S (W t + s • H)) (-frob (W' t) H) 0)
    (hsmall : ∀ t ∈ Icc 0 T, trM (bW S (W t)) ≤ ε) :
    ∀ t ∈ Icc 0 T, σ * nsq (col (W 0) e) * exp (4 * (σ * (-(μ * epD' 0) / K) - δ -
      3 * μ * σ * 8 * ε / (K * (K + 2))) * t) ≤ σ * nsq (col (W t) e) :=
  early_phase_flow hiso hK (fun _ hx => hasDerivAt_epD hx) measurable_epD' (fun _ hx => abs_epD'_le hx)
    (fun _ hx => abs_epD_le hx) (by norm_num) (fun _ hx => epD'_le_lin hx) hμ hΔ hΔe hSe hW hflow hsmall

end LejepaDyn
