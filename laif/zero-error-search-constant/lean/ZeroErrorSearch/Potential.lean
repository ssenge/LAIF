import ZeroErrorSearch.Basic

/-!
# Zero-error search: the potential argument

State after a random relabelling: survival probability `a` and the common off-diagonal Gram entry `b`, with
`b ≤ a` and `0 ≤ a + (N-1) b`. The angle is `ω = arccos √((a + (N-1) b)/(N a))`, the potential `Φ = a h(ω)` with
`h ω = c - ω` for `ω ≤ ω*` and `c - 2 ω* + ω` beyond, `c = π/4 + 1/2 - θ`, `ω* = π/2 - θ/2`.

* `hfun_lip`: `h` is 1-Lipschitz, so a round that moves `ω` by at most `δ` lowers `Φ` by at most `δ a`.
* `halting_mono`: halting (lowering `a` at fixed `b`, staying feasible) never lowers `Φ`.
* `lower_bound`: every trajectory obeying these two step rules, from `a = b = 1` to `a = 0`, has
  `π/4 + 1/2 - θ ≤ δ ∑ a_t`.
-/

open Real Set

namespace ZeroErrorSearch

variable (N : ℕ)

noncomputable def wstar : ℝ := π / 2 - theta N / 2
noncomputable def cc : ℝ := π / 4 + 1 / 2 - theta N
noncomputable def hfun (ω : ℝ) : ℝ := if ω ≤ wstar N then cc N - ω else cc N - 2 * wstar N + ω
noncomputable def omegaOf (a b : ℝ) : ℝ := arccos √((a + (N - 1) * b) / (N * a))
noncomputable def Phi (a b : ℝ) : ℝ := a * hfun N (omegaOf N a b)

lemma hfun_lip (x y : ℝ) : |hfun N x - hfun N y| ≤ |x - y| := by
  have h1 := le_abs_self (x - y); have h2 := neg_abs_le (x - y)
  unfold hfun; rw [abs_le]
  split_ifs with hx hy hy <;> constructor <;> linarith

lemma cc_pos (hN : 2 ≤ N) : 0 < cc N := by
  obtain ⟨hθ0, hθ4, -⟩ := theta_facts N hN
  unfold cc; linarith [pi_pos]

/-- Derivative of `(p + q x)/(r + s cos² x)`. -/
lemma quot_hasDeriv (p q r s x : ℝ) (hv : r + s * cos x ^ 2 ≠ 0) :
    HasDerivAt (fun x => (p + q * x) / (r + s * cos x ^ 2))
      ((q * (r + s * cos x ^ 2) + s * (p + q * x) * sin (2 * x)) / (r + s * cos x ^ 2) ^ 2) x := by
  have hu : HasDerivAt (fun x => p + q * x) q x := by
    simpa using ((hasDerivAt_id x).const_mul q).const_add p
  have hv' : HasDerivAt (fun x => r + s * cos x ^ 2) (s * (↑2 * cos x ^ (2 - 1) * (-sin x))) x :=
    (((hasDerivAt_cos x).pow 2).const_mul s).const_add r
  convert hu.div hv' hv using 1
  rw [sin_two_mul]; ring

lemma quot_monotoneOn (p q r s l u : ℝ) (hv : ∀ x ∈ Icc l u, r + s * cos x ^ 2 ≠ 0)
    (hnum : ∀ x ∈ Ioo l u, 0 ≤ q * (r + s * cos x ^ 2) + s * (p + q * x) * sin (2 * x)) :
    MonotoneOn (fun x => (p + q * x) / (r + s * cos x ^ 2)) (Icc l u) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc l u)
  · intro x hx; exact (quot_hasDeriv p q r s x (hv x hx)).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (quot_hasDeriv p q r s x (hv x (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    rw [(quot_hasDeriv p q r s x (hv x (Ioo_subset_Icc_self hx))).deriv]
    exact div_nonneg (hnum x hx) (sq_nonneg _)

lemma quot_antitoneOn (p q r s l u : ℝ) (hv : ∀ x ∈ Icc l u, r + s * cos x ^ 2 ≠ 0)
    (hnum : ∀ x ∈ Ioo l u, q * (r + s * cos x ^ 2) + s * (p + q * x) * sin (2 * x) ≤ 0) :
    AntitoneOn (fun x => (p + q * x) / (r + s * cos x ^ 2)) (Icc l u) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc l u)
  · intro x hx; exact (quot_hasDeriv p q r s x (hv x hx)).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (quot_hasDeriv p q r s x (hv x (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    rw [(quot_hasDeriv p q r s x (hv x (Ioo_subset_Icc_self hx))).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (hnum x hx) (sq_nonneg _)

/-- Angle of a feasible state: `cos² ω = (a + (N-1) b)/(N a)`, `ω ∈ [0, π/2]`, and `a (cos² ω - 1/N) = (1 - 1/N) b`. -/
lemma omegaOf_facts (hN : 2 ≤ N) {a b : ℝ} (ha : 0 < a) (hb1 : b ≤ a) (hb2 : 0 ≤ a + (N - 1) * b) :
    0 ≤ omegaOf N a b ∧ omegaOf N a b ≤ π / 2 ∧
      a * (cos (omegaOf N a b) ^ 2 - 1 / N) = (1 - 1 / N) * b := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hC0 : 0 ≤ (a + (N - 1) * b) / (N * a) := div_nonneg hb2 (by positivity)
  have hC1 : (a + (N - 1) * b) / (N * a) ≤ 1 := by rw [div_le_one₀ (by positivity)]; nlinarith
  refine ⟨arccos_nonneg _, arccos_le_pi_div_two.mpr (sqrt_nonneg _), ?_⟩
  unfold omegaOf
  rw [cos_arccos (by linarith [sqrt_nonneg ((a + (N - 1) * b) / (N * a))]) (sqrt_le_one.mpr hC1), sq_sqrt hC0]
  field_simp; ring

lemma omegaOf_one (hN : 2 ≤ N) : omegaOf N 1 1 = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
                               exact this.ne'
  unfold omegaOf
  rw [show ((1 : ℝ) + (N - 1) * 1) / (N * 1) = 1 by field_simp; ring, sqrt_one, arccos_one]

lemma omegaOf_zero (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) : omegaOf N a 0 = π / 2 - theta N := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  unfold omegaOf
  rw [show (a + (N - 1) * 0) / (N * a) = 1 / (N : ℝ) by rw [mul_zero, add_zero]; field_simp, arccos_eq_pi_div_two_sub_arcsin,
    sqrt_div' 1 hN'.le, sqrt_one]; rfl

lemma hfun_omega0 (hN : 2 ≤ N) : hfun N (π / 2 - theta N) < 0 := by
  obtain ⟨hθ0, hθ4, -⟩ := theta_facts N hN
  unfold hfun wstar cc; rw [if_pos (by linarith)]; linarith [pi_gt_three]

/-- `cos² ω > 1/N` forces `ω < π/2 - θ`, and `cos² ω < 1/N` forces `ω > π/2 - θ`. -/
lemma lt_omega0 (hN : 2 ≤ N) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ π / 2) (h : 1 / N < cos ω ^ 2) :
    ω < π / 2 - theta N := by
  obtain ⟨hθ0, hθ4, hsθ, hsq, -⟩ := theta_facts N hN
  by_contra hc; push_neg at hc
  have h2 : cos ω ≤ cos (π / 2 - theta N) := cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) hc
  rw [cos_pi_div_two_sub, hsθ] at h2
  have h3 : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩
  nlinarith

lemma omega0_lt (hN : 2 ≤ N) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ π / 2) (h : cos ω ^ 2 < 1 / N) :
    π / 2 - theta N < ω := by
  obtain ⟨hθ0, hθ4, hsθ, hsq, -⟩ := theta_facts N hN
  by_contra hc; push_neg at hc
  have h2 : cos (π / 2 - theta N) ≤ cos ω := cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [pi_pos]) hc
  rw [cos_pi_div_two_sub, hsθ] at h2
  have h3 : 0 ≤ 1 / √(N : ℝ) := by positivity
  nlinarith

lemma cos_sq_anti {x y : ℝ} (h0 : 0 ≤ x) (hxy : x ≤ y) (h1 : y ≤ π / 2) : cos y ^ 2 ≤ cos x ^ 2 := by
  have h2 : cos y ≤ cos x := cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [pi_pos]) hxy
  have h3 : 0 ≤ cos y := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩
  nlinarith

/-- **Lemma 4**: halting never lowers the potential. -/
theorem halting_mono (hN : 2 ≤ N) {a a' b : ℝ} (ha' : 0 < a') (haa : a' ≤ a) (hb1 : b ≤ a')
    (hb2 : 0 ≤ a' + (N - 1) * b) : Phi N a b ≤ Phi N a' b := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hθ0, hθ4, -⟩ := theta_facts N hN
  have ha : 0 < a := lt_of_lt_of_le ha' haa
  have hb2a : 0 ≤ a + (N - 1) * b := by nlinarith
  obtain ⟨hw0, hw1, hid⟩ := omegaOf_facts N hN ha (hb1.trans haa) hb2a
  obtain ⟨hw0', hw1', hid'⟩ := omegaOf_facts N hN ha' hb1 hb2
  have hk : 0 < 1 - 1 / (N : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hws : π / 2 - theta N ≤ wstar N := by unfold wstar; linarith
  have hws2 : wstar N ≤ π / 2 := by unfold wstar; linarith
  set ω := omegaOf N a b; set ω' := omegaOf N a' b
  unfold Phi
  rcases lt_trichotomy b 0 with hbn | hbz | hbp
  · -- b < 0: `ω ≤ ω'` in `(π/2 - θ, π/2]`, and `h/(1/N - cos²)` is increasing there
    have hu : cos ω ^ 2 < 1 / N := by nlinarith
    have hu' : cos ω' ^ 2 - 1 / N ≤ cos ω ^ 2 - 1 / N := by
      have : a' * (cos ω' ^ 2 - 1 / N) ≤ a' * (cos ω ^ 2 - 1 / N) := by nlinarith
      exact le_of_mul_le_mul_left this ha'
    have hωω : ω ≤ ω' := by
      by_contra hc; push_neg at hc
      have := cos_sq_anti hw0' hc.le hw1
      have : cos ω' ^ 2 = cos ω ^ 2 := by linarith
      have hc' : ω' < ω := hc
      have h4 : cos ω < cos ω' := cos_lt_cos_of_nonneg_of_le_pi hw0' (by linarith [pi_pos]) hc'
      have h5 : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hw1⟩
      nlinarith
    have hω0 := omega0_lt N hN hw0 hw1 hu
    have hden : ∀ x ∈ Icc ω (π / 2), 1 / (N : ℝ) + (-1) * cos x ^ 2 ≠ 0 := by
      intro x hx; have := cos_sq_anti hw0 hx.1 hx.2; apply ne_of_gt; linarith
    -- the two branches of h as quotients
    set L := fun x => (cc N + (-1) * x) / (1 / (N : ℝ) + (-1) * cos x ^ 2)
    set R := fun x => (cc N - 2 * wstar N + 1 * x) / (1 / (N : ℝ) + (-1) * cos x ^ 2)
    have hL : MonotoneOn L (Icc ω (wstar N)) := by
      apply quot_monotoneOn
      · intro x hx; exact hden x ⟨hx.1, hx.2.trans hws2⟩
      · intro x hx
        have := halting_left N hN (ω := x) (by linarith [hx.1, pi_pos]) (by have := hx.2; unfold wstar at this; linarith)
        unfold cc; nlinarith
    have hR : MonotoneOn R (Icc (max ω (wstar N)) (π / 2)) := by
      apply quot_monotoneOn
      · intro x hx; exact hden x ⟨(le_max_left _ _).trans hx.1, hx.2⟩
      · intro x hx
        have h5 : wstar N ≤ x := (le_max_right _ _).trans hx.1.le
        have := halting_right N hN (ω := x) (by unfold wstar at h5; linarith) hx.2.le
        unfold cc wstar at *; nlinarith
    have hLR : L (wstar N) = R (wstar N) := by simp only [L, R]; ring
    -- value of the potential through the quotient
    have hval : ∀ x z, 0 < x → x * (cos z ^ 2 - 1 / N) = (1 - 1 / N) * b → 1 / (N : ℝ) + (-1) * cos z ^ 2 ≠ 0 →
        x * hfun N z = (1 - 1 / N) * (-b) * (hfun N z / (1 / N + (-1) * cos z ^ 2)) := by
      intro x z hx h hz
      rw [show (1 - 1 / (N : ℝ)) * (-b) = x * (1 / N + (-1) * cos z ^ 2) by linear_combination h]
      generalize (1 / (N : ℝ) + (-1) * cos z ^ 2) = v at hz ⊢
      field_simp
    have hden' : 1 / (N : ℝ) + (-1) * cos ω' ^ 2 ≠ 0 := hden ω' ⟨hωω, hw1'⟩
    rw [hval a ω ha hid (hden ω ⟨le_rfl, hw1⟩), hval a' ω' ha' hid' hden']
    have hmono : hfun N ω / (1 / N + (-1) * cos ω ^ 2) ≤ hfun N ω' / (1 / N + (-1) * cos ω' ^ 2) := by
      have eL : ∀ x, x ≤ wstar N → hfun N x / (1 / N + (-1) * cos x ^ 2) = L x := by
        intro x hx; simp only [L, hfun, if_pos hx]; ring_nf
      have eR : ∀ x, wstar N ≤ x → hfun N x / (1 / N + (-1) * cos x ^ 2) = R x := by
        intro x hx; simp only [R, hfun]; split_ifs with h
        · congr 1; have : x = wstar N := le_antisymm h hx
          subst this; ring
        · ring_nf
      rcases le_or_gt ω' (wstar N) with h1 | h1
      · rw [eL ω (hωω.trans h1), eL ω' h1]
        exact hL ⟨le_rfl, hωω.trans h1⟩ ⟨hωω, h1⟩ hωω
      · rcases le_or_gt (wstar N) ω with h2 | h2
        · rw [eR ω h2, eR ω' h1.le]
          exact hR ⟨max_le le_rfl h2, hw1⟩ ⟨max_le hωω h1.le, hw1'⟩ hωω
        · rw [eL ω h2.le, eR ω' h1.le]
          calc L ω ≤ L (wstar N) := hL ⟨le_rfl, h2.le⟩ ⟨h2.le, le_rfl⟩ h2.le
            _ = R (wstar N) := hLR
            _ ≤ R ω' := hR ⟨max_le h2.le le_rfl, hws2⟩ ⟨max_le hωω h1.le, hw1'⟩ h1.le
    have : 0 ≤ (1 - 1 / (N : ℝ)) * (-b) := by nlinarith
    exact mul_le_mul_of_nonneg_left hmono this
  · -- b = 0: the angle is `π/2 - θ` for every `a`, and `h` is negative there
    subst hbz
    simp only [ω, ω', omegaOf_zero N hN ha, omegaOf_zero N hN ha']
    have := hfun_omega0 N hN; nlinarith
  · -- b > 0: `ω' ≤ ω < π/2 - θ`, and `(c - x)/(cos² x - 1/N)` is decreasing there
    have hu : 1 / N < cos ω ^ 2 := by nlinarith
    have hu' : cos ω ^ 2 - 1 / N ≤ cos ω' ^ 2 - 1 / N := by
      have : a' * (cos ω ^ 2 - 1 / N) ≤ a' * (cos ω' ^ 2 - 1 / N) := by nlinarith
      exact le_of_mul_le_mul_left this ha'
    have hωω : ω' ≤ ω := by
      by_contra hc; push_neg at hc
      have h4 : cos ω' < cos ω := cos_lt_cos_of_nonneg_of_le_pi hw0 (by linarith [pi_pos]) hc
      have h5 : 0 ≤ cos ω' := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hw1'⟩
      nlinarith
    have hω0 := lt_omega0 N hN hw0 hw1 hu
    have hden : ∀ x ∈ Icc ω' ω, -(1 / (N : ℝ)) + 1 * cos x ^ 2 ≠ 0 := by
      intro x hx; apply ne_of_gt
      have := cos_sq_anti (hw0'.trans hx.1) hx.2 hw1; linarith
    have hA : AntitoneOn (fun x => (cc N + (-1) * x) / (-(1 / (N : ℝ)) + 1 * cos x ^ 2)) (Icc ω' ω) := by
      apply quot_antitoneOn _ _ _ _ _ _ hden
      intro x hx
      have := halting_left N hN (ω := x) (by linarith [hx.1, hw0']) (by linarith [hx.2])
      unfold cc; nlinarith
    have hval : ∀ x z, 0 < x → x * (cos z ^ 2 - 1 / N) = (1 - 1 / N) * b → -(1 / (N : ℝ)) + 1 * cos z ^ 2 ≠ 0 →
        z ≤ wstar N → x * hfun N z = (1 - 1 / N) * b * ((cc N + (-1) * z) / (-(1 / N) + 1 * cos z ^ 2)) := by
      intro x z hx h hz hzw; simp only [hfun, if_pos hzw]
      rw [show (1 - 1 / (N : ℝ)) * b = x * (-(1 / N) + 1 * cos z ^ 2) by linear_combination -h]
      generalize (-(1 / (N : ℝ)) + 1 * cos z ^ 2) = v at hz ⊢
      field_simp; ring
    rw [hval a ω ha hid (hden ω ⟨hωω, le_rfl⟩) (by linarith), hval a' ω' ha' hid' (hden ω' ⟨le_rfl, hωω⟩) (by linarith)]
    exact mul_le_mul_of_nonneg_left (hA ⟨le_rfl, hωω⟩ ⟨hωω, le_rfl⟩ hωω) (by nlinarith)

/-- Halting, including halting of everything (`a' = 0`, which feasibility forces to `b = 0`). -/
theorem halting_mono' (hN : 2 ≤ N) {a a' b : ℝ} (ha' : 0 ≤ a') (haa : a' ≤ a) (hb1 : b ≤ a')
    (hb2 : 0 ≤ a' + (N - 1) * b) : Phi N a b ≤ Phi N a' b := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rcases ha'.lt_or_eq with h | h
  · exact halting_mono N hN h haa hb1 hb2
  · subst h
    have hb : b = 0 := by nlinarith
    subst hb
    rcases (ha'.trans haa).lt_or_eq with ha | ha
    · unfold Phi; rw [omegaOf_zero N hN ha]; have := hfun_omega0 N hN; simp; nlinarith
    · rw [← ha]

/-- A round moves the potential by at most `δ a` when it moves the angle by at most `δ`. -/
lemma round_step {a b b' δ : ℝ} (ha : 0 ≤ a) (h : |omegaOf N a b' - omegaOf N a b| ≤ δ) :
    Phi N a b - δ * a ≤ Phi N a b' := by
  unfold Phi
  have h1 := hfun_lip N (omegaOf N a b') (omegaOf N a b)
  have h2 : a * |hfun N (omegaOf N a b') - hfun N (omegaOf N a b)| ≤ a * δ :=
    mul_le_mul_of_nonneg_left (h1.trans h) ha
  have h3 := neg_abs_le (hfun N (omegaOf N a b') - hfun N (omegaOf N a b))
  nlinarith

/-- **Theorem 1, potential form.** A trajectory starts at `a = b = 1`. In step `t` a round changes `b_t` to
`b_{t+1}` with the angle moving by at most `δ`, then halting lowers `a_t` to `a_{t+1}` keeping the state
feasible; it ends at `a_T = 0`. Then `π/4 + 1/2 - θ ≤ δ ∑_{t<T} a_t`. -/
theorem lower_bound (hN : 2 ≤ N) (δ : ℝ) (T : ℕ) (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) (haT : a T = 0)
    (hround : ∀ t < T, |omegaOf N (a t) (b (t + 1)) - omegaOf N (a t) (b t)| ≤ δ)
    (hhalt : ∀ t < T, 0 ≤ a (t + 1) ∧ a (t + 1) ≤ a t ∧ b (t + 1) ≤ a (t + 1) ∧
      0 ≤ a (t + 1) + (N - 1) * b (t + 1)) :
    cc N ≤ δ * ∑ t ∈ Finset.range T, a t := by
  have hnn : ∀ t ≤ T, 0 ≤ a t := by
    intro t ht; cases t with
    | zero => rw [ha0]; norm_num
    | succ t => exact (hhalt t (by omega)).1
  have key : ∀ n ≤ T, Phi N 1 1 - δ * ∑ t ∈ Finset.range n, a t ≤ Phi N (a n) (b n) := by
    intro n hn
    induction n with
    | zero => simp [ha0, hb0]
    | succ n ih =>
      have ih := ih (by omega)
      obtain ⟨h1, h2, h3, h4⟩ := hhalt n (by omega)
      have hr := round_step N (hnn n (by omega)) (hround n (by omega))
      have hh := halting_mono' N hN h1 h2 h3 h4
      rw [Finset.sum_range_succ]; linarith
  have := key T le_rfl
  have hPhi0 : Phi N 1 1 = cc N := by
    unfold Phi; rw [omegaOf_one N hN, one_mul]; unfold hfun
    obtain ⟨hθ0, hθ4, -⟩ := theta_facts N hN
    rw [if_pos (by unfold wstar; linarith [pi_pos])]; ring
  rw [hPhi0, haT] at this; unfold Phi at this; simp at this; linarith

/-! ## Non-vacuity

For `N = 4` and `δ = π/3 = 2 arcsin (1/2)` (one query per round), exact Grover search is a trajectory of one
step: the round takes `(a, b) = (1, 1)` to `(1, 0)`, halting takes it to `(0, 0)`. So the hypotheses of
`lower_bound` hold, and its conclusion `π/4 + 1/2 - θ ≤ π/3` is not trivial: `π/4 + 1/2 - θ > 0`. -/

lemma theta_four : theta 4 = π / 6 := by
  unfold theta
  rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)], ← sin_pi_div_six,
    arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

example : ∃ (a b : ℕ → ℝ), a 0 = 1 ∧ b 0 = 1 ∧ a 1 = 0 ∧
    (∀ t < 1, |omegaOf 4 (a t) (b (t + 1)) - omegaOf 4 (a t) (b t)| ≤ π / 3) ∧
    (∀ t < 1, 0 ≤ a (t + 1) ∧ a (t + 1) ≤ a t ∧ b (t + 1) ≤ a (t + 1) ∧
      0 ≤ a (t + 1) + ((4 : ℕ) - 1) * b (t + 1)) := by
  refine ⟨fun t => if t = 0 then 1 else 0, fun t => if t = 0 then 1 else 0, by simp, by simp, by simp, ?_, ?_⟩
  · intro t ht
    have : t = 0 := by omega
    subst this
    show |omegaOf 4 1 0 - omegaOf 4 1 1| ≤ π / 3
    rw [omegaOf_zero 4 (by norm_num) one_pos, omegaOf_one 4 (by norm_num), theta_four, sub_zero,
      abs_of_nonneg (by linarith [pi_pos])]; linarith [pi_pos]
  · intro t ht
    have : t = 0 := by omega
    subst this; norm_num

example : 0 < cc 4 := cc_pos 4 (by norm_num)

end ZeroErrorSearch
