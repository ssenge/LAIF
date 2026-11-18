import LejepaDyn.Flow

/-!
# Critical points of linear LeJEPA

At a critical point of `L(W) = tr(W Δ Wᵀ) + μ ∫ h(aᵀ W Σ Wᵀ a) dν`, the images `vᵢ = W eᵢ` of common
eigenvectors of `Δ` and `Σ = SᵀS` with different costs `δᵢ/σᵢ` are orthogonal. For an orthonormal common
eigenbasis with distinct costs, the embedding covariance `M = W Σ Wᵀ` therefore has the eigenvectors `vⱼ` with the
eigenvalues `nⱼ = σⱼ ‖vⱼ‖²`, at most `K` of the `vⱼ` are nonzero, and `tr(W Δ Wᵀ) = Σ δⱼ ‖vⱼ‖²`.
The direction law `ν` is any finite measure on the unit sphere, so finite sets of slices are included.
-/

open MeasureTheory Finset Filter

namespace LejepaDyn

variable {K d : ℕ}

lemma dot_comm (u v : Fin K → ℝ) : dot u v = dot v u := by
  simp only [dot]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- `Σₖ uₖ (G v)ₖ = uᵀ G v`, the bilinear form of `G = ∫ h'(aᵀ M a) a aᵀ dν`. -/
lemma sum_mul_gint {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) (B : Fin d → Fin K → ℝ) (u v : Fin K → ℝ) :
    ∑ k, u k * ∫ a, hp (qf B a) * (a k * dot v a) ∂ν = ∫ a, hp (qf B a) * (dot u a * dot v a) ∂ν := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun k _ => (integrable_hp_mul hs hm hC B
    (by unfold dot; fun_prop : Continuous fun a : Fin K → ℝ => a k * dot v a)).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  have : ∑ k, u k * (hp (qf B a) * (a k * dot v a)) = hp (qf B a) * dot v a * ∑ k, u k * a k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  dsimp only
  rw [this, show ∑ k, u k * a k = dot u a from rfl]; ring

/-- **Orthogonality at critical points.** If `grad L (W) = 0` and `e, e'` are common eigenvectors of `Δ` and `SᵀS`
with eigenvalues `(δ, σ)` and `(δ', σ')`, then `(δ σ' - δ' σ) ⟨W e, W e'⟩ = 0`. -/
theorem crit_orth {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {μ σ δ σ' δ' : ℝ} {Δ S : Fin d → Fin d → ℝ}
    {e e' : Fin d → ℝ} (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q)
    (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q) (hΔe' : ∀ q, ∑ p, Δ q p * e' p = δ' * e' q)
    (hSe' : ∀ q, ∑ r, S r q * ∑ p, S r p * e' p = σ' * e' q) {W : Fin K → Fin d → ℝ}
    (hcrit : ∀ k p, grad ν hp μ Δ S W k p = 0) :
    (δ * σ' - δ' * σ) * dot (col W e) (col W e') = 0 := by
  set B := bW S W
  have eq : ∀ {δ σ : ℝ} {e : Fin d → ℝ}, (∀ q, ∑ p, Δ q p * e p = δ * e q) →
      (∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q) → ∀ u : Fin K → ℝ,
      δ * dot u (col W e) + μ * σ * ∫ a, hp (qf B a) * (dot u a * dot (col W e) a) ∂ν = 0 := by
    intro δ σ e h1 h2 u
    have hk : ∀ k, 2 * δ * col W e k + 2 * μ * σ * ∫ a, hp (qf B a) * (a k * dot (col W e) a) ∂ν = 0 := by
      intro k; rw [← grad_col hs hm hC h1 h2 W k]; simp [hcrit]
    have hsum : ∑ k, u k * (2 * δ * col W e k + 2 * μ * σ * ∫ a, hp (qf B a) * (a k * dot (col W e) a) ∂ν) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hk k, mul_zero]
    have e1 : ∑ k, u k * (2 * δ * col W e k) = 2 * δ * dot u (col W e) := by
      simp only [dot, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ k, u k * (2 * μ * σ * ∫ a, hp (qf B a) * (a k * dot (col W e) a) ∂ν) =
        2 * μ * σ * ∑ k, u k * ∫ a, hp (qf B a) * (a k * dot (col W e) a) ∂ν := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [mul_add, Finset.sum_add_distrib] at hsum
    rw [e1, e2, sum_mul_gint hs hm hC B u (col W e)] at hsum
    linarith
  have a1 := eq hΔe hSe (col W e')
  have a2 := eq hΔe' hSe' (col W e)
  have sym : ∫ a, hp (qf B a) * (dot (col W e) a * dot (col W e') a) ∂ν =
      ∫ a, hp (qf B a) * (dot (col W e') a * dot (col W e) a) ∂ν := by
    congr 1; funext a; ring
  rw [dot_comm (col W e') (col W e)] at a1
  rw [sym] at a2
  linear_combination σ' * a1 - σ * a2

/-! ## Orthonormal common eigenbasis -/

section Basis

variable {E : Fin d → Fin d → ℝ} (horth : ∀ i j, ∑ p, E i p * E j p = if i = j then 1 else 0)
  (hcomp : ∀ p q, ∑ i, E i p * E i q = if p = q then 1 else 0)

include hcomp in
lemma W_expand (W : Fin K → Fin d → ℝ) (k : Fin K) (p : Fin d) : W k p = ∑ i, col W (E i) k * E i p := by
  simp only [col, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, hcomp]
  simp

include hcomp in
/-- `tr(W Δ Wᵀ) = Σᵢ δᵢ ‖W eᵢ‖²` for every `W`. -/
lemma invc_eq {Δ : Fin d → Fin d → ℝ} {δ : Fin d → ℝ} (hΔ : ∀ i q, ∑ p, Δ q p * E i p = δ i * E i q)
    (W : Fin K → Fin d → ℝ) : invc Δ W = ∑ i, δ i * nsq (col W (E i)) := by
  have h1 : ∀ k p, ∑ q, Δ p q * W k q = ∑ i, col W (E i) k * (δ i * E i p) := by
    intro k p
    simp only [W_expand hcomp W k, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hΔ i p, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  calc invc Δ W = ∑ k, ∑ p, W k p * ∑ q, Δ p q * W k q := by
        simp only [invc, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ k, ∑ i, δ i * col W (E i) k ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [h1, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have : ∑ p, W k p * (col W (E i) k * (δ i * E i p)) = δ i * col W (E i) k * ∑ p, W k p * E i p := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [this, show ∑ p, W k p * E i p = col W (E i) k from rfl]; ring
    _ = ∑ i, δ i * nsq (col W (E i)) := by
        rw [Finset.sum_comm]; simp only [nsq, Finset.mul_sum]

include horth hcomp in
/-- `M = W SᵀS Wᵀ = Σᵢ σᵢ vᵢ vᵢᵀ` with `vᵢ = W eᵢ`, for every `W`. -/
lemma M_eq {S : Fin d → Fin d → ℝ} {σ : Fin d → ℝ} (hS : ∀ i q, ∑ r, S r q * ∑ p, S r p * E i p = σ i * E i q)
    (W : Fin K → Fin d → ℝ) (k l : Fin K) :
    ∑ r, bW S W r k * bW S W r l = ∑ i, σ i * col W (E i) k * col W (E i) l := by
  set y : Fin d → Fin d → ℝ := fun i r => ∑ p, S r p * E i p
  have hb : ∀ r k, bW S W r k = ∑ i, col W (E i) k * y i r := by
    intro r k
    simp only [bW, y]
    conv_lhs => rw [show col W (S r) k = ∑ p, W k p * S r p from rfl]
    simp only [W_expand hcomp W k, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have yd : ∀ i r, y i r = ∑ p, S r p * E i p := fun _ _ => rfl
  have hy : ∀ i j, ∑ r, y i r * y j r = if i = j then σ i else 0 := by
    intro i j
    calc ∑ r, y i r * y j r = ∑ r, ∑ q, y i r * (S r q * E j q) := by
          refine Finset.sum_congr rfl fun r _ => ?_; rw [yd j r, Finset.mul_sum]
      _ = ∑ q, ∑ r, E j q * (S r q * y i r) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = ∑ q, E j q * (σ i * E i q) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.mul_sum, show ∑ r, S r q * y i r = σ i * E i q from hS i q]
      _ = σ i * ∑ q, E i q * E j q := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [horth]; split_ifs <;> simp
  calc ∑ r, bW S W r k * bW S W r l
      = ∑ r, ∑ i, ∑ j, col W (E i) k * col W (E j) l * (y i r * y j r) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hb, hb, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ i, ∑ j, ∑ r, col W (E i) k * col W (E j) l * (y i r * y j r) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, col W (E i) k * col W (E j) l * ∑ r, y i r * y j r := by
        simp only [Finset.mul_sum]
    _ = ∑ i, σ i * col W (E i) k * col W (E i) l := by
        simp only [hy, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        exact Finset.sum_congr rfl fun _ _ => by ring

include horth hcomp in
/-- **Learned features at a critical point.** With an orthonormal common eigenbasis `eᵢ` of `Δ` and `SᵀS` with
distinct costs, at every critical point each `vⱼ = W eⱼ` is an eigenvector of `M = W SᵀS Wᵀ` with eigenvalue
`nⱼ = σⱼ ‖vⱼ‖²`, the learned variance of feature `j`. -/
theorem crit_eigen {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {μ : ℝ} {Δ S : Fin d → Fin d → ℝ}
    {δ σ : Fin d → ℝ} (hΔ : ∀ i q, ∑ p, Δ q p * E i p = δ i * E i q)
    (hS : ∀ i q, ∑ r, S r q * ∑ p, S r p * E i p = σ i * E i q)
    (hdist : ∀ i j, i ≠ j → δ i * σ j ≠ δ j * σ i) {W : Fin K → Fin d → ℝ}
    (hcrit : ∀ k p, grad ν hp μ Δ S W k p = 0) (j : Fin d) (k : Fin K) :
    ∑ l, (∑ r, bW S W r k * bW S W r l) * col W (E j) l = σ j * nsq (col W (E j)) * col W (E j) k := by
  have ho : ∀ i, i ≠ j → dot (col W (E i)) (col W (E j)) = 0 := fun i hij => by
    have := crit_orth hs hm hC (hΔ i) (hS i) (hΔ j) (hS j) hcrit
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (hdist i j hij))
  simp only [M_eq horth hcomp hS, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ l, σ i * col W (E i) k * col W (E i) l * col W (E j) l =
      σ i * col W (E i) k * dot (col W (E i)) (col W (E j)) := fun i => by
    simp only [dot, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [this]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho i hij, mul_zero]) (by simp)]
  simp only [dot, nsq]
  rw [show ∑ x, col W (E j) x * col W (E j) x = ∑ x, col W (E j) x ^ 2 from
    Finset.sum_congr rfl fun _ _ => (sq _).symm]
  ring

/-- **At most `K` features are learned at a critical point.** -/
theorem crit_card_le {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {μ : ℝ} {Δ S : Fin d → Fin d → ℝ}
    {δ σ : Fin d → ℝ} (hΔ : ∀ i q, ∑ p, Δ q p * E i p = δ i * E i q)
    (hS : ∀ i q, ∑ r, S r q * ∑ p, S r p * E i p = σ i * E i q)
    (hdist : ∀ i j, i ≠ j → δ i * σ j ≠ δ j * σ i) {W : Fin K → Fin d → ℝ}
    (hcrit : ∀ k p, grad ν hp μ Δ S W k p = 0) :
    (Finset.univ.filter fun i => col W (E i) ≠ 0).card ≤ K := by
  set s := Finset.univ.filter fun i => col W (E i) ≠ 0
  have ho : ∀ i j, i ≠ j → dot (col W (E i)) (col W (E j)) = 0 := fun i j hij => by
    have := crit_orth hs hm hC (hΔ i) (hS i) (hΔ j) (hS j) hcrit
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (hdist i j hij))
  have hli : LinearIndependent ℝ (fun i : s => col W (E i)) := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have h := congrArg (fun x => dot x (col W (E i))) hg
    simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero] at h
    have h2 : ∑ x, (∑ c ∈ t, g c * col W (E c) x) * col W (E i) x =
        ∑ c ∈ t, g c * dot (col W (E c)) (col W (E i)) := by
      simp only [dot, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h2, Finset.sum_eq_single i (fun c _ hci => by
      rw [ho c i (fun h' => hci (Subtype.ext h')), mul_zero]) (fun h' => absurd hi h')] at h
    have hn : dot (col W (E i)) (col W (E i)) ≠ 0 := by
      intro h0
      apply (Finset.mem_filter.1 i.2).2
      funext x
      have hsum : ∑ y, col W (E i) y ^ 2 = 0 := by
        rw [← h0]; simp only [dot]; exact Finset.sum_congr rfl fun _ _ => sq _
      have := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg (col W (E i) y)).1 hsum x
        (Finset.mem_univ _)
      simpa using this
    exact (mul_eq_zero.1 h).resolve_right hn
  have := hli.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using this

end Basis

/-- **Stationarity of the learned variance.** At a critical point, `δ ‖v‖² + μ σ vᵀ G v = 0` for `v = W e`, so
every learned feature is stationary for the reduced objective. -/
theorem crit_stat {ν : Measure (Fin K → ℝ)} [IsFiniteMeasure ν] (hs : ∀ᵐ a ∂ν, nsq a = 1) {hp : ℝ → ℝ}
    (hm : Measurable hp) {C : ℝ} (hC : ∀ x, 0 ≤ x → |hp x| ≤ C) {μ σ δ : ℝ} {Δ S : Fin d → Fin d → ℝ}
    {e : Fin d → ℝ} (hΔe : ∀ q, ∑ p, Δ q p * e p = δ * e q)
    (hSe : ∀ q, ∑ r, S r q * ∑ p, S r p * e p = σ * e q) {W : Fin K → Fin d → ℝ}
    (hcrit : ∀ k p, grad ν hp μ Δ S W k p = 0) :
    δ * nsq (col W e) + μ * σ * gq ν hp (bW S W) (col W e) = 0 := by
  have hk : ∀ k, 2 * δ * col W e k + 2 * μ * σ * ∫ a, hp (qf (bW S W) a) * (a k * dot (col W e) a) ∂ν = 0 := by
    intro k; rw [← grad_col hs hm hC hΔe hSe W k]; simp [hcrit]
  have h := Finset.sum_eq_zero (s := Finset.univ) fun k _ =>
    show col W e k * (2 * δ * col W e k + 2 * μ * σ * ∫ a, hp (qf (bW S W) a) * (a k * dot (col W e) a) ∂ν) = 0
      by rw [hk k, mul_zero]
  have h2 := sum_mul_gq hs hm hC (bW S W) (col W e)
  have e1 : ∑ k, col W e k * (2 * δ * col W e k + 2 * μ * σ * ∫ a, hp (qf (bW S W) a) * (a k * dot (col W e) a) ∂ν)
      = 2 * δ * nsq (col W e) + 2 * μ * σ * ∑ k, col W e k * ∫ a, hp (qf (bW S W) a) * (a k * dot (col W e) a) ∂ν := by
    simp only [nsq, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, h2] at h
  linarith

end LejepaDyn
