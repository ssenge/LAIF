import SigregDim.Stiffness

/-!
# Minimizers of the reduced linear objective: ordering, spectral gaps and a rank bound

`F(λ) = ∑ₖ cₖ λₖ + μ · S_h(λ)` over nonnegative spectra `λ`, where `cₖ` is the invariance cost of
direction `k` and `S_h` the sliced regularizer. At a global minimizer:

* `ordering`: a cheaper direction never carries less variance;
* `gap`: if direction `j` is active and `cᵢ < cⱼ`, then `cⱼ - cᵢ ≤ 2 L μ (λᵢ - λⱼ) / (K(K+2))`;
* `rank_bound`: if consecutive costs differ by at least `δ`, the number `r` of active directions
  satisfies `r (r - 1) ≤ 4 L μ (∑ cₖ + μ κ) / (c₁ δ K (K+2))`.
-/

open MeasureTheory Finset

namespace SigregDim

variable {K : ℕ} {ν : Measure (Fin K → ℝ)}

/-- The reduced objective: invariance cost plus `μ` times the sliced regularizer. -/
noncomputable def objective (ν : Measure (Fin K → ℝ)) (h : ℝ → ℝ) (c : Fin K → ℝ) (μ : ℝ)
    (lam : Fin K → ℝ) : ℝ :=
  ∑ k, c k * lam k + μ * sliced ν h lam

/-- `λ` is a global minimizer of the objective over nonnegative spectra. -/
def IsMinimizer (ν : Measure (Fin K → ℝ)) (h : ℝ → ℝ) (c : Fin K → ℝ) (μ : ℝ)
    (lam : Fin K → ℝ) : Prop :=
  (∀ k, 0 ≤ lam k) ∧ ∀ lam' : Fin K → ℝ, (∀ k, 0 ≤ lam' k) →
    objective ν h c μ lam ≤ objective ν h c μ lam'

/-- A sum over `Fin K` split off at two distinct indices. -/
lemma sum_split_two {f : Fin K → ℝ} {i j : Fin K} (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (univ.erase i).erase j, f k := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i),
    ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨hij.symm, mem_univ j⟩)]
  ring

lemma sum_mul_swap (f g : Fin K → ℝ) {i j : Fin K} (hij : i ≠ j) :
    ∑ k, f k * g (Equiv.swap i j k) = ∑ k, f k * g k + (f i - f j) * (g j - g i) := by
  rw [sum_split_two (f := fun k => f k * g (Equiv.swap i j k)) hij,
    sum_split_two (f := fun k => f k * g k) hij]
  have hrest : ∑ k ∈ (univ.erase i).erase j, f k * g (Equiv.swap i j k) =
      ∑ k ∈ (univ.erase i).erase j, f k * g k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, hrest]
  ring

lemma measurable_comp_swap (i j : Fin K) :
    Measurable fun x : Fin K → ℝ => x ∘ Equiv.swap i j :=
  measurable_pi_iff.2 fun k => measurable_pi_apply (Equiv.swap i j k)

/-- Integrals are unchanged by a transposition of the coordinates of the direction. -/
lemma integral_comp_swap (hν : SphereLike K ν) (i j : Fin K) {f : (Fin K → ℝ) → ℝ}
    (hf : Measurable f) : ∫ x, f (x ∘ Equiv.swap i j) ∂ν = ∫ x, f x ∂ν := by
  rw [← integral_map (measurable_comp_swap i j).aemeasurable hf.aestronglyMeasurable, hν.swap]

lemma sliceVar_comp_swap (lam x : Fin K → ℝ) (i j : Fin K) :
    sliceVar lam (x ∘ Equiv.swap i j) = sliceVar (lam ∘ Equiv.swap i j) x := by
  unfold sliceVar
  rw [← Equiv.sum_comp (Equiv.swap i j)]
  simp [Function.comp, Equiv.swap_apply_self]

lemma sliceVar_swap_eq (lam x : Fin K → ℝ) {i j : Fin K} (hij : i ≠ j) :
    sliceVar (lam ∘ Equiv.swap i j) x =
      sliceVar lam x - (lam i - lam j) * (x i ^ 2 - x j ^ 2) := by
  unfold sliceVar
  have h1 := sum_mul_swap (fun k => x k ^ 2) lam hij
  simp only [Function.comp]
  calc ∑ k, lam (Equiv.swap i j k) * x k ^ 2 = ∑ k, x k ^ 2 * lam (Equiv.swap i j k) :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ = ∑ k, x k ^ 2 * lam k + (x i ^ 2 - x j ^ 2) * (lam j - lam i) := h1
    _ = ∑ k, lam k * x k ^ 2 - (lam i - lam j) * (x i ^ 2 - x j ^ 2) := by
        rw [Finset.sum_congr rfl fun k _ => mul_comm (x k ^ 2) (lam k)]; ring

lemma sliced_swap (hν : SphereLike K ν) {h : ℝ → ℝ} (hmeas : Measurable h) (lam : Fin K → ℝ)
    (i j : Fin K) : sliced ν h (lam ∘ Equiv.swap i j) = sliced ν h lam := by
  unfold sliced
  simp_rw [← sliceVar_comp_swap]
  exact integral_comp_swap hν i j (f := fun x => h (sliceVar lam x))
    (hmeas.comp (measurable_sliceVar lam))

/-- **Ordering.** At a minimizer a direction with smaller invariance cost carries at least as much
variance. -/
theorem ordering (hν : SphereLike K ν) {h : ℝ → ℝ} (hmeas : Measurable h) {c : Fin K → ℝ} {μ : ℝ}
    {lam : Fin K → ℝ} (hmin : IsMinimizer ν h c μ lam) {i j : Fin K} (hc : c i < c j) :
    lam j ≤ lam i := by
  by_contra hlt
  push Not at hlt
  have hij : i ≠ j := fun e => by subst e; exact lt_irrefl _ hc
  have hle := hmin.2 (lam ∘ Equiv.swap i j) fun k => hmin.1 _
  unfold objective at hle
  rw [sliced_swap hν hmeas, Function.comp_def, sum_mul_swap c lam hij] at hle
  nlinarith

/-- The perturbed spectrum `λ + ε (eᵢ - eⱼ)`. -/
def shift (lam : Fin K → ℝ) (i j : Fin K) (ε : ℝ) : Fin K → ℝ :=
  fun k => lam k + ε * ((if k = i then 1 else 0) - (if k = j then 1 else 0))

lemma sum_mul_shift (f lam : Fin K → ℝ) (i j : Fin K) (ε : ℝ) :
    ∑ k, f k * shift lam i j ε k = ∑ k, f k * lam k + ε * (f i - f j) := by
  unfold shift
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [mul_comm, mul_left_comm, Finset.mul_sum]

lemma sliceVar_shift (lam x : Fin K → ℝ) (i j : Fin K) (ε : ℝ) :
    sliceVar (shift lam i j ε) x = sliceVar lam x + ε * (x i ^ 2 - x j ^ 2) := by
  unfold sliceVar
  rw [Finset.sum_congr rfl fun k _ => mul_comm (shift lam i j ε k) (x k ^ 2),
    sum_mul_shift (fun k => x k ^ 2), Finset.sum_congr rfl fun k _ => mul_comm (x k ^ 2) (lam k)]

/-- Assumptions on the slice function `h` with derivative `h'` on `[0, ∞)`: measurability,
bounds, the quadratic upper model (descent inequality) and the one-sided curvature bound
`h' y - h' x ≤ L (y - x)` for `x ≤ y` (for smooth `h`: `h'' ≤ L`). -/
structure SliceFn (h h' : ℝ → ℝ) (L : ℝ) : Prop where
  meas : Measurable h
  meas' : Measurable h'
  bdd : ∃ C, ∀ x, 0 ≤ x → |h x| ≤ C
  bdd' : ∃ C, ∀ x, 0 ≤ x → |h' x| ≤ C
  desc : ∀ x y, 0 ≤ x → 0 ≤ y → h y ≤ h x + h' x * (y - x) + L / 2 * (y - x) ^ 2
  curv : ∀ x y, 0 ≤ x → x ≤ y → h' y - h' x ≤ L * (y - x)
  L_nonneg : 0 ≤ L

lemma integrable_h (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L : ℝ} (hh : SliceFn h h' L)
    {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) : Integrable (fun x => h (sliceVar lam x)) ν := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact integrable_of_bdd hν (hh.meas.comp (measurable_sliceVar lam)) C
    (Filter.Eventually.of_forall fun x => hC _ (sliceVar_nonneg hlam x))

lemma abs_diff_sq_le_ae (hν : SphereLike K ν) (i j : Fin K) :
    ∀ᵐ x ∂ν, |x i ^ 2 - x j ^ 2| ≤ 1 := by
  filter_upwards [sq_le_one_ae hν] with x hx
  rw [abs_le]
  constructor <;> nlinarith [hx i, hx j, sq_nonneg (x i), sq_nonneg (x j)]

lemma integrable_h'_mul (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L : ℝ} (hh : SliceFn h h' L)
    {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) (i j : Fin K) :
    Integrable (fun x => h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2)) ν := by
  obtain ⟨C, hC⟩ := hh.bdd'
  refine integrable_of_bdd hν ((hh.meas'.comp (measurable_sliceVar lam)).mul (by fun_prop)) C ?_
  filter_upwards [abs_diff_sq_le_ae hν i j] with x hx
  rw [abs_mul]
  have h1 := hC _ (sliceVar_nonneg hlam x)
  calc |h' (sliceVar lam x)| * |x i ^ 2 - x j ^ 2| ≤ C * 1 :=
        mul_le_mul h1 hx (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = C := mul_one C

lemma integrable_diff_sq_sq (hν : SphereLike K ν) (i j : Fin K) :
    Integrable (fun x => (x i ^ 2 - x j ^ 2) ^ 2) ν :=
  integrable_of_bdd hν (by fun_prop) 1 (by
    filter_upwards [abs_diff_sq_le_ae hν i j] with x hx
    rw [abs_pow]
    calc |x i ^ 2 - x j ^ 2| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      _ = 1 := one_pow 2)

/-- `E (aᵢ² - aⱼ²)² = 4/(K(K+2))` for `i ≠ j`. -/
lemma integral_diff_sq_sq (hν : SphereLike K ν) {i j : Fin K} (hij : i ≠ j) :
    ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν = 4 / (K * (K + 2)) := by
  have hrw : (fun x : Fin K → ℝ => (x i ^ 2 - x j ^ 2) ^ 2) =
      fun x => x i ^ 4 + x j ^ 4 - 2 * (x i ^ 2 * x j ^ 2) := by
    funext x; ring
  have hi4 : Integrable (fun x : Fin K → ℝ => x i ^ 4) ν := by
    have := integrable_sq_mul_sq hν i i
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hj4 : Integrable (fun x : Fin K → ℝ => x j ^ 4) ν := by
    have := integrable_sq_mul_sq hν j j
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have h44 : Integrable (fun x : Fin K → ℝ => x i ^ 4 + x j ^ 4) ν := hi4.add hj4
  have h22 : Integrable (fun x : Fin K → ℝ => 2 * (x i ^ 2 * x j ^ 2)) ν :=
    (integrable_sq_mul_sq hν i j).const_mul 2
  rw [hrw, integral_sub h44 h22, integral_add hi4 hj4, integral_const_mul, hν.m4, hν.m4,
    hν.m22 i j hij]
  ring

/-- The first-order term is controlled by the swap symmetry: if `λⱼ ≤ λᵢ`, then
`E[h'(X) (aᵢ² - aⱼ²)] ≤ (L/2) (λᵢ - λⱼ) E (aᵢ² - aⱼ²)²`. -/
lemma first_order_le (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L : ℝ} (hh : SliceFn h h' L)
    {lam : Fin K → ℝ} (hlam : ∀ k, 0 ≤ lam k) {i j : Fin K} (hij : i ≠ j) (hord : lam j ≤ lam i) :
    ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν ≤
      L / 2 * (lam i - lam j) * ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν := by
  set E1 := ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν
  have hlamσ : ∀ k, 0 ≤ (lam ∘ Equiv.swap i j) k := fun k => hlam _
  -- the swapped integrand integrates to `-E1`
  have hswap : ∫ x, h' (sliceVar (lam ∘ Equiv.swap i j) x) * (x i ^ 2 - x j ^ 2) ∂ν = -E1 := by
    have := integral_comp_swap hν i j
      (f := fun x => h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2))
      ((hh.meas'.comp (measurable_sliceVar lam)).mul (by fun_prop))
    simp only [sliceVar_comp_swap, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right] at this
    have hneg : ∫ x, h' (sliceVar (lam ∘ Equiv.swap i j) x) * (x i ^ 2 - x j ^ 2) ∂ν =
        -∫ x, h' (sliceVar (lam ∘ Equiv.swap i j) x) * (x j ^ 2 - x i ^ 2) ∂ν := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [hneg, this]
  have hdiff : ∫ x, (h' (sliceVar lam x) - h' (sliceVar (lam ∘ Equiv.swap i j) x)) *
      (x i ^ 2 - x j ^ 2) ∂ν = 2 * E1 := by
    simp_rw [sub_mul]
    rw [integral_sub (integrable_h'_mul hν hh hlam i j) (integrable_h'_mul hν hh hlamσ i j),
      hswap]
    ring
  have hpt : ∀ x, (h' (sliceVar lam x) - h' (sliceVar (lam ∘ Equiv.swap i j) x)) *
      (x i ^ 2 - x j ^ 2) ≤ L * (lam i - lam j) * (x i ^ 2 - x j ^ 2) ^ 2 := by
    intro x
    have hX := sliceVar_nonneg hlam x
    have hX' := sliceVar_nonneg hlamσ x
    rw [sliceVar_swap_eq lam x hij] at hX' ⊢
    set X := sliceVar lam x
    set U := x i ^ 2 - x j ^ 2
    set d := lam i - lam j
    have hd : 0 ≤ d := by simp only [d]; linarith
    rcases le_total 0 U with hU | hU
    · have hle : X - d * U ≤ X := by nlinarith
      have hc := hh.curv _ _ hX' hle
      have : (h' X - h' (X - d * U)) * U ≤ (L * (X - (X - d * U))) * U :=
        mul_le_mul_of_nonneg_right hc hU
      nlinarith
    · have hle : X ≤ X - d * U := by nlinarith
      have hc := hh.curv _ _ hX hle
      have : (h' (X - d * U) - h' X) * (-U) ≤ (L * (X - d * U - X)) * (-U) :=
        mul_le_mul_of_nonneg_right hc (by linarith)
      nlinarith
  have hint : ∫ x, (h' (sliceVar lam x) - h' (sliceVar (lam ∘ Equiv.swap i j) x)) *
      (x i ^ 2 - x j ^ 2) ∂ν ≤ ∫ x, L * (lam i - lam j) * (x i ^ 2 - x j ^ 2) ^ 2 ∂ν := by
    refine integral_mono ?_ ((integrable_diff_sq_sq hν i j).const_mul _) hpt
    simp_rw [sub_mul]
    exact (integrable_h'_mul hν hh hlam i j).sub (integrable_h'_mul hν hh hlamσ i j)
  rw [hdiff, integral_const_mul] at hint
  linarith

/-- For every admissible step `ε`, minimality gives
`cⱼ - cᵢ ≤ μ E[h'(X)(aᵢ² - aⱼ²)] + μ (L/2) ε E(aᵢ² - aⱼ²)²`. -/
lemma gap_eps (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L : ℝ} (hh : SliceFn h h' L)
    {c : Fin K → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) {lam : Fin K → ℝ} (hmin : IsMinimizer ν h c μ lam)
    {i j : Fin K} (hij : i ≠ j) {ε : ℝ} (hε : 0 < ε) (hεj : ε ≤ lam j) :
    c j - c i ≤ μ * ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν +
      μ * (L / 2) * ε * ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν := by
  have hlam := hmin.1
  have hsh : ∀ k, 0 ≤ shift lam i j ε k := by
    intro k
    unfold shift
    by_cases hki : k = i
    · subst hki; simp [hij]; nlinarith [hlam k]
    · by_cases hkj : k = j
      · subst hkj; simp [hki]; linarith
      · simp [hki, hkj, hlam k]
  have hle := hmin.2 _ hsh
  unfold objective at hle
  rw [sum_mul_shift] at hle
  -- the sliced value after the step
  have hS : sliced ν h (shift lam i j ε) ≤ sliced ν h lam +
      ε * ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν +
      L / 2 * ε ^ 2 * ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν := by
    unfold sliced
    have iA := integrable_h hν hh hlam
    have iB : Integrable (fun x => ε * (h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2))) ν :=
      (integrable_h'_mul hν hh hlam i j).const_mul ε
    have iC : Integrable (fun x : Fin K → ℝ => L / 2 * ε ^ 2 * (x i ^ 2 - x j ^ 2) ^ 2) ν :=
      (integrable_diff_sq_sq hν i j).const_mul _
    have iAB : Integrable (fun x => h (sliceVar lam x) +
        ε * (h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2))) ν := iA.add iB
    have iABC : Integrable (fun x => h (sliceVar lam x) +
        ε * (h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2)) +
        L / 2 * ε ^ 2 * (x i ^ 2 - x j ^ 2) ^ 2) ν := iAB.add iC
    calc ∫ x, h (sliceVar (shift lam i j ε) x) ∂ν
        ≤ ∫ x, (h (sliceVar lam x) + ε * (h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2)) +
            L / 2 * ε ^ 2 * (x i ^ 2 - x j ^ 2) ^ 2) ∂ν := by
          refine integral_mono (integrable_h hν hh hsh) iABC fun x => ?_
          have hd := hh.desc (sliceVar lam x) (sliceVar (shift lam i j ε) x)
            (sliceVar_nonneg hlam x) (sliceVar_nonneg hsh x)
          rw [sliceVar_shift] at hd ⊢
          calc h (sliceVar lam x + ε * (x i ^ 2 - x j ^ 2)) ≤ _ := hd
            _ = _ := by ring
      _ = ∫ x, h (sliceVar lam x) ∂ν +
            ε * ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν +
            L / 2 * ε ^ 2 * ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν := by
          rw [integral_add iAB iC, integral_add iA iB, integral_const_mul, integral_const_mul]
  have hμS := mul_le_mul_of_nonneg_left hS hμ
  have key : 0 ≤ ε * ((c i - c j) + μ * ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν +
      μ * (L / 2) * ε * ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hε).mp key
  linarith

/-- **Spectral gap.** At a minimizer, if direction `j` is active and `cᵢ < cⱼ`, then
`cⱼ - cᵢ ≤ 2 L μ (λᵢ - λⱼ) / (K(K+2))`. -/
theorem gap (hν : SphereLike K ν) {h h' : ℝ → ℝ} {L : ℝ} (hh : SliceFn h h' L)
    {c : Fin K → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) {lam : Fin K → ℝ} (hmin : IsMinimizer ν h c μ lam)
    {i j : Fin K} (hc : c i < c j) (hj : 0 < lam j) :
    c j - c i ≤ 2 * L * μ * (lam i - lam j) / (K * (K + 2)) := by
  have hij : i ≠ j := fun e => by subst e; exact lt_irrefl _ hc
  have hord := ordering hν hh.meas hmin hc
  set E1 := ∫ x, h' (sliceVar lam x) * (x i ^ 2 - x j ^ 2) ∂ν
  set E2 := ∫ x, (x i ^ 2 - x j ^ 2) ^ 2 ∂ν
  have hE2 : 0 ≤ E2 := integral_nonneg fun x => sq_nonneg _
  have hC : 0 ≤ μ * (L / 2) * E2 := mul_nonneg (mul_nonneg hμ (by linarith [hh.L_nonneg])) hE2
  have hfirst : c j - c i ≤ μ * E1 := by
    refine le_of_forall_sub_le fun η hη => ?_
    set ε := min (lam j) (η / (μ * (L / 2) * E2 + 1)) with hεdef
    have hεpos : 0 < ε := lt_min hj (div_pos hη (by linarith))
    have hb := gap_eps hν hh hμ hmin hij hεpos (min_le_left _ _)
    have hε2 : μ * (L / 2) * ε * E2 ≤ η := by
      have h1 : ε ≤ η / (μ * (L / 2) * E2 + 1) := min_le_right _ _
      have h2 : μ * (L / 2) * E2 * ε ≤ μ * (L / 2) * E2 * (η / (μ * (L / 2) * E2 + 1)) :=
        mul_le_mul_of_nonneg_left h1 hC
      have h3 : μ * (L / 2) * E2 * (η / (μ * (L / 2) * E2 + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
      nlinarith
    linarith
  have hsec := first_order_le hν hh hmin.1 hij hord
  rw [integral_diff_sq_sq hν hij] at hsec
  have := mul_le_mul_of_nonneg_left hsec hμ
  calc c j - c i ≤ μ * E1 := hfirst
    _ ≤ μ * (L / 2 * (lam i - lam j) * (4 / (K * (K + 2)))) := this
    _ = 2 * L * μ * (lam i - lam j) / (K * (K + 2)) := by ring

end SigregDim
