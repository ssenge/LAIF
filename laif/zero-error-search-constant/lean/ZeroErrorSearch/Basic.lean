import Mathlib

/-!
# Zero-error search: the one-round angle bound and the halting inequalities

Search for one marked item among `N` with zero error. After a random relabelling, the part of the state that has not
halted is a family of vectors `ψ y`, one per marked item `y`, all of squared norm `a`. With `μ` the mean of the family,
`ω = arccos (‖μ‖ / √a)`.

* `angle_step`: one round of at most `m` parallel oracle calls maps `ψ y` to `ψ y - 2 P y (ψ y)`, with `P y`
  self-adjoint idempotent and `∑ y, ‖P y v‖ ^ 2 ≤ m ‖v‖ ^ 2`; the new angle is at most `ω + 2 arcsin √(m / N)`.
* `halting_left`, `halting_right`: the scalar inequalities which show that the potential `a h(ω)` never drops when
  part of the state halts.
-/

open Finset Real
open scoped InnerProductSpace

namespace ZeroErrorSearch

/-! ## Scalar inequalities -/

lemma tangent_ineq {x : ℝ} (h1 : -(π / 4) < x) (h2 : x < π / 4) : (1 - x) * sin x ≤ x * cos x := by
  have hpi : π ≤ 4 := pi_le_four
  rcases le_or_gt 0 x with hx | hx
  · have hs : sin x ≤ x := sin_le hx
    have hc : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
    have hx1 : x < 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 1 - x),
      mul_le_mul_of_nonneg_left hc hx, sq_nonneg x]
  · set y := -x with hy
    have hy0 : 0 < y := by linarith
    have hyl : y < π / 2 := by linarith
    have hcy : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hyl⟩
    have hsy : 0 ≤ sin y := sin_nonneg_of_nonneg_of_le_pi hy0.le (by linarith)
    have ht : y ≤ tan y := le_tan hy0.le hyl
    rw [tan_eq_sin_div_cos, le_div_iff₀ hcy] at ht
    have hsx : sin x = - sin y := by rw [hy, sin_neg, neg_neg]
    have hcx : cos x = cos y := by rw [hy, cos_neg]
    rw [hsx, hcx]
    nlinarith

/-- Tangent line of `cot` at `π/4`, in multiplied form: `sin 2ω (1/2 + π/4 - ω) ≤ cos² ω` on `(0, π/2)`. -/
lemma cot_tangent {ω : ℝ} (h0 : 0 < ω) (h1 : ω < π / 2) :
    sin (2 * ω) * (1 / 2 + π / 4 - ω) ≤ cos ω ^ 2 := by
  set x := ω - π / 4 with hx
  have hω : ω = π / 4 + x := by rw [hx]; ring
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hT := tangent_ineq (x := x) (by linarith) (by linarith)
  have hs2 : (0 : ℝ) < √2 := by positivity
  have key : cos ω - sin ω * (1 - 2 * x) = √2 * (x * cos x - (1 - x) * sin x) := by
    rw [hω, sin_add, cos_add, cos_pi_div_four, sin_pi_div_four]; ring
  have : sin (2 * ω) * (1 / 2 + π / 4 - ω) = cos ω * (sin ω * (1 - 2 * x)) := by
    rw [sin_two_mul, hx]; ring
  rw [this]
  nlinarith [mul_nonneg hc.le (mul_nonneg hs2.le (sub_nonneg.mpr hT))]

/-- On `[θ, π - θ]` with `θ ∈ [0, π/2]`, `sin z ≥ sin θ`. -/
lemma sin_ge_of_mem {θ z : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ π / 2) (h1 : θ ≤ z) (h2 : z ≤ π - θ) : sin θ ≤ sin z := by
  rcases le_or_gt z (π / 2) with hz | hz
  · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) hz h1
  · rw [← sin_pi_sub z]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

section Halting
variable (N : ℕ)

/-- The angle `θ` with `sin θ = 1/√N`. -/
noncomputable def theta : ℝ := arcsin (1 / √N)

lemma theta_facts (hN : 2 ≤ N) :
    0 < theta N ∧ theta N ≤ π / 4 ∧ sin (theta N) = 1 / √N ∧ (1 / √N) ^ 2 = 1 / N ∧ 1 / √N ≤ theta N ∧
      cos (theta N) = √(1 - 1 / N) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (1 / √(N : ℝ)) ^ 2 = 1 / N := by rw [div_pow, sq_sqrt (by linarith)]; ring
  have hx0 : 0 < 1 / √(N : ℝ) := by positivity
  have h4 : (2 : ℝ) ≤ √2 * √(N : ℝ) := by
    have h : √(4 : ℝ) ≤ √(2 * (N : ℝ)) := sqrt_le_sqrt (by linarith)
    rw [sqrt_mul (by norm_num)] at h
    have : √(4 : ℝ) = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    linarith
  have hx1 : 1 / √(N : ℝ) ≤ √2 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx1' : 1 / √(N : ℝ) ≤ 1 := hx1.trans (by linarith [sqrt_two_lt_three_halves])
  have hsin : sin (theta N) = 1 / √N := sin_arcsin (by linarith) hx1'
  refine ⟨arcsin_pos.mpr hx0, ?_, hsin, hsq, ?_, ?_⟩
  · calc theta N = arcsin (1 / √(N : ℝ)) := rfl
      _ ≤ arcsin (sin (π / 4)) := arcsin_le_arcsin (by rw [sin_pi_div_four]; exact hx1)
      _ = π / 4 := arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])
  · have := sin_le (arcsin_pos.mpr hx0).le
    unfold theta at hsin ⊢; rw [hsin] at this; exact this
  · unfold theta; rw [cos_arcsin, hsq]

/-- Halting inequality on `(0, π/2 - θ/2]`: `(c - ω) sin 2ω ≤ cos² ω - 1/N`, `c = π/4 + 1/2 - θ`. -/
theorem halting_left (hN : 2 ≤ N) {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ π / 2 - theta N / 2) :
    (π / 4 + 1 / 2 - theta N - ω) * sin (2 * ω) ≤ cos ω ^ 2 - 1 / N := by
  obtain ⟨hθ0, hθ4, hsθ, hsq, hxθ, hcθ⟩ := theta_facts N hN
  set θ := theta N
  set x := 1 / √(N : ℝ) with hxdef
  have hpi3 : 3 < π := pi_gt_three
  have hpi4 : π < 3.15 := pi_lt_d2
  have hω2 : ω < π / 2 := by linarith
  rcases le_or_gt x (sin (2 * ω)) with hA | hB
  · have hT := cot_tangent h0 hω2
    have hx0 : 0 ≤ x := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hA hθ0.le, mul_le_mul_of_nonneg_right hxθ hx0]
  · -- then 2ω < θ
    have h2ω : 2 * ω < θ := by
      by_contra hc; push_neg at hc
      have := sin_ge_of_mem hθ0.le (by linarith) hc (by linarith)
      linarith
    have hs0 : 0 ≤ sin (2 * ω) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcos : cos θ ≤ cos (2 * ω) := cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h2ω.le
    have hcsq : cos ω ^ 2 = 1 / 2 + cos (2 * ω) / 2 := cos_sq ω
    rcases eq_or_lt_of_le hN with h2 | h3
    · -- N = 2: θ = π/4, c = 1/2
      subst h2
      have hθ : θ = π / 4 := by
        have hx : x = sin (π / 4) := by
          rw [sin_pi_div_four, hxdef]; push_cast
          rw [div_eq_div_iff (by positivity) (by norm_num)]
          nlinarith [mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        show arcsin x = π / 4
        rw [hx, arcsin_sin (by linarith) (by linarith)]
      have hsc : sin (2 * ω) ≤ cos (2 * ω) := by
        have hsub : cos (2 * ω) - sin (2 * ω) = √2 * cos (2 * ω + π / 4) := by
          rw [cos_add, cos_pi_div_four, sin_pi_div_four]
          nlinarith [mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        have : 0 ≤ cos (2 * ω + π / 4) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
        nlinarith [sqrt_nonneg 2]
      rw [hθ]; push_cast
      nlinarith
    · have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
      have hx2 : x ^ 2 ≤ 1 / 3 := by
        rw [hsq]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hx0 : 0 < x := by positivity
      have hxl : x ≤ 0.58 := by nlinarith
      have hsq1 : (0.8 : ℝ) ≤ √(1 - 1 / N) := by
        rw [← hsq]; apply le_sqrt_of_sq_le; nlinarith
      have hc_nonneg : 0 ≤ π / 4 + 1 / 2 - θ - ω := by linarith
      have hprod : (π / 4 + 1 / 2 - θ - ω) * sin (2 * ω) ≤ (π / 4 + 1 / 2 - x) * x := by
        have := mul_le_mul (by linarith : π / 4 + 1 / 2 - θ - ω ≤ π / 4 + 1 / 2 - x) hB.le hs0 (by linarith)
        linarith
      rw [hcθ] at hcos
      rw [← hsq]
      nlinarith

/-- Halting inequality on `[π/2 - θ/2, π/2]`, for the increasing branch of the potential. -/
theorem halting_right (hN : 2 ≤ N) {ω : ℝ} (h0 : π / 2 - theta N / 2 ≤ ω) (h1 : ω ≤ π / 2) :
    (π / 4 + 1 / 2 - theta N - 2 * (π / 2 - theta N / 2) + ω) * sin (2 * ω) + (cos ω ^ 2 - 1 / N) ≤ 0 := by
  obtain ⟨hθ0, hθ4, hsθ, hsq, hxθ, hcθ⟩ := theta_facts N hN
  set θ := theta N
  have hpi3 : 3 < π := pi_gt_three
  have hs0 : 0 ≤ sin (2 * ω) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hneg : π / 4 + 1 / 2 - θ - 2 * (π / 2 - θ / 2) + ω ≤ 0 := by linarith
  have hc0 : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩
  have hcle : cos ω ≤ sin (θ / 2) := by
    rw [← cos_pi_div_two_sub]; exact cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h0
  have hhalf : sin (θ / 2) ^ 2 = 1 / 2 - cos θ / 2 := by
    have := cos_sq (θ / 2); have h2 : 2 * (θ / 2) = θ := by ring
    rw [h2] at this; nlinarith [sin_sq_add_cos_sq (θ / 2)]
  have hroot : 1 - 1 / (N : ℝ) ≤ √(1 - 1 / N) := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h01 : 0 ≤ 1 - 1 / (N : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hN0 : 0 ≤ 1 / (N : ℝ) := by positivity
    have h11 : 1 - 1 / (N : ℝ) ≤ 1 := by linarith
    exact le_sqrt_of_sq_le (by nlinarith)
  have hNpos : 0 ≤ 1 / (N : ℝ) := by positivity
  rw [hcθ] at hhalf
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg hs0, mul_le_mul hcle hcle hc0 (by linarith [hc0, hcle])]

end Halting

/-! ## The one-round angle bound -/

section Round
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

/-- A self-adjoint idempotent map: `⟪P v, v⟫ = ‖P v‖²`. -/
lemma proj_inner_self (P : E →ₗ[ℝ] E) (hsa : ∀ v w, ⟪P v, w⟫_ℝ = ⟪v, P w⟫_ℝ) (hid : ∀ v, P (P v) = P v) (v : E) :
    ⟪P v, v⟫_ℝ = ‖P v‖ ^ 2 := by
  rw [← hid v, hsa, hid v, real_inner_self_eq_norm_sq]

/-- Sum identity for one round, with the mean-zero shift by `c μ`. -/
lemma round_sum (μ : E) (δ : ι → E) (P : ι → E →ₗ[ℝ] E) (hsa : ∀ y v w, ⟪P y v, w⟫_ℝ = ⟪v, P y w⟫_ℝ)
    (hid : ∀ y v, P y (P y v) = P y v) (hδ : ∑ y, δ y = 0) (c : ℝ) :
    ∑ y, ⟪μ, (μ + δ y) - (2 : ℝ) • P y (μ + δ y)⟫_ℝ =
      (Fintype.card ι : ℝ) * ‖μ‖ ^ 2 - 2 * ∑ y, ‖P y μ‖ ^ 2 - 2 * ∑ y, ⟪P y μ - c • μ, δ y⟫_ℝ := by
  have h1 : ∀ y, ⟪μ, (μ + δ y) - (2 : ℝ) • P y (μ + δ y)⟫_ℝ =
      ‖μ‖ ^ 2 + ⟪μ, δ y⟫_ℝ - 2 * ‖P y μ‖ ^ 2 - 2 * ⟪P y μ - c • μ, δ y⟫_ℝ - 2 * c * ⟪μ, δ y⟫_ℝ := by
    intro y
    rw [map_add, inner_sub_right, inner_add_right, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
      inner_sub_left, inner_smul_left, ← hsa y μ μ, proj_inner_self _ (hsa y) (hid y), ← hsa y μ (δ y)]
    simp only [conj_trivial]; ring
  simp_rw [h1]
  have h0 : ∑ y, ⟪μ, δ y⟫_ℝ = 0 := by rw [← inner_sum, hδ, inner_zero_right]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, ← mul_sum, h0, nsmul_eq_mul]
  ring

/-- Cauchy-Schwarz over a sum of inner products. -/
lemma sum_inner_le (u v : ι → E) : ∑ y, ⟪u y, v y⟫_ℝ ≤ √(∑ y, ‖u y‖ ^ 2) * √(∑ y, ‖v y‖ ^ 2) :=
  (sum_le_sum fun y _ => real_inner_le_norm (u y) (v y)).trans (sum_mul_le_sqrt_mul_sqrt _ _ _)

lemma sum_norm_shift (μ : E) (P : ι → E →ₗ[ℝ] E) (hsa : ∀ y v w, ⟪P y v, w⟫_ℝ = ⟪v, P y w⟫_ℝ)
    (hid : ∀ y v, P y (P y v) = P y v) (c : ℝ) :
    ∑ y, ‖P y μ - c • μ‖ ^ 2 =
      (1 - 2 * c) * ∑ y, ‖P y μ‖ ^ 2 + c ^ 2 * ((Fintype.card ι : ℝ) * ‖μ‖ ^ 2) := by
  have : ∀ y, ‖P y μ - c • μ‖ ^ 2 = (1 - 2 * c) * ‖P y μ‖ ^ 2 + c ^ 2 * ‖μ‖ ^ 2 := by
    intro y
    rw [norm_sub_sq_real, inner_smul_right, proj_inner_self _ (hsa y) (hid y), norm_smul, mul_pow, norm_eq_abs, sq_abs]
    ring
  simp_rw [this]; rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]; ring

lemma sum_norm_mean (μ : E) (δ : ι → E) (hδ : ∑ y, δ y = 0) :
    ∑ y, ‖μ + δ y‖ ^ 2 = (Fintype.card ι : ℝ) * ‖μ‖ ^ 2 + ∑ y, ‖δ y‖ ^ 2 := by
  have h0 : ∑ y, ⟪μ, δ y⟫_ℝ = 0 := by rw [← inner_sum, hδ, inner_zero_right]
  simp_rw [norm_add_sq_real]
  rw [sum_add_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, h0]; ring

/-- **One round moves the angle to the mean by at most `2 θ_m`.** For a family `ψ y` with mean `μ`, squared norms of
average `a`, and a round `ψ y ↦ ψ y - 2 P y (ψ y)` with `P y` self-adjoint idempotent and `∑ y, ‖P y v‖² ≤ m ‖v‖²`,
`arccos (‖μ'‖/√a) ≤ arccos (‖μ‖/√a) + 2 arcsin √(m/N)`. -/
theorem angle_step [Nonempty ι] (ψ : ι → E) (P : ι → E →ₗ[ℝ] E) (hsa : ∀ y v w, ⟪P y v, w⟫_ℝ = ⟪v, P y w⟫_ℝ)
    (hid : ∀ y v, P y (P y v) = P y v) (m : ℝ) (hcap : ∀ v, ∑ y, ‖P y v‖ ^ 2 ≤ m * ‖v‖ ^ 2)
    (hmN : m ≤ Fintype.card ι) (ha : 0 < ∑ y, ‖ψ y‖ ^ 2) :
    let n : ℝ := Fintype.card ι
    let a := (∑ y, ‖ψ y‖ ^ 2) / n
    arccos (‖n⁻¹ • ∑ y, (ψ y - (2 : ℝ) • P y (ψ y))‖ / √a) ≤
      arccos (‖n⁻¹ • ∑ y, ψ y‖ / √a) + 2 * arcsin √(m / n) := by
  intro n a
  have hn : 0 < n := by simp only [n]; exact_mod_cast Fintype.card_pos
  set μ := n⁻¹ • ∑ y, ψ y with hμ
  set δ : ι → E := fun y => ψ y - μ with hδdef
  have hψ : ∀ y, ψ y = μ + δ y := fun y => by simp [δ]
  have hδ : ∑ y, δ y = 0 := by
    simp only [δ, sum_sub_distrib, sum_const, card_univ, hμ, smul_smul]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn.ne', one_smul, sub_self]
  set β := ‖μ‖
  set s := ∑ y, ‖δ y‖ ^ 2
  have ha' : 0 < a := div_pos ha hn
  have hsum : ∑ y, ‖ψ y‖ ^ 2 = n * β ^ 2 + s := by
    simp_rw [hψ]; exact sum_norm_mean μ δ hδ
  have hs0 : 0 ≤ s := sum_nonneg fun _ _ => by positivity
  have haβ : a = β ^ 2 + s / n := by simp only [a]; rw [hsum]; field_simp
  set ω := arccos (β / √a)
  set θm := arcsin √(m / n)
  have hsqa : 0 < √a := sqrt_pos.mpr ha'
  have hθm0 : 0 ≤ θm := by
    rcases le_or_gt 0 m with hm | hm
    · exact arcsin_nonneg.mpr (sqrt_nonneg _)
    · -- m < 0 contradicts hcap at a nonzero vector unless all P vanish; handle via sqrt of negative = 0
      have : m / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hm.le hn.le
      simp only [θm, sqrt_eq_zero'.mpr this, arcsin_zero, le_refl]
  have hlhs_le : arccos (‖n⁻¹ • ∑ y, (ψ y - (2 : ℝ) • P y (ψ y))‖ / √a) ≤ π / 2 :=
    arccos_le_pi_div_two.mpr (div_nonneg (norm_nonneg _) hsqa.le)
  by_cases hbig : π / 2 ≤ ω + 2 * θm
  · exact hlhs_le.trans hbig
  push_neg at hbig
  have hω0 : 0 ≤ ω := arccos_nonneg _
  -- β > 0, otherwise ω = π/2
  have hβ : 0 < β := by
    rcases eq_or_lt_of_le (norm_nonneg μ) with h | h
    · exfalso; have : ω = π / 2 := by simp only [ω, β, ← h, zero_div, arccos_zero]
      linarith
    · exact h
  have hβa : β ≤ √a := by
    rw [le_sqrt hβ.le ha'.le, haβ]; have : 0 ≤ s / n := div_nonneg hs0 hn.le
    linarith
  have hcosω : cos ω = β / √a := cos_arccos (by linarith [div_nonneg hβ.le hsqa.le]) ((div_le_one hsqa).mpr hβa)
  have hsinω : √a * sin ω = √(s / n) := by
    simp only [ω, sin_arccos]
    rw [← sqrt_mul ha'.le, div_pow, sq_sqrt ha'.le, mul_sub, mul_one, mul_div_cancel₀ _ ha'.ne', haβ]; ring_nf
  -- p and its angle
  set q := ∑ y, ‖P y μ‖ ^ 2
  have hq0 : 0 ≤ q := sum_nonneg fun _ _ => by positivity
  have hqm : q ≤ m * β ^ 2 := hcap μ
  set p := q / (n * β ^ 2)
  have hnb : 0 < n * β ^ 2 := by positivity
  have hp0 : 0 ≤ p := div_nonneg hq0 hnb.le
  have hpm : p ≤ m / n := by
    rw [div_le_div_iff₀ hnb hn]; nlinarith
  have hp1 : p ≤ 1 := hpm.trans ((div_le_one hn).mpr hmN)
  set tp := arcsin √p
  have htp : tp ≤ θm := arcsin_le_arcsin (sqrt_le_sqrt hpm)
  have htp0 : 0 ≤ tp := arcsin_nonneg.mpr (sqrt_nonneg _)
  have hstp : sin tp = √p := sin_arcsin (by linarith [sqrt_nonneg p]) (by rw [sqrt_le_one]; exact hp1)
  have hctp : cos tp = √(1 - p) := by simp only [tp, cos_arcsin, sq_sqrt hp0]
  -- inner product bound
  set ψ' : ι → E := fun y => ψ y - (2 : ℝ) • P y (ψ y)
  set μ' := n⁻¹ • ∑ y, ψ' y
  have hrs := round_sum μ δ P hsa hid hδ p
  have hcs := sum_inner_le (fun y => P y μ - p • μ) δ
  have hshift := sum_norm_shift μ P hsa hid p
  have hshift' : ∑ y, ‖P y μ - p • μ‖ ^ 2 = n * β ^ 2 * (p * (1 - p)) := by
    rw [hshift]; simp only [p]; field_simp; ring
  have hinner : ⟪μ, ∑ y, ψ' y⟫_ℝ ≥ n * β ^ 2 - 2 * q - 2 * (β * √n * √(p * (1 - p)) * √s) := by
    rw [inner_sum]
    have : ∑ y, ⟪μ, ψ' y⟫_ℝ = ∑ y, ⟪μ, (μ + δ y) - (2 : ℝ) • P y (μ + δ y)⟫_ℝ := by
      apply sum_congr rfl; intro y _; simp only [ψ', ← hψ]
    rw [this, hrs]
    have hsq' : √(∑ y, ‖P y μ - p • μ‖ ^ 2) = β * √n * √(p * (1 - p)) := by
      rw [hshift', sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_sq hβ.le]; ring
    rw [hsq'] at hcs
    linarith
  have hnorm : β * ‖μ'‖ ≥ ⟪μ, μ'⟫_ℝ := by
    rw [ge_iff_le]; exact real_inner_le_norm _ _
  have hmu' : ⟪μ, μ'⟫_ℝ = n⁻¹ * ⟪μ, ∑ y, ψ' y⟫_ℝ := by simp only [μ', inner_smul_right]
  -- target: ‖μ'‖ ≥ √a cos(ω + 2 tp)
  have hq : q = p * (n * β ^ 2) := by simp only [p]; field_simp
  have htrig : √a * cos (ω + 2 * tp) = β * (1 - 2 * p) - 2 * √(s / n) * (√p * √(1 - p)) := by
    rw [cos_add, cos_two_mul, sin_two_mul, hstp, hctp, sq_sqrt (show (0 : ℝ) ≤ 1 - p by linarith)]
    have : √a * cos ω = β := by rw [hcosω]; field_simp
    have h2 := hsinω
    linear_combination (1 - 2 * p) * this - 2 * (√p * √(1 - p)) * h2
  have hsn : √(s / n) = √s / √n := sqrt_div' s hn.le
  have hsqn : 0 < √n := sqrt_pos.mpr hn
  have hpp : √(p * (1 - p)) = √p * √(1 - p) := sqrt_mul hp0 _
  have hmain : √a * cos (ω + 2 * tp) ≤ ‖μ'‖ := by
    rw [htrig]
    have h1 : β * ‖μ'‖ ≥ n⁻¹ * (n * β ^ 2 - 2 * q - 2 * (β * √n * √(p * (1 - p)) * √s)) := by
      rw [hmu'] at hnorm
      have := mul_le_mul_of_nonneg_left hinner.le (inv_nonneg.mpr hn.le)
      linarith
    have h2 : n⁻¹ * (n * β ^ 2 - 2 * q - 2 * (β * √n * √(p * (1 - p)) * √s)) =
        β * (β * (1 - 2 * p) - 2 * √(s / n) * (√p * √(1 - p))) := by
      have key : ∀ r : ℝ, 0 < r → (r * r)⁻¹ * (r * r * β ^ 2 - 2 * (p * (r * r * β ^ 2)) -
          2 * (β * r * (√p * √(1 - p)) * √s)) = β * (β * (1 - 2 * p) - 2 * (√s / r) * (√p * √(1 - p))) := by
        intro r hr; field_simp
      have := key (√n) hsqn
      rw [mul_self_sqrt hn.le] at this
      rw [hq, hsn, hpp]; linarith [this]
    rw [h2] at h1
    exact le_of_mul_le_mul_left (by linarith) hβ
  have hmono : cos (ω + 2 * θm) ≤ cos (ω + 2 * tp) :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hge : cos (ω + 2 * θm) ≤ ‖μ'‖ / √a := by
    rw [le_div_iff₀ hsqa]; nlinarith
  calc arccos (‖μ'‖ / √a) ≤ arccos (cos (ω + 2 * θm)) := arccos_le_arccos hge
    _ = ω + 2 * θm := arccos_cos (by linarith) (by linarith)

/-- The round is an involution and preserves norms. -/
lemma round_invol (P : E →ₗ[ℝ] E) (hid : ∀ v, P (P v) = P v) (v : E) :
    (v - (2 : ℝ) • P v) - (2 : ℝ) • P (v - (2 : ℝ) • P v) = v := by
  rw [map_sub, map_smul, hid]; module

lemma round_norm (P : E →ₗ[ℝ] E) (hsa : ∀ v w, ⟪P v, w⟫_ℝ = ⟪v, P w⟫_ℝ) (hid : ∀ v, P (P v) = P v) (v : E) :
    ‖v - (2 : ℝ) • P v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, real_inner_comm, proj_inner_self P hsa hid]
  simp; ring

/-- **Lemma 3, both directions**: one round changes `ω` by at most `2 arcsin √(m/N)`. -/
theorem angle_step_abs [Nonempty ι] (ψ : ι → E) (P : ι → E →ₗ[ℝ] E) (hsa : ∀ y v w, ⟪P y v, w⟫_ℝ = ⟪v, P y w⟫_ℝ)
    (hid : ∀ y v, P y (P y v) = P y v) (m : ℝ) (hcap : ∀ v, ∑ y, ‖P y v‖ ^ 2 ≤ m * ‖v‖ ^ 2)
    (hmN : m ≤ Fintype.card ι) (ha : 0 < ∑ y, ‖ψ y‖ ^ 2) :
    let n : ℝ := Fintype.card ι
    let a := (∑ y, ‖ψ y‖ ^ 2) / n
    |arccos (‖n⁻¹ • ∑ y, (ψ y - (2 : ℝ) • P y (ψ y))‖ / √a) - arccos (‖n⁻¹ • ∑ y, ψ y‖ / √a)| ≤
      2 * arcsin √(m / n) := by
  intro n a
  have h1 := angle_step ψ P hsa hid m hcap hmN ha
  set ψ' : ι → E := fun y => ψ y - (2 : ℝ) • P y (ψ y)
  have hn' : ∑ y, ‖ψ' y‖ ^ 2 = ∑ y, ‖ψ y‖ ^ 2 := sum_congr rfl fun y _ => round_norm (P y) (hsa y) (hid y) (ψ y)
  have h2 := angle_step ψ' P hsa hid m hcap hmN (by rw [hn']; exact ha)
  simp only [hn'] at h2
  have hback : ∀ y, ψ' y - (2 : ℝ) • P y (ψ' y) = ψ y := fun y => round_invol (P y) (hid y) (ψ y)
  simp only [hback] at h2
  rw [abs_le]; constructor <;> linarith [h1, h2]

end Round

/-! ## Non-vacuity: the angle bound is attained

For `N = 4`, one-dimensional states `ψ y = 1` and `P y` the identity for `y = 0` and zero otherwise (so `m = 1`),
the mean moves from `1` to `1/2`: the angle goes from `0` to `π/3 = 2 arcsin (1/2)`. -/

noncomputable def tightP (y : Fin 4) : ℝ →ₗ[ℝ] ℝ := if y = 0 then LinearMap.id else 0

example : arccos (‖(4 : ℝ)⁻¹ • ∑ y : Fin 4, ((1 : ℝ) - (2 : ℝ) • tightP y 1)‖ / √1) -
    arccos (‖(4 : ℝ)⁻¹ • ∑ _y : Fin 4, (1 : ℝ)‖ / √1) = 2 * arcsin √(1 / 4) := by
  have h1 : (4 : ℝ)⁻¹ • ∑ y : Fin 4, ((1 : ℝ) - (2 : ℝ) • tightP y 1) = 1 / 2 := by
    simp [Fin.sum_univ_four, tightP]; norm_num
  have h2 : (4 : ℝ)⁻¹ • ∑ _y : Fin 4, (1 : ℝ) = 1 := by simp
  have hs : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]
  rw [h1, h2, hs, sqrt_one, div_one, div_one, norm_one, arccos_one, sub_zero,
    show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
  have ha : arccos (1 / 2) = π / 3 := by rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]
  have hb : arcsin (1 / 2) = π / 6 := by
    rw [← sin_pi_div_six, arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]
  rw [ha, hb]; ring

lemma tightP_hyp : (∀ y v w, ⟪tightP y v, w⟫_ℝ = ⟪v, tightP y w⟫_ℝ) ∧ (∀ y v, tightP y (tightP y v) = tightP y v) ∧
    (∀ v, ∑ y, ‖tightP y v‖ ^ 2 ≤ 1 * ‖v‖ ^ 2) := by
  refine ⟨fun y v w => ?_, fun y v => ?_, fun v => ?_⟩
  · by_cases h : y = 0 <;> simp [tightP, h, real_inner_comm]
  · by_cases h : y = 0 <;> simp [tightP, h]
  · simp [Fin.sum_univ_four, tightP]

end ZeroErrorSearch
